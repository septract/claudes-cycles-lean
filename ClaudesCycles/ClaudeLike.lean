/-
# Claude-like Decompositions

General framework for Claude-like direction tables: a direction function on (Z/mZ)³
determined by the coarsened fiber index s, first coordinate i, and second coordinate j.
The paper's Theorem characterizes all 760 valid decompositions.
-/
import ClaudesCycles.Orbit

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- Coarsen a ZMod m value into Fin 3: 0 ↦ 0, -1 (= m-1) ↦ 2, everything else ↦ 1. -/
def coarsen (x : ZMod m) : Fin 3 :=
  if x = 0 then 0 else if x = -1 then 2 else 1

/-- A Claude-like table maps (cycle, coarsened_s, coarsened_i, coarsened_j) to a direction. -/
abbrev ClaudeLikeTable := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3

variable {m}

/-- Direction function induced by a Claude-like table. -/
def claudeLikeDir (T : ClaudeLikeTable) (c : Fin 3) (v : Vertex m) : Fin 3 :=
  T c (coarsen m (fiber m v)) (coarsen m v.1) (coarsen m v.2.1)

/-- Step function induced by a Claude-like table. -/
def claudeLikeStep (T : ClaudeLikeTable) (c : Fin 3) (v : Vertex m) : Vertex m :=
  bump m v (claudeLikeDir T c v)

/-- A table is valid if at each coarsened triple, c ↦ T(c, s̄, ī, j̄) is a bijection. -/
def IsValidTable (T : ClaudeLikeTable) : Prop :=
  ∀ s_bar i_bar j_bar : Fin 3,
    Function.Bijective (fun c => T c s_bar i_bar j_bar)

/-- A table is generalizable if each cycle is Hamiltonian for all odd m ≥ 3.
    This matches the paper's definition: a cycle "generalizes" when the lifting
    procedure yields a Hamiltonian cycle for every odd m. -/
def IsGeneralizable (T : ClaudeLikeTable) : Prop :=
  ∀ (c : Fin 3) (m : ℕ) [NeZero m], Odd m → 3 ≤ m → IsHamiltonian m (claudeLikeStep T c)

/-! ## Basic lemmas about coarsen -/

omit [NeZero m] in
@[simp]
theorem coarsen_zero : coarsen m (0 : ZMod m) = 0 := by
  simp [coarsen]

omit [NeZero m] in
theorem coarsen_neg_one (hm : 2 ≤ m) : coarsen m (-1 : ZMod m) = 2 := by
  simp [coarsen, neg_one_ne_zero m hm]

omit [NeZero m] in
theorem coarsen_mid {x : ZMod m} (h0 : x ≠ 0) (hm1 : x ≠ -1) : coarsen m x = 1 := by
  simp [coarsen, h0, hm1]

/-! ## Iff characterizations for rewriting -/

omit [NeZero m] in
theorem coarsen_eq_zero_iff (x : ZMod m) : coarsen m x = 0 ↔ x = 0 := by
  unfold coarsen; constructor
  · intro h; split_ifs at h <;> first | assumption | exact absurd h (by decide)
  · intro h; simp [h]

omit [NeZero m] in
theorem coarsen_eq_two_iff (hm : 2 ≤ m) (x : ZMod m) : coarsen m x = 2 ↔ x = -1 := by
  unfold coarsen; constructor
  · intro h; split_ifs at h <;> first | assumption | exact absurd h (by decide)
  · intro h; simp [h, neg_one_ne_zero m hm]

/-! ## Structural lemmas -/

omit [NeZero m] in
/-- Stepping with a Claude-like table advances the fiber by 1. -/
@[simp]
theorem fiber_claudeLikeStep (T : ClaudeLikeTable) (c : Fin 3) (v : Vertex m) :
    fiber m (claudeLikeStep T c v) = fiber m v + 1 := by
  simp [claudeLikeStep]

omit [NeZero m] in
/-- If the table is valid, the induced direction function is a bijection at each vertex. -/
theorem claudeLikeDir_bijective (T : ClaudeLikeTable) (hT : IsValidTable T)
    (v : Vertex m) :
    Function.Bijective (fun c => claudeLikeDir T c v) :=
  hT (coarsen m (fiber m v)) (coarsen m v.1) (coarsen m v.2.1)

end ClaudesCycles
