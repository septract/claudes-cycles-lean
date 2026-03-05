/-
# General Claude-like Theorem

The paper's main characterization: a valid Claude-like table gives a Hamiltonian
decomposition for all odd m ≥ 3 if and only if it is generalizable (i.e., each cycle
yields a Hamiltonian cycle for all odd m ≥ 3).
-/
import ClaudesCycles.ClaudeLike

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- If a valid table is generalizable, then each cycle is Hamiltonian at all odd m ≥ 3.
    This is immediate from the definition of `IsGeneralizable`, which already requires
    Hamiltonicity at all odd m ≥ 3 (matching the paper's definition of "generalizable"). -/
theorem claudeLike_generalize (T : ClaudeLikeTable)
    (hvalid : IsValidTable T)
    (hgen : IsGeneralizable T)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (c : Fin 3) :
    IsHamiltonian m (claudeLikeStep T c) :=
  hgen c m hm hm3

/-- Generalized decomposition: a valid, generalizable table gives a Hamiltonian cycle
    decomposition for all odd m ≥ 3. -/
theorem claudeLike_decomposition (T : ClaudeLikeTable)
    (hvalid : IsValidTable T) (hgen : IsGeneralizable T)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    ∃ (d : Fin 3 → Vertex m → Fin 3),
      (∀ v, Function.Bijective (fun c => d c v)) ∧
      (∀ c, IsHamiltonian m (fun v => bump m v (d c v))) :=
  ⟨fun c v => claudeLikeDir T c v,
   fun v => claudeLikeDir_bijective T hvalid v,
   fun c => claudeLike_generalize m T hvalid hgen hm hm3 c⟩

/-- Repackaging: reorder quantifiers (∀ m c → ∀ c m). -/
theorem claudeLike_specialize (T : ClaudeLikeTable)
    (h : ∀ (m : ℕ) [NeZero m], Odd m → 3 ≤ m →
         ∀ c, IsHamiltonian m (claudeLikeStep T c)) :
    IsGeneralizable T := by
  intro c m _ hm hm3; exact h m hm hm3 c

/-- Iff characterization: `IsGeneralizable` is equivalent to the ∀ m, ∀ c form. -/
theorem claudeLike_iff (T : ClaudeLikeTable) :
    (∀ (m : ℕ) [NeZero m], Odd m → 3 ≤ m →
     ∀ c, IsHamiltonian m (claudeLikeStep T c)) ↔
    IsGeneralizable T := by
  constructor
  · intro h c m _ hm hm3; exact h m hm hm3 c
  · intro hgen m _ hm hm3 c; exact hgen c m hm hm3

end ClaudesCycles
