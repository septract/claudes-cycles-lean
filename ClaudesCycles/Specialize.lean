/-
# Specialization: Claude's Table

Bridges the general Claude-like framework to the concrete direction function in Defs.lean.
Shows Claude's specific construction is a valid, generalizable Claude-like table.
-/
import ClaudesCycles.Generalize
import ClaudesCycles.Main

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- Claude's specific table, extracted from the direction function in Defs.lean.
    Maps (cycle, coarsened_s, coarsened_i, coarsened_j) → direction.

    Cycle 0: s̄=0 → (j̄=2 → 0, else 2); s̄=2 → (ī≠0 → 1, else 2); s̄=1 → (ī=2 → 2, else 1)
    Cycle 1: s̄=0 → 1; s̄=2 → (ī≠0 → 2, else 1); s̄=1 → 0
    Cycle 2: s̄=0 → (j̄≠2 → 0, else 2); s̄=2 → 0; s̄=1 → (ī≠2 → 2, else 1) -/
def claudesTable : ClaudeLikeTable := fun c s_bar i_bar j_bar =>
  match c with
  | 0 =>
    if s_bar = 0 then (if j_bar = 2 then 0 else 2)
    else if s_bar = 2 then (if i_bar ≠ 0 then 1 else 2)
    else (if i_bar = 2 then 2 else 1)
  | 1 =>
    if s_bar = 0 then 1
    else if s_bar = 2 then (if i_bar ≠ 0 then 2 else 1)
    else 0
  | 2 =>
    if s_bar = 0 then (if j_bar ≠ 2 then 0 else 2)
    else if s_bar = 2 then 0
    else (if i_bar ≠ 2 then 2 else 1)

/-- Claude's table is valid: at each coarsened triple, the three cycles bump
    distinct coordinates. -/
theorem claudesTable_valid : IsValidTable claudesTable := by
  intro s_bar i_bar j_bar
  apply (Finite.injective_iff_bijective).mp
  intro a b h
  fin_cases s_bar <;> fin_cases i_bar <;> fin_cases j_bar <;>
    fin_cases a <;> fin_cases b <;> simp_all [claudesTable]

set_option maxHeartbeats 3200000 in
-- 3 cycles × 3 fiber regions × direction/coarsen splits = large case analysis
omit [NeZero m] in
/-- The concrete direction function equals the Claude-like direction induced
    by Claude's table, for m ≥ 2. -/
theorem direction_eq_claudeLikeDir (hm : 2 ≤ m) (c : Fin 3) (v : Vertex m) :
    direction m c v = claudeLikeDir claudesTable c v := by
  unfold direction claudeLikeDir claudesTable coarsen fiber
  have h10 : (1 : ZMod m) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_lt m 1 (by omega) (by omega)
  fin_cases c <;> split_ifs <;> simp_all

omit [NeZero m] in
/-- The concrete step function equals the Claude-like step. -/
theorem step_eq_claudeLikeStep (hm : 2 ≤ m) (c : Fin 3) (v : Vertex m) :
    step m c v = claudeLikeStep claudesTable c v := by
  simp [step, claudeLikeStep, direction_eq_claudeLikeDir m hm]

/-- Claude's table is generalizable: each cycle is Hamiltonian for all odd m ≥ 3.
    Derived from the concrete Hamiltonicity proofs in Cycle0/1/2.lean. -/
theorem claudesTable_generalizable : IsGeneralizable claudesTable := by
  intro c m _ hm hm3
  suffices h : claudeLikeStep claudesTable c = step m c by
    rw [h]
    fin_cases c
    · exact cycle0_hamiltonian m hm hm3
    · exact cycle1_hamiltonian m hm hm3
    · exact cycle2_hamiltonian m hm hm3
  funext v
  exact (step_eq_claudeLikeStep m (by omega) c v).symm

/-- The existing main theorem factors through the general framework. -/
theorem claudes_cycles_via_generalize (hm : Odd m) (hm3 : 3 ≤ m) :
    ∃ (d : Fin 3 → Vertex m → Fin 3),
      (∀ v, Function.Bijective (fun c => d c v)) ∧
      (∀ c, IsHamiltonian m (fun v => bump m v (d c v))) := by
  exact claudeLike_decomposition m claudesTable claudesTable_valid
    claudesTable_generalizable hm hm3

end ClaudesCycles
