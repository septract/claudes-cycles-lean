/-
# Main Theorem: Hamiltonian Cycle Decomposition

For all odd m ≥ 3, the digraph on (Z/mZ)³ with arcs that increment one
coordinate can be decomposed into three directed Hamiltonian cycles.
-/
import ClaudeCycles.Cycle0
import ClaudeCycles.Cycle1
import ClaudeCycles.Cycle2
import LeanTcb

namespace ClaudeCycles

variable (m : ℕ) [NeZero m]

/-- All three cycles are Hamiltonian for odd m ≥ 3. -/
theorem all_cycles_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 0) ∧
    IsHamiltonian m (step m 1) ∧
    IsHamiltonian m (step m 2) :=
  ⟨cycle0_hamiltonian m hm hm3,
   cycle1_hamiltonian m hm hm3,
   cycle2_hamiltonian m hm hm3⟩

/-- The three cycles partition all arcs: at each vertex, they bump
    distinct coordinates (since direction is a bijection Fin 3 → Fin 3). -/
theorem arcs_partitioned (v : Vertex m) :
    Function.Bijective (fun c : Fin 3 => direction m c v) :=
  direction_bijective m v

/-- Main theorem: for odd m ≥ 3, Claude's construction gives three directed
    Hamiltonian cycles that partition all 3m³ arcs of the digraph on (Z/mZ)³. -/
@[tcb] theorem claude_cycles_decomposition (hm : Odd m) (hm3 : 3 ≤ m) :
    (∀ c : Fin 3, IsHamiltonian m (step m c)) ∧
    (∀ v : Vertex m, Function.Bijective (fun c : Fin 3 => direction m c v)) := by
  constructor
  · intro c
    fin_cases c
    · exact cycle0_hamiltonian m hm hm3
    · exact cycle1_hamiltonian m hm hm3
    · exact cycle2_hamiltonian m hm hm3
  · exact fun v => direction_bijective m v

end ClaudeCycles
