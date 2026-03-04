/-
# Main Theorem: Hamiltonian Cycle Decomposition

For all odd m ≥ 3, the digraph on (Z/mZ)³ with arcs that increment one
coordinate can be decomposed into three directed Hamiltonian cycles.
-/
import ClaudesCycles.Cycle0
import ClaudesCycles.Cycle1
import ClaudesCycles.Cycle2
import LeanTcb

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- All three cycles are Hamiltonian for odd m ≥ 3. -/
theorem all_cycles_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 0) ∧
    IsHamiltonian m (step m 1) ∧
    IsHamiltonian m (step m 2) :=
  ⟨cycle0_hamiltonian m hm hm3,
   cycle1_hamiltonian m hm hm3,
   cycle2_hamiltonian m hm hm3⟩

omit [NeZero m] in
/-- The three cycles partition all arcs: at each vertex, they bump
    distinct coordinates (since direction is a bijection Fin 3 → Fin 3). -/
theorem arcs_partitioned (v : Vertex m) :
    Function.Bijective (fun c : Fin 3 => direction m c v) :=
  direction_bijective m v

/-- Main theorem: for odd m ≥ 3, the digraph on (Z/mZ)³ with arcs that increment
    one coordinate can be decomposed into three directed Hamiltonian cycles.
    The construction (witness) is Claude's direction function, verified by the kernel. -/
@[tcb] theorem claudes_cycles_decomposition (hm : Odd m) (hm3 : 3 ≤ m) :
    ∃ (d : Fin 3 → Vertex m → Fin 3),
      (∀ v : Vertex m, Function.Bijective (fun c : Fin 3 => d c v)) ∧
      (∀ c : Fin 3, IsHamiltonian m (fun v => bump m v (d c v))) :=
  ⟨direction m, direction_bijective m, fun c => by
    fin_cases c
    · exact cycle0_hamiltonian m hm hm3
    · exact cycle1_hamiltonian m hm hm3
    · exact cycle2_hamiltonian m hm hm3⟩

end ClaudesCycles
