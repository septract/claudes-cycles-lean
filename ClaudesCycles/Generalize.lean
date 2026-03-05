/-
# General Claude-like Theorem

The paper's main characterization: a valid Claude-like table gives a Hamiltonian
decomposition for all odd m ≥ 3 if and only if it is generalizable (i.e., works at m = 3).
-/
import ClaudesCycles.ClaudeLike

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- The hard direction: if a valid table is generalizable (Hamiltonian at m = 3),
    then it is Hamiltonian at all odd m ≥ 3.

    Proof strategy (sorry'd): follow the same fiber-by-fiber argument as Cycle0/1/2.lean,
    abstracted over the table:
    1. The table determines which coordinate is "stable" vs "advancing" at each fiber.
    2. Track m-step return formulas using table entries for interior fibers (coarsened s = 1).
    3. Show the advancing coordinate moves by 2 at each fiber-0 return.
    4. Apply `ZMod.addOrderOf_two` and `orbit_add_two_surj` for the gcd(2,m)=1 argument.
    5. Stitch blocks together to get minimalPeriod = m³. -/
theorem claudeLike_generalize (T : ClaudeLikeTable)
    (hvalid : IsValidTable T)
    (hgen : IsGeneralizable T)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (c : Fin 3) :
    IsHamiltonian m (claudeLikeStep T c) := by
  sorry

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

/-- The easy direction: if a table gives a decomposition for all odd m ≥ 3,
    then it is generalizable (just instantiate at m = 3). -/
theorem claudeLike_specialize (T : ClaudeLikeTable)
    (h : ∀ (m : ℕ) [NeZero m], Odd m → 3 ≤ m →
         ∀ c, IsHamiltonian m (claudeLikeStep T c)) :
    IsGeneralizable T :=
  fun c => h 3 ⟨1, rfl⟩ (by omega) c

/-- Iff characterization: a valid table gives a decomposition for all odd m ≥ 3
    if and only if it is generalizable. -/
theorem claudeLike_iff (T : ClaudeLikeTable) (hvalid : IsValidTable T) :
    (∀ (m : ℕ) [NeZero m], Odd m → 3 ≤ m →
     ∀ c, IsHamiltonian m (claudeLikeStep T c)) ↔
    IsGeneralizable T :=
  ⟨claudeLike_specialize T,
   fun hgen m _ hm hm3 c => claudeLike_generalize m T hvalid hgen hm hm3 c⟩

end ClaudesCycles
