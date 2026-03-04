/-
# Hamiltonicity of Cycle 1

Cycle 1 rules:
  s = 0:       bump j (1)
  0 < s < m-1: bump i (0)
  s = m-1:     i ≠ 0  → bump k (2), else bump j (1)

Proof structure (Knuth's Appendix):
  The s=0 vertices are visited in order (0, k, -k), (-2, 1+k, 1-k),
  (-4, 2+k, 2-k), ... for k = 0, 1, ..., m-1. The "advance by 2" now
  occurs in the i-coordinate. Since gcd(2,m) = 1 for odd m, all values hit.
-/
import ClaudesCycles.Orbit

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-! ## Direction lemmas for cycle 1 -/

/-- At s = 0: cycle 1 always bumps j. -/
theorem direction_one_s0 (v : Vertex m)
    (hs : fiber m v = 0) :
    direction m 1 v = 1 := by
  simp only [direction, hs, ↓reduceIte]

/-- At 0 < s < m-1: cycle 1 always bumps i. -/
theorem direction_one_mid (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) :
    direction m 1 v = 0 := by
  simp only [direction, hs0, hsm, ↓reduceIte]

/-- At s = -1, i ≠ 0: cycle 1 bumps k. -/
theorem direction_one_sm_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 ≠ 0) :
    direction m 1 v = 2 := by
  simp only [direction]; split_ifs <;> simp_all

/-- At s = -1, i = 0: cycle 1 bumps j. -/
theorem direction_one_sm_i0 (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 = 0) :
    direction m 1 v = 1 := by
  simp only [direction]; split_ifs <;> simp_all

/-! ## Hamiltonicity of cycle 1

The key observation: at mid fibers (0 < s < m-1), cycle 1 always bumps i.
So i advances by 1 per step except at s=0 (bump j) and s=-1 (bump k or j).

After m steps from an s=0 vertex, we return to s=0 with i advanced by m-2
(mid steps) or m-1 depending on the i=0 exception at s=-1.

More precisely (Knuth): the s=0 vertices are visited in the order:
  (0, k, -k), (-2, 1+k, 1-k), (-4, 2+k, 2-k), ...
The first coordinate decreases by 2 each time → advances through all m values
since gcd(2,m) = 1.
-/

/-- Cycle 1 is Hamiltonian for odd m ≥ 3. -/
theorem cycle1_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 1) := by
  sorry

end ClaudesCycles
