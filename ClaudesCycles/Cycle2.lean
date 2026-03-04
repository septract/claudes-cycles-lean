/-
# Hamiltonicity of Cycle 2

Cycle 2 rules:
  s = 0, j ≠ -1: bump i (0)
  s = 0, j = -1: bump k (2)
  0 < s < m-1, i ≠ -1: bump k (2)
  0 < s < m-1, i = -1: bump j (1)
  s = m-1:       bump i (0)

Proof structure (Knuth's Appendix):
  The s=0 vertices with j < m-1 are (0, j, -j), (2, j, -2-j),
  (4, j, -4-j), ...; the s=0 vertices with j = m-1 are (0, -1, 1),
  (1, -1, 0), (2, -1, -1), .... The "advance by 2" in i holds again.
-/
import ClaudesCycles.Orbit

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-! ## Direction lemmas for cycle 2 -/

/-- At s = 0, j ≠ -1: cycle 2 bumps i. -/
theorem direction_two_s0_j_ne (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) :
    direction m 2 v = 0 := by
  simp only [direction, hs, ↓reduceIte, if_pos hj]

/-- At s = 0, j = -1: cycle 2 bumps k. -/
theorem direction_two_s0_j_neg (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    direction m 2 v = 2 := by
  simp only [direction, hs, ↓reduceIte, hj, ne_eq, not_true_eq_false, if_neg]

/-- At 0 < s < m-1, i ≠ -1: cycle 2 bumps k. -/
theorem direction_two_mid_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 ≠ -1) :
    direction m 2 v = 2 := by
  simp only [direction, hs0, hsm, ↓reduceIte, if_pos hi]

/-- At 0 < s < m-1, i = -1: cycle 2 bumps j. -/
theorem direction_two_mid_i_neg (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 = -1) :
    direction m 2 v = 1 := by
  simp only [direction, hs0, hsm, ↓reduceIte, hi, ne_eq, not_true_eq_false, if_neg]

/-- At s = -1: cycle 2 bumps i. -/
theorem direction_two_sm (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) :
    direction m 2 v = 0 := by
  simp only [direction]; split_ifs <;> simp_all

/-! ## Hamiltonicity of cycle 2

Cycle 2's structure mirrors cycle 0 with the roles of i and k swapped:
- At mid fibers, cycle 2 bumps k (when i ≠ -1) or j (when i = -1).
- At s = 0, cycle 2 bumps i (when j ≠ -1) or k (when j = -1).
- At s = -1, cycle 2 always bumps i.

The "advance by 2" argument applies to the i-coordinate at s=0 returns
for "j-blocks" (where j is the stable coordinate).
-/

/-- Cycle 2 is Hamiltonian for odd m ≥ 3. -/
theorem cycle2_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 2) := by
  sorry

end ClaudesCycles
