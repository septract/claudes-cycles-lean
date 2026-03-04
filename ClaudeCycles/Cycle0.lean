/-
# Hamiltonicity of Cycle 0

Cycle 0 rules:
  s = 0:       j = -1 → bump i (0), else bump k (2)
  0 < s < m-1: i = -1 → bump k (2), else bump j (1)
  s = m-1:     i ≠ 0  → bump j (1), else bump k (2)

Proof structure (following Knuth):
  - i changes only when s = 0 ∧ j = -1, so each i-block is contiguous.
  - For i = 0: at s=0 returns within the block, k advances by 2. Since
    gcd(2,m) = 1 for odd m, all m k-values are visited.
  - For 0 < i < m-1: k advances by 1 at s=0 returns (trivial coverage).
  - For i = m-1: rules change (bump k instead of j at mid fibers),
    but coverage still holds.
  - Between s=0 returns, vertices are distinct (unique fiber assignment).
  - m i-blocks × m² vertices each = m³ total.
-/
import ClaudeCycles.Orbit

namespace ClaudeCycles

variable (m : ℕ) [NeZero m]

set_option linter.unusedSectionVars false in
/-! ## Direction lemmas for cycle 0 -/
section DirectionLemmas

/-- At s = 0, j = -1: cycle 0 bumps coordinate 0 (i). -/
theorem direction_zero_s0_j_neg (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    direction m 0 v = 0 := by
  simp only [direction, hs, hj, ↓reduceIte]

/-- At s = 0, j ≠ -1: cycle 0 bumps coordinate 2 (k). -/
theorem direction_zero_s0_j_ne (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) :
    direction m 0 v = 2 := by
  simp only [direction, hs, ↓reduceIte, hj]

/-- At 0 < s < m-1 (s ≠ 0 ∧ s ≠ -1), i = -1: cycle 0 bumps k. -/
theorem direction_zero_mid_i_neg (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 = -1) :
    direction m 0 v = 2 := by
  simp only [direction, hs0, hsm, hi, ↓reduceIte]

/-- At 0 < s < m-1 (s ≠ 0 ∧ s ≠ -1), i ≠ -1: cycle 0 bumps j. -/
theorem direction_zero_mid_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 ≠ -1) :
    direction m 0 v = 1 := by
  simp only [direction, hs0, hsm, hi, ↓reduceIte]

/-- At s = -1, i ≠ 0: cycle 0 bumps j. -/
theorem direction_zero_sm_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 ≠ 0) :
    direction m 0 v = 1 := by
  simp only [direction]; split_ifs <;> simp_all

/-- At s = -1, i = 0: cycle 0 bumps k. -/
theorem direction_zero_sm_i0 (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 = 0) :
    direction m 0 v = 2 := by
  simp only [direction]; split_ifs <;> simp_all

end DirectionLemmas

/-! ## i-stability: i changes only at s = 0 with j = -1 -/

/-- step 0 preserves the first coordinate unless s = 0 ∧ j = -1. -/
theorem step_zero_preserves_i (v : Vertex m)
    (h : ¬(fiber m v = 0 ∧ v.2.1 = -1)) :
    (step m 0 v).1 = v.1 := by
  push_neg at h
  by_cases hs0 : fiber m v = 0
  · simp only [step, direction_zero_s0_j_ne m v hs0 (h hs0), bump]
  · by_cases hsm : fiber m v = -1
    · by_cases hi : v.1 = 0
      · simp only [step, direction_zero_sm_i0 m v hs0 hsm hi, bump]
      · simp only [step, direction_zero_sm_i_ne m v hs0 hsm hi, bump]
    · by_cases hi : v.1 = -1
      · simp only [step, direction_zero_mid_i_neg m v hs0 hsm hi, bump]
      · simp only [step, direction_zero_mid_i_ne m v hs0 hsm hi, bump]

/-- At s = 0 with j = -1, step 0 increments i. -/
theorem step_zero_bumps_i (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    (step m 0 v).1 = v.1 + 1 := by
  unfold step bump; rw [direction_zero_s0_j_neg m v hs hj]

/-! ## Helper: nonzero cast -/

theorem natCast_ne_zero_of_lt (n : ℕ) (hn0 : 0 < n) (hnm : n < m) :
    (n : ZMod m) ≠ 0 := by
  intro h; rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hn0 h) (not_le.mpr hnm)

/-! ## i-preservation over m steps -/

/-- i is preserved over n steps (0 ≤ n ≤ m) from an s=0 vertex with j ≠ -1. -/
theorem iterate_preserves_i (v : Vertex m) (_hm : 1 < m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) (n : ℕ) (hn : n ≤ m) :
    ((step m 0)^[n] v).1 = v.1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk : k < m := Nat.lt_of_succ_le hn
    suffices h_pres : ¬(fiber m ((step m 0)^[k] v) = 0 ∧
        ((step m 0)^[k] v).2.1 = -1) by
      rw [step_zero_preserves_i m _ h_pres]; exact ih (le_of_lt hk)
    intro ⟨hfib, hjk⟩
    rw [iterate_fiber, hs, zero_add] at hfib
    by_cases hk0 : k = 0
    · subst hk0; simp at hjk; exact hj hjk
    · exact absurd hfib (natCast_ne_zero_of_lt m k (Nat.pos_of_ne_zero hk0) hk)

/-- After m steps from s=0 with i ≠ -1, j ≠ -1: i is preserved. -/
theorem m_step_preserves_i (v : Vertex m) (hm : 1 < m)
    (hs : fiber m v = 0) (_hi : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).1 = v.1 :=
  iterate_preserves_i m v hm hs hj m le_rfl

/-! ## m-step coordinate advance lemmas

These are the core computational lemmas. The proof requires tracing m steps
through the direction function. Each splits into:
  Step 1 (s=0, j≠-1): bump k
  Steps 2..m-1 (mid fiber, i≠-1): bump j
  Step m (s=-1): bump j if i≠0, bump k if i=0

For i=0: k gets bumped at steps 1 and m → advance by 2
For i≠0, i≠-1: k gets bumped only at step 1 → advance by 1
-/

/-- For i = 0: after m steps from s=0, k advances by 2. -/
theorem m_step_k_advance_i0 (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 = 0) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.2 = v.2.2 + 2 := by
  sorry

/-- For i = 0: after m steps from s=0, j retreats by 2. -/
theorem m_step_j_retreat_i0 (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 = 0) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.1 = v.2.1 - 2 := by
  sorry

/-- For 0 < i < m-1: after m steps from s=0, k advances by 1. -/
theorem m_step_k_advance_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi0 : v.1 ≠ 0) (him : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.2 = v.2.2 + 1 := by
  sorry

/-- For 0 < i < m-1: after m steps from s=0, j retreats by 1. -/
theorem m_step_j_retreat_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi0 : v.1 ≠ 0) (him : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.1 = v.2.1 - 1 := by
  sorry

/-! ## Hamiltonicity of cycle 0

For each i-block, the s=0 return points cycle through all m k-residues:
- i = 0: k advances by 2. gcd(2,m) = 1 for odd m → all values visited.
- 0 < i < m-1: k advances by 1 → trivially all values visited.
- i = m-1: special traversal (bump k at mid fibers, bump j at s=m-1).
  Still covers all values.

Between s=0 returns: m-1 distinct intermediate vertices (unique fibers).
m i-blocks × m² vertices = m³ total = |Vertex m|.
-/

/-- Cycle 0 is Hamiltonian for odd m ≥ 3. -/
theorem cycle0_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 0) := by
  sorry

end ClaudeCycles
