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
import ClaudesCycles.Orbit

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-! ## Direction lemmas for cycle 0 -/
section DirectionLemmas

omit [NeZero m] in
/-- At s = 0, j = -1: cycle 0 bumps coordinate 0 (i). -/
theorem direction_zero_s0_j_neg (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    direction m 0 v = 0 := by
  simp only [direction, hs, hj, ↓reduceIte]

omit [NeZero m] in
/-- At s = 0, j ≠ -1: cycle 0 bumps coordinate 2 (k). -/
theorem direction_zero_s0_j_ne (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) :
    direction m 0 v = 2 := by
  simp only [direction, hs, ↓reduceIte, hj]

omit [NeZero m] in
/-- At 0 < s < m-1 (s ≠ 0 ∧ s ≠ -1), i = -1: cycle 0 bumps k. -/
theorem direction_zero_mid_i_neg (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 = -1) :
    direction m 0 v = 2 := by
  simp only [direction, hs0, hsm, hi, ↓reduceIte]

omit [NeZero m] in
/-- At 0 < s < m-1 (s ≠ 0 ∧ s ≠ -1), i ≠ -1: cycle 0 bumps j. -/
theorem direction_zero_mid_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 ≠ -1) :
    direction m 0 v = 1 := by
  simp only [direction, hs0, hsm, hi, ↓reduceIte]

omit [NeZero m] in
/-- At s = -1, i ≠ 0: cycle 0 bumps j. -/
theorem direction_zero_sm_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 ≠ 0) :
    direction m 0 v = 1 := by
  simp only [direction]; split_ifs <;> simp_all

omit [NeZero m] in
/-- At s = -1, i = 0: cycle 0 bumps k. -/
theorem direction_zero_sm_i0 (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 = 0) :
    direction m 0 v = 2 := by
  simp only [direction]; split_ifs <;> simp_all

end DirectionLemmas

/-! ## i-stability: i changes only at s = 0 with j = -1 -/

omit [NeZero m] in
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

omit [NeZero m] in
/-- At s = 0 with j = -1, step 0 increments i. -/
theorem step_zero_bumps_i (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    (step m 0 v).1 = v.1 + 1 := by
  unfold step bump; rw [direction_zero_s0_j_neg m v hs hj]

/-! ## i-preservation over m steps -/

omit [NeZero m] in
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
    · subst hk0; simp only [Function.iterate_zero, id_eq] at hjk; exact hj hjk
    · exact absurd hfib (natCast_ne_zero_of_lt m k (Nat.pos_of_ne_zero hk0) hk)

omit [NeZero m] in
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

/-! ### Tracking the full vertex through m steps

For steps 2..m-1, the vertex at iterate n (1 ≤ n ≤ m-2) from s=0 with i≠-1 is:
  (i, j + n - 1, k + 1) with fiber = n.
Step 1 bumps k (s=0), steps 2..m-1 bump j (mid fiber), step m depends on i. -/

omit [NeZero m] in
/-- After step 1 from s=0, j≠-1: the vertex is (i, j, k+1) with fiber 1. -/
theorem step1_from_s0 (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) :
    step m 0 v = (v.1, v.2.1, v.2.2 + 1) := by
  simp only [step, direction_zero_s0_j_ne m v hs hj, bump]

omit [NeZero m] in
/-- At mid fiber with i≠-1, step bumps j only: (i, j+1, k) -/
theorem step_mid (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 ≠ -1) :
    step m 0 v = (v.1, v.2.1 + 1, v.2.2) := by
  simp only [step, direction_zero_mid_i_ne m v hs0 hsm hi, bump]

omit [NeZero m] in
/-- After n mid-fiber steps (from fiber=1, i≠-1), the vertex is
    (i, j+n, k) with fiber 1+n. -/
theorem iterate_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hfib : fiber m v = 1) (hi : v.1 ≠ -1)
    (n : ℕ) (hn : n ≤ m - 2) :
    (step m 0)^[n] v = (v.1, v.2.1 + n, v.2.2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k < m - 2 := Nat.lt_of_succ_le hn
    rw [Function.iterate_succ_apply', ih (le_of_lt hk)]
    have hfib_k : fiber m (v.1, v.2.1 + ↑k, v.2.2) = 1 + (k : ZMod m) := by
      simp only [fiber]; rw [← hfib]; simp [fiber]; ring
    have hne0 : 1 + (k : ZMod m) ≠ 0 := by
      have := natCast_ne_zero_of_lt m (1 + k) (by omega) (by omega)
      push_cast at this; exact this
    have hnem : 1 + (k : ZMod m) ≠ -1 := by
      intro h
      have h2 : (1 + (k : ZMod m)) + 1 = 0 := by rw [h]; ring
      have h3 : ((k + 2 : ℕ) : ZMod m) = 0 := by
        have : ((k + 2 : ℕ) : ZMod m) = 1 + (k : ZMod m) + 1 := by push_cast; ring
        rw [this, h2]
      rw [ZMod.natCast_eq_zero_iff] at h3
      exact absurd (Nat.le_of_dvd (by omega) h3) (by omega)
    have hs0' : fiber m (v.1, v.2.1 + ↑k, v.2.2) ≠ 0 := by rw [hfib_k]; exact hne0
    have hsm' : fiber m (v.1, v.2.1 + ↑k, v.2.2) ≠ -1 := by rw [hfib_k]; exact hnem
    rw [step_mid m _ hs0' hsm' hi]
    simp only [Prod.mk.injEq, true_and, and_true]
    push_cast; ring

omit [NeZero m] in
/-- Full m-step formula, i=0 case. From (0, j, k) with s=0, j≠-1:
    after m steps → (0, j+(m-2), k+2). -/
theorem m_step_i0 (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 = 0) (hj : v.2.1 ≠ -1) :
    (step m 0)^[m] v = (v.1, v.2.1 + (m - 2 : ℕ), v.2.2 + 2) := by
  have hiter : (step m 0)^[m] v = (step m 0)^[1 + (m - 2) + 1] v := by congr 2; omega
  rw [hiter, Function.iterate_add, Function.iterate_add, Function.comp_apply,
      Function.comp_apply]
  rw [Function.iterate_one, step1_from_s0 m v hs hj]
  have hfib1 : fiber m (v.1, v.2.1, v.2.2 + 1) = 1 := by
    have : fiber m (v.1, v.2.1, v.2.2 + 1) = fiber m v + 1 := by simp [fiber]; ring
    rw [this, hs, zero_add]
  have him : v.1 ≠ -1 := by rw [hi]; exact zero_ne_neg_one m (by omega)
  rw [iterate_mid m (v.1, v.2.1, v.2.2 + 1) hm3 hfib1 him (m - 2) le_rfl]
  -- Step m: s = m-1, i = 0 → bump k
  have hcast2 : ((m - 2 : ℕ) : ZMod m) = -2 := natCast_sub_eq_neg m 2 (by omega)
  have hfib_last : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) = -1 := by
    have : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) = fiber m v + (↑(m - 2) + 1) := by
      simp [fiber]; ring
    rw [this, hs, zero_add, hcast2]; ring
  have hne0 : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) ≠ 0 := by
    rw [hfib_last]; exact neg_one_ne_zero m (by omega)
  rw [step, direction_zero_sm_i0 m _ hne0 hfib_last hi, bump]
  simp only [Prod.mk.injEq, true_and]; ring

omit [NeZero m] in
/-- For i = 0: after m steps from s=0, k advances by 2. -/
theorem m_step_k_advance_i0 (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 = 0) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.2 = v.2.2 + 2 := by
  rw [m_step_i0 m v hm3 hs hi hj]

omit [NeZero m] in
/-- For i = 0: after m steps from s=0, j retreats by 2. -/
theorem m_step_j_retreat_i0 (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 = 0) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.1 = v.2.1 - 2 := by
  rw [m_step_i0 m v hm3 hs hi hj]
  change v.2.1 + ↑(m - 2) = v.2.1 - 2
  rw [natCast_sub_eq_neg m 2 (by omega)]; ring

omit [NeZero m] in
/-- Full m-step formula, 0<i<m-1 case. From (i, j, k) with s=0, i≠0, i≠-1, j≠-1:
    after m steps → (i, j+(m-1), k+1). -/
theorem m_step_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi0 : v.1 ≠ 0) (him : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    (step m 0)^[m] v = (v.1, v.2.1 + (m - 1 : ℕ), v.2.2 + 1) := by
  have hiter : (step m 0)^[m] v = (step m 0)^[1 + (m - 2) + 1] v := by congr 2; omega
  rw [hiter, Function.iterate_add, Function.iterate_add, Function.comp_apply,
      Function.comp_apply]
  rw [Function.iterate_one, step1_from_s0 m v hs hj]
  have hfib1 : fiber m (v.1, v.2.1, v.2.2 + 1) = 1 := by
    have : fiber m (v.1, v.2.1, v.2.2 + 1) = fiber m v + 1 := by simp [fiber]; ring
    rw [this, hs, zero_add]
  rw [iterate_mid m (v.1, v.2.1, v.2.2 + 1) hm3 hfib1 him (m - 2) le_rfl]
  -- Step m: s = m-1, i ≠ 0 → bump j
  have hcast2 : ((m - 2 : ℕ) : ZMod m) = -2 := natCast_sub_eq_neg m 2 (by omega)
  have hfib_last : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) = -1 := by
    have : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) = fiber m v + (↑(m - 2) + 1) := by
      simp [fiber]; ring
    rw [this, hs, zero_add, hcast2]; ring
  have hne0 : fiber m (v.1, v.2.1 + ↑(m - 2), v.2.2 + 1) ≠ 0 := by
    rw [hfib_last]; exact neg_one_ne_zero m (by omega)
  rw [step, direction_zero_sm_i_ne m _ hne0 hfib_last hi0, bump]
  simp only [Prod.mk.injEq, true_and, and_true]
  rw [hcast2, natCast_sub_eq_neg m 1 (by omega)]; push_cast; ring

omit [NeZero m] in
/-- For 0 < i < m-1: after m steps from s=0, k advances by 1. -/
theorem m_step_k_advance_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi0 : v.1 ≠ 0) (him : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.2 = v.2.2 + 1 := by
  rw [m_step_mid m v hm3 hs hi0 him hj]

omit [NeZero m] in
/-- For 0 < i < m-1: after m steps from s=0, j retreats by 1. -/
theorem m_step_j_retreat_mid (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi0 : v.1 ≠ 0) (him : v.1 ≠ -1) (hj : v.2.1 ≠ -1) :
    ((step m 0)^[m] v).2.1 = v.2.1 - 1 := by
  rw [m_step_mid m v hm3 hs hi0 him hj]
  change v.2.1 + ↑(m - 1) = v.2.1 - 1
  rw [natCast_sub_eq_neg m 1 (by omega)]; ring

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

end ClaudesCycles
