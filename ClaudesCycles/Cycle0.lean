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

Proof by Aristotle (Harmonic) via return map on (x,y) coordinates at fiber 0.
  Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/
import ClaudesCycles.Orbit
import Mathlib.Tactic
-- Harmonic `generalize_proofs` tactic

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

/-! ## 2D Model for Cycle 0 Hamiltonicity

Return-map approach: define a 2D model `next_state` on the (x,y) coordinates at
fiber 0, show it has period m², then lift to period m³ via the fiber structure. -/

noncomputable section AristotleLemmas

def next_state (v : ZMod m × ZMod m) : ZMod m × ZMod m :=
  let x := v.1
  let y := v.2
  if y = -1 then
    if x = -2 then (-1, 0)
    else if x = -1 then (0, -3)
    else (x + 1, -2)
  else
    if x = -1 then (-1, y + 1)
    else if x = 0 then (0, y - 2)
    else (x, y - 1)

omit [NeZero m] in
lemma step_generic (v : Vertex m)
    (h1 : fiber m v ≠ 0) (h2 : fiber m v ≠ -1) :
    let v' := step m 0 v
    v'.1 = v.1 ∧
    (v.1 = -1 → v'.2.1 = v.2.1) ∧
    (v.1 ≠ -1 → v'.2.1 = v.2.1 + 1) := by
      unfold step direction bump; aesop

omit [NeZero m] in
lemma middle_steps' (hm3 : 3 ≤ m) (v : Vertex m)
    (h_fiber : fiber m v = 1) :
    let v' := (step m 0)^[m - 2] v
    v'.1 = v.1 ∧
    v'.2.1 = (if v.1 = -1 then v.2.1 else v.2.1 - 2) := by
      have h_fiber_k (k : ℕ) (_ : k ≤ m - 2) : fiber m ((step m 0)^[k] v) = 1 + k := by
        rw [iterate_fiber m 0, h_fiber]
      have h_ind : ∀ k ≤ m - 2,
          ((step m 0)^[k] v).1 = v.1 ∧
          ((step m 0)^[k] v).2.1 =
            if v.1 = -1 then v.2.1 else v.2.1 + k := by
        intro k hk_le
        induction' k with k ih <;>
          simp_all +decide [ Function.iterate_succ_apply' ]
        specialize ih ( Nat.le_of_succ_le hk_le )
        specialize h_fiber_k k ( Nat.le_of_succ_le hk_le )
        simp_all +decide [ ← add_assoc ]
        have h_step :
            fiber m ((step m 0)^[k] v) ≠ 0 ∧
            fiber m ((step m 0)^[k] v) ≠ -1 := by
          constructor <;> intro h <;>
            simp_all +decide
          · norm_cast at h_fiber_k
            rw [ eq_comm, ZMod.natCast_eq_zero_iff ] at h_fiber_k
            linarith [ Nat.le_of_dvd ( by linarith ) h_fiber_k,
              Nat.sub_add_cancel ( by linarith : 2 ≤ m ) ]
          · rw [ eq_comm ] at h_fiber_k
            rw [ eq_neg_iff_add_eq_zero ] at h_fiber_k
            norm_cast at h_fiber_k
            rw [ ZMod.natCast_eq_zero_iff ] at h_fiber_k
            linarith [ Nat.le_of_dvd ( by linarith ) h_fiber_k,
              Nat.sub_add_cancel ( by linarith : 2 ≤ m ) ]
        have := step_generic m ( ( step m 0 )^[k] v ) h_step.1 h_step.2; aesop;
      convert h_ind ( m - 2 ) le_rfl using 2 ; ring;
      rw [ Nat.cast_sub ( by linarith ) ] ; norm_num ; ring;

lemma return_map_eq_model (hm3 : 3 ≤ m) (v : Vertex m) (h : fiber m v = 0) :
    let v' := (step m 0)^[m] v
    (v'.1, v'.2.1) = next_state m (v.1, v.2.1) := by
      obtain ⟨v1, hv1⟩ : ∃ v1 : Vertex m, step m 0 v = v1 ∧ fiber m v1 = 1 := by
        have := fiber_step m 0 v; aesop;
      obtain ⟨v_end, hv_end⟩ : ∃ v_end : Vertex m,
          (step m 0)^[m - 2] v1 = v_end ∧ fiber m v_end = -1 ∧
          v_end.1 = v1.1 ∧
          v_end.2.1 = (if v1.1 = -1 then v1.2.1 else v1.2.1 - 2) := by
        have h_fiber_iter := iterate_fiber m 0 v1
        have := h_fiber_iter ( m - 2 )
        rcases m with ( _ | _ | m ) <;> simp_all +decide
        exact ⟨ by rw [ eq_neg_iff_add_eq_zero ]; norm_cast
                   simp +arith +decide,
               by simpa [ hv1.2 ] using
                 middle_steps' ( m + 2 )
                   ( Nat.le_trans ( by decide )
                     ( Nat.add_le_add_right hm3 2 ) ) v1 hv1.2 ⟩
      obtain ⟨v', hv'⟩ : ∃ v' : Vertex m,
          step m 0 v_end = v' ∧
          (v'.1, v'.2.1) = next_state m (v.1, v.2.1) := by
        unfold step at *; simp_all +decide [ direction ] ;
        unfold bump at *; simp_all +decide [ fiber ] ;
        rcases m with ( _ | _ | _ | m ) <;> norm_num at *;
        unfold next_state; simp +decide ;
        grind;
      rcases m with ( _ | _ | m ) <;> simp_all +decide [ Function.iterate_add_apply ];
      erw [ Function.iterate_succ_apply' ] ; aesop;

omit [NeZero m] in
lemma next_state_fst (v : ZMod m × ZMod m) (h : v.2 = -1) :
    (next_state m v).1 = v.1 + 1 := by
      have h_next_state : next_state m v =
          if v.1 = -2 then (-1, 0)
          else if v.1 = -1 then (0, -3)
          else (v.1 + 1, -2) := by
        unfold next_state; aesop;
      grind

omit [NeZero m] in
lemma next_state_snd_eq_neg_one (v : ZMod m × ZMod m) (h : v.2 ≠ -1) :
    (next_state m v).1 = v.1 := by
      unfold next_state
      simp [h];
      grind +ring

def entry_point (x : ZMod m) : ZMod m :=
  if x = -1 then 0
  else if x = 0 then -3
  else -2

omit [NeZero m] in
lemma next_state_entry (x : ZMod m) :
    (next_state m (x, -1)).2 = entry_point m (x + 1) := by
      unfold next_state entry_point;
      grind +ring

def column_delta (x : ZMod m) : ZMod m :=
  if x = -1 then 1
  else if x = 0 then -2
  else -1

lemma column_y_avoid_neg_one (hm : Odd m) (x : ZMod m) (k : ℕ) (hk : k < m - 1) :
    entry_point m x + k * column_delta m x ≠ -1 := by
      unfold column_delta entry_point;
      split_ifs <;> norm_num;
      · rw [ eq_neg_iff_add_eq_zero ];
        norm_cast;
        rw [ ZMod.natCast_eq_zero_iff ]
        exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ )
          ( Nat.lt_pred_iff.mp hk )
      · intro h
        have h_eq : (k : ZMod m) * 2 = -2 := by
          linear_combination' -h
        have h_eq' : (k : ZMod m) = -1 := by
          have h_eq' : (k : ZMod m) * 2 = (-1 : ZMod m) * 2 := by
            aesop
          have h_inv : ∃ y : ZMod m, y * 2 = 1 := by
            have h_inv : ∃ y : ℕ, y * 2 ≡ 1 [MOD m] := by
              exact ⟨ ( m + 1 ) / 2, by
                rw [ Nat.div_mul_cancel ( even_iff_two_dvd.mp
                  ( by simpa [ parity_simps ] using hm ) ) ]
                norm_num [ Nat.ModEq ] ⟩
            exact ⟨ h_inv.choose, by
              simpa [ ← ZMod.natCast_eq_natCast_iff ]
                using h_inv.choose_spec ⟩
          exact eq_of_sub_eq_zero ( by
            obtain ⟨ y, hy ⟩ := h_inv
            linear_combination' h_eq' * y - hy * ( k - -1 ) )
        have h_contra : k = m - 1 := by
          rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ];
          norm_num [ Fin.ext_iff ] at h_eq';
          rw [ Nat.mod_eq_of_lt ] at h_eq' <;> linarith
        exact hk.ne h_contra;
      · intro h; rw [ neg_add_eq_sub ] at h; rw [ sub_eq_iff_eq_add ] at h; norm_num at h;
        rw [ neg_eq_iff_add_eq_zero ] at h;
        norm_cast at h;
        rw [ ZMod.natCast_eq_zero_iff ] at h
        exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ )
          ( Nat.lt_pred_iff.mp hk ) h

set_option maxHeartbeats 800000 in -- Aristotle proof: case split + column_traversal
lemma column_traversal (hm : Odd m) (x : ZMod m) :
    let start := entry_point m x
    let delta := column_delta m x
    (∀ k < m, (next_state m)^[k] (x, start) = (x, start + k * delta)) ∧
    ((next_state m)^[m] (x, start)).1 = x + 1 := by
      have h_avoid : ∀ k < m - 1,
          let start := entry_point m x; let delta := column_delta m x
          start + k * delta ≠ -1 := by
        exact fun k hk => column_y_avoid_neg_one m hm x k hk
      have h_induction : ∀ k < m,
          let start := entry_point m x
          let delta := column_delta m x
          (next_state m)^[k] (x, start) = (x, start + k * delta) := by
        intro k hk
        induction' k with k ih
        all_goals generalize_proofs at *;
        · norm_num;
        · specialize ih ( Nat.lt_of_succ_lt hk )
          simp_all +decide [ Function.iterate_succ_apply' ]
          unfold next_state
          simp +decide [ add_mul, add_assoc ]
          split_ifs <;> simp_all +decide [ ← add_assoc ]
          all_goals have := h_avoid k ( Nat.lt_pred_iff.mpr hk )
          all_goals simp_all +decide [ column_delta ]
          · ring;
          · ring;
      specialize h_induction ( m - 1 )
      rcases m with ( _ | _ | m ) <;>
        simp_all +decide [ Function.iterate_succ_apply' ]
      · fin_cases x ; trivial;
      · refine ⟨ fun k hk => ?_, ?_ ⟩;
        · induction k with
          | zero => norm_num
          | succ k ih =>
            rw [ Function.iterate_succ_apply', ih ( by omega ) ];
            unfold next_state; simp +decide [ *, add_mul, add_assoc ] ;
            split_ifs <;> simp_all +decide [ add_assoc, sub_eq_add_neg ];
            · unfold column_delta; simp +decide ;
            · unfold column_delta; simp +decide [ * ] ;
            · unfold column_delta; aesop;
        · convert next_state_fst (m + 1 + 1) _ _ using 1;
          unfold column_delta entry_point; norm_num; ring;
          split_ifs <;> norm_num [
            show ( m : ZMod ( m + 1 + 1 ) ) = -2 by
              exact eq_neg_of_add_eq_zero_left
                ( by norm_cast; simp +arith +decide ) ]

set_option maxHeartbeats 800000 in -- Aristotle proof: case split + column_step
lemma column_step (hm : Odd m) (x : ZMod m) :
    (next_state m)^[m] (x, entry_point m x) = (x + 1, entry_point m (x + 1)) := by
      have h_col_traversal : ∀ k < m,
          (next_state m)^[k] (x, entry_point m x) =
            (x, entry_point m x + k * column_delta m x) := by
        exact (column_traversal m hm x).1
      have h_col_traversal_last : (next_state m)^[m - 1] (x, entry_point m x) = (x, -1) := by
        convert h_col_traversal ( m - 1 ) ( Nat.sub_lt ( NeZero.pos m ) zero_lt_one ) using 1;
        unfold column_delta entry_point
        norm_num [ hm, Nat.even_sub
          ( show 1 ≤ m from NeZero.pos m ) ]
        split_ifs <;> norm_num [ Nat.cast_sub
          ( show 1 ≤ m from NeZero.pos m ) ]
      rcases m with ( _ | _ | m ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
      · fin_cases x ; trivial;
      · simp_all +decide [ next_state, entry_point ];
        grind +ring

lemma delta_is_unit (hm : Odd m) (x : ZMod m) :
    IsUnit (column_delta m x) := by
      obtain ⟨u, hu⟩ : ∃ u : ZMod m, 2 * u = 1 := by
        have h_inv : ∃ u : ℤ, 2 * u ≡ 1 [ZMOD m] := by
          exact ⟨ ( m + 1 ) / 2, by
            rw [ mul_comm, Int.ediv_mul_cancel
              ( even_iff_two_dvd.mp
                ( by simpa [ parity_simps ] using hm ) ) ]
            norm_num [ Int.ModEq ] ⟩
        exact ⟨ h_inv.choose, by
          simpa [ ← ZMod.intCast_eq_intCast_iff ]
            using h_inv.choose_spec ⟩
      unfold column_delta;
      split_ifs <;> norm_num [ ← hu, isUnit_iff_exists_inv ];
      · exact ⟨ -u, by linear_combination' hu ⟩;
      · exact ⟨ -1, by norm_num ⟩

lemma orbit_formula (hm : Odd m) (i : ℕ) (j : ℕ) (hi : i < m) (hj : j < m) :
    (next_state m)^[i * m + j] (0, entry_point m 0) =
    ((i : ZMod m), entry_point m i + (j : ZMod m) * column_delta m i) := by
      induction i generalizing j with
      | zero =>
        convert (column_traversal m hm 0).1 j hj using 1
        · aesop
        · grind
      | succ i ih =>
        convert (column_traversal m hm ( i + 1 )).1 j hj using 1;
        · convert congr_arg
            ( fun x : ZMod m × ZMod m =>
              ( next_state m )^[j] x )
            ( column_step m hm i ) using 1;
          rw [ ← Function.iterate_add_apply ]; ring;
          convert congr_arg
            ( fun x : ZMod m × ZMod m =>
              ( next_state m )^[m + j] x )
            ( ih 0 ( Nat.lt_of_succ_lt hi )
              ( Nat.zero_lt_of_lt hj ) ) using 1; ring;
          · rw [ ← Function.iterate_add_apply, add_right_comm ];
            ac_rfl;
          · norm_num;
        · norm_num

set_option maxHeartbeats 1600000 in -- Aristotle proof: minimality via orbit_formula
lemma model_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    ∀ x : ZMod m × ZMod m, Function.minimalPeriod (next_state m) x = m ^ 2 := by
      have h_start : Function.minimalPeriod (next_state m) (0, entry_point m 0) = m^2 := by
        rw [ Function.minimalPeriod ];
        split_ifs <;> norm_num at *;
        · simp_all +decide [ Nat.find_eq_iff ];
          refine ⟨ ⟨ by positivity, ?_ ⟩, ?_ ⟩;
          · rw [ sq, Function.IsPeriodicPt, Function.IsFixedPt ];
            have h_step : ∀ x : ZMod m,
                (next_state m)^[m] (x, entry_point m x) =
                  (x + 1, entry_point m (x + 1)) := by
              exact column_step m hm
            have h_step_m : ∀ x : ZMod m, ∀ k : ℕ,
                (next_state m)^[k * m] (x, entry_point m x) =
                  (x + k, entry_point m (x + k)) := by
              intro x k
              induction k <;>
                simp_all +decide [ Nat.succ_mul, ← add_assoc ]
              rw [ add_comm, Function.iterate_add_apply,
                ‹ ( next_state m ) ^[ _ * m ]
                  ( x, entry_point m x ) = _ ›, h_step ]
            simpa [ mul_comm ] using h_step_m 0 m;
          · intro n hn hn_pos hn_periodic
            have h_orbit : (next_state m)^[n] (0, entry_point m 0) = (0, entry_point m 0) := by
              exact hn_periodic.eq;
            obtain ⟨i, j, hi, hj, hn_eq⟩ :
                ∃ i j : ℕ, i < m ∧ j < m ∧ n = i * m + j := by
              exact ⟨ n / m, n % m,
                Nat.div_lt_of_lt_mul <| by linarith,
                Nat.mod_lt _ <| by positivity,
                by rw [ Nat.div_add_mod' ] ⟩
            have h_orbit_eq :
                (i : ZMod m) = 0 ∧
                entry_point m i + j * column_delta m i =
                  entry_point m 0 := by
              have h_orbit_eq :
                  (next_state m)^[i * m + j]
                    (0, entry_point m 0) =
                  ((i : ZMod m), entry_point m i +
                    (j : ZMod m) * column_delta m i) := by
                convert orbit_formula m hm i j hi hj using 1;
              aesop;
            rw [ ZMod.natCast_eq_zero_iff ] at h_orbit_eq
            simp_all +decide
              [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ]
            simp_all +decide [ entry_point, column_delta ];
            have h_contra : (j : ZMod m) = 0 := by
              have h_contra : IsUnit (2 : ZMod m) := by
                have h_contra :
                    ∃ k : ℕ, 2 * k ≡ 1 [MOD m] := by
                  exact ⟨ ( m + 1 ) / 2, by
                    rw [ mul_comm, Nat.div_mul_cancel
                      ( even_iff_two_dvd.mp
                        ( by simpa [ parity_simps ]
                              using hm ) ) ]
                    norm_num [ Nat.ModEq ] ⟩
                obtain ⟨ k, hk ⟩ := h_contra
                exact isUnit_iff_exists_inv.mpr
                  ⟨ k, by simpa
                    [ ← ZMod.natCast_eq_natCast_iff ]
                    using hk ⟩
              exact h_contra.mul_left_inj.mp ( by aesop )
            exact absurd h_contra ( by
              rw [ ZMod.natCast_eq_zero_iff ]
              exact Nat.not_dvd_of_pos_of_lt hn_pos hj )
        · rename_i h;
          contrapose! h;
          use m^2;
          simp +decide [ sq, Function.IsPeriodicPt, Function.IsFixedPt ];
          refine ⟨ by linarith, ?_ ⟩;
          have h_step : ∀ x : ZMod m,
              (next_state m)^[m] (x, entry_point m x) =
                (x + 1, entry_point m (x + 1)) := by
              exact column_step m hm
          have h_step_m2 : ∀ x : ZMod m,
              (next_state m)^[m * m] (x, entry_point m x) =
                (x + m, entry_point m (x + m)) := by
            intro x
            have h_step_m2 : ∀ k : ℕ,
                (next_state m)^[k * m] (x, entry_point m x) =
                  (x + k, entry_point m (x + k)) := by
              intro k
              induction k with
              | zero => norm_num
              | succ k ih =>
                rw [ Nat.succ_mul, add_comm,
                  Function.iterate_add_apply, ih, h_step ]
                push_cast; ring
            exact h_step_m2 m;
          simpa using h_step_m2 0;
      have h_orbit : ∀ x : ZMod m × ZMod m,
          x ∈ {(next_state m)^[i] (0, entry_point m 0) |
            i < m^2} := by
        intro x
        obtain ⟨i, j, hi, hj, hx⟩ :
            ∃ i j : ℕ, i < m ∧ j < m ∧
            x = ((i : ZMod m), entry_point m i +
              (j : ZMod m) * column_delta m i) := by
          obtain ⟨i, j, hi, hj, hx⟩ :
              ∃ i j : ZMod m,
              x = (i, entry_point m i +
                j * column_delta m i) := by
            use x.1;
            have h_unit : IsUnit (column_delta m x.1) := by
              exact delta_is_unit m hm x.1
            obtain ⟨ j, hj ⟩ := h_unit.exists_right_inv;
            exact ⟨ ( x.2 - entry_point m x.1 ) * j,
              Prod.ext rfl <| by
                linear_combination'
                  hj.symm * ( x.2 - entry_point m x.1 ) ⟩
          use i.val, j.val;
          exact ⟨ i.val_lt, j.val_lt, by cases m <;> aesop ⟩;
        use i * m + j;
        exact ⟨ by nlinarith, hx ▸ orbit_formula m hm i j hi hj ⟩;
      intro x
      obtain ⟨i, hi, hx⟩ := h_orbit x
      have h_period :
          Function.minimalPeriod (next_state m) x =
          Function.minimalPeriod (next_state m)
            (0, entry_point m 0) := by
        rw [ ← hx, Function.minimalPeriod_apply_iterate ];
        use m^2;
        exact ⟨ by positivity, by rw [ ← h_start ] ; exact Function.isPeriodicPt_minimalPeriod _ _ ⟩
      rw [h_period, h_start]

omit [NeZero m] in
lemma period_scaling {S : Type*} (f : S → S) (fib : S → ZMod m)
    (h_fiber : ∀ x, fib (f x) = fib x + 1) (x : S) :
    Function.minimalPeriod f x = m * Function.minimalPeriod (f^[m]) x := by
      have h_one_cycle :
          Function.minimalPeriod f x ∣
            m * Function.minimalPeriod (f^[m]) x ∧
          m * Function.minimalPeriod (f^[m]) x ∣
            Function.minimalPeriod f x := by
        constructor;
        · have h_iter : (f^[m])^[Function.minimalPeriod (f^[m]) x] x = x :=
            Function.isPeriodicPt_minimalPeriod _ _
          rw [ ← Function.iterate_mul, mul_comm ] at h_iter;
          rw [ Nat.mul_comm ];
          exact Function.IsPeriodicPt.minimalPeriod_dvd h_iter
        · have h_min_period : f^[Function.minimalPeriod f x] x = x := by
            exact Function.isPeriodicPt_minimalPeriod f x;
          have h_div : m ∣ Function.minimalPeriod f x := by
            have h_fiber_period :
                fib (f^[Function.minimalPeriod f x] x) =
                  fib x + Function.minimalPeriod f x := by
              refine Nat.recOn
                ( Function.minimalPeriod f x ) ?_ ?_ <;>
                simp_all +decide
                  [ Function.iterate_succ_apply', add_assoc ]
            simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
          obtain ⟨ k, hk ⟩ := h_div
          simp_all +decide
            [ Function.iterate_mul ]
          exact Nat.mul_dvd_mul_left m
            ( Function.IsPeriodicPt.minimalPeriod_dvd
              ( by aesop ) )
      exact Nat.dvd_antisymm h_one_cycle.1 h_one_cycle.2

omit [NeZero m] in
lemma fiber_zero_determined (v1 v2 : Vertex m)
    (h1 : fiber m v1 = 0) (h2 : fiber m v2 = 0)
    (hx : v1.1 = v2.1) (hy : v1.2.1 = v2.2.1) : v1 = v2 := by
      have h_third : v1.2.2 = -v1.1 - v1.2.1 ∧ v2.2.2 = -v2.1 - v2.2.1 := by
        unfold fiber at h1 h2; exact ⟨ by linear_combination' h1, by linear_combination' h2 ⟩ ;
      aesop

def model_to_vertex (x : ZMod m × ZMod m) : Vertex m :=
  (x.1, x.2, -(x.1 + x.2))

omit [NeZero m] in
lemma model_to_vertex_fiber (x : ZMod m × ZMod m) :
    fiber m (model_to_vertex m x) = 0 := by
      unfold fiber model_to_vertex; ring;

omit [NeZero m] in
lemma model_to_vertex_inj :
    Function.Injective (model_to_vertex m) := by
      intro x y hxy; simp [model_to_vertex] at hxy; aesop;

lemma conjugacy (hm3 : 3 ≤ m) (x : ZMod m × ZMod m) :
    (step m 0)^[m] (model_to_vertex m x) = model_to_vertex m (next_state m x) := by
      apply fiber_zero_determined m;
      · rw [ iterate_m_fiber m 0 ];
        exact model_to_vertex_fiber m x;
      · exact model_to_vertex_fiber m (next_state m x);
      · have := return_map_eq_model m hm3 (model_to_vertex m x) (model_to_vertex_fiber m x);
        convert congr_arg Prod.fst this using 1;
      · convert congr_arg Prod.snd
          ( return_map_eq_model m hm3
            ( model_to_vertex m x )
            (model_to_vertex_fiber m x) ) using 1

lemma period_conjugacy (hm3 : 3 ≤ m) (x : ZMod m × ZMod m) :
    Function.minimalPeriod ((step m 0)^[m]) (model_to_vertex m x) =
    Function.minimalPeriod (next_state m) x := by
      rw [ Function.minimalPeriod, Function.minimalPeriod ];
      congr! 2;
      · ext n; simp [Function.IsPeriodicPt];
        intro hn_pos
        have h_conj : ∀ n : ℕ,
            (step m 0)^[m * n] (model_to_vertex m x) =
              model_to_vertex m ((next_state m)^[n] x) := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [ Nat.mul_succ, add_comm,
              Function.iterate_add_apply, ih,
              Function.iterate_succ_apply' ]
            exact conjugacy m hm3 ((next_state m)^[n] x);
        simp_all +decide [ Function.iterate_mul, Function.IsFixedPt ];
        exact ⟨ fun h => by simpa using model_to_vertex_inj m h, fun h => by simp [ h ] ⟩;
      · constructor;
        · rintro ⟨ n, hn, hn' ⟩;
          use n;
          have h_conj : ∀ k : ℕ,
              (step m 0)^[m * k] (model_to_vertex m x) =
                model_to_vertex m
                  ((next_state m)^[k] x) := by
            intro k
            induction k <;> simp_all +decide
              [ Nat.mul_succ, Function.iterate_succ_apply' ]
            rw [ Nat.add_comm,
              Function.iterate_add_apply,
              ‹ ( step m 0 ) ^[ m * _ ]
                ( model_to_vertex m x ) =
                model_to_vertex m
                  ( ( next_state m ) ^[ _ ] x ) › ]
            exact conjugacy m hm3 ((next_state m)^[‹ℕ›] x);
          have := h_conj n; simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt ] ;
          have := h_conj n; simp_all +decide [ Function.iterate_mul ] ;
          exact model_to_vertex_inj m this.symm;
        · rintro ⟨ k, hk ⟩;
          use k;
          simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt ];
          have h_conj :
              (step m 0)^[m]^[k] (model_to_vertex m x) =
                model_to_vertex m
                  ((next_state m)^[k] x) := by
            refine Nat.recOn k ?_ ?_ <;>
              simp_all +decide
                [ Function.iterate_succ_apply' ]
            exact fun n _ => conjugacy m hm3 ((next_state m)^[n] x);
          rw [ h_conj, hk.2 ]

omit [NeZero m] in
lemma exists_model_preimage (v : Vertex m)
    (h : fiber m v = 0) :
    ∃ x : ZMod m × ZMod m, model_to_vertex m x = v := by
      use (v.1, v.2.1);
      simp [model_to_vertex];
      ext <;> simp_all +decide [ fiber ];
      linear_combination -h

lemma step_period_fiber0 (_hm : Odd m) (hm3 : 3 ≤ m)
    (h_model : ∀ x : ZMod m × ZMod m, Function.minimalPeriod (next_state m) x = m ^ 2)
    (u : Vertex m) (hu : fiber m u = 0) :
    Function.minimalPeriod (step m 0) u = m ^ 3 := by
      obtain ⟨ x, rfl ⟩ := exists_model_preimage m u hu;
      convert period_scaling m ( step m 0 ) ( fiber m ) _ ( model_to_vertex m x ) using 1;
      · rw [ period_conjugacy m hm3 x, h_model ] ; ring;
      · exact fiber_step m 0

end AristotleLemmas

/-- Cycle 0 is Hamiltonian for odd m ≥ 3. -/
theorem cycle0_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 0) := by
  set f : Vertex m → Vertex m := step m 0;
  intro v
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k < m ∧ fiber m (f^[k] v) = 0 := by
    have h_fiber_iter : ∀ k : ℕ, fiber m (f^[k] v) = fiber m v + k :=
      fun k => iterate_fiber m 0 v k
    obtain ⟨k, hk⟩ : ∃ k : ZMod m, fiber m v + k = 0 := by
      exact ⟨ -fiber m v, by ring ⟩;
    exact ⟨ k.val, k.val_lt, by simpa [ h_fiber_iter ] using hk ⟩
  have h_period : Function.minimalPeriod f (f^[k] v) = m ^ 3 := by
    apply step_period_fiber0 m hm hm3 (model_hamiltonian m hm hm3) (f^[k] v) hk.right
  have h_period_eq : Function.minimalPeriod f v = Function.minimalPeriod f (f^[k] v) := by
    have h_period_eq : ∀ x : Vertex m,
        Function.minimalPeriod f x =
          Function.minimalPeriod f (f x) := by
      intros x
      have h_period_iff : ∀ n : ℕ, f^[n] x = x ↔ f^[n] (f x) = f x := by
        intro n
        constructor
        · intro hn
          have h_eq : f^[n] (f x) = f (f^[n] x) := by
            exact Function.iterate_succ_apply' f n x ▸ rfl
          rw [h_eq, hn]
        · intro hn
          apply (step_bijective m 0).injective
          change f (f^[n] x) = f x
          rw [← Function.iterate_succ_apply' f n x, Function.iterate_succ_apply f n x]
          exact hn
      exact Nat.dvd_antisymm
        (Function.IsPeriodicPt.minimalPeriod_dvd
          ((h_period_iff _).mpr
            (Function.isPeriodicPt_minimalPeriod f (f x))))
        (Function.IsPeriodicPt.minimalPeriod_dvd
          ((h_period_iff _).mp
            (Function.isPeriodicPt_minimalPeriod f x)))
    exact Nat.recOn k rfl fun n hn => by rw [ Function.iterate_succ_apply', ← h_period_eq, hn ] ;
  rw [h_period_eq, h_period]

end ClaudesCycles
