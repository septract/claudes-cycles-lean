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

Proof by Aristotle (Harmonic) via return map F on (i,j) coordinates at fiber 0.
  Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/
import ClaudesCycles.Orbit
import Mathlib.Tactic

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-! ## Direction lemmas for cycle 2 -/

omit [NeZero m] in
/-- At s = 0, j ≠ -1: cycle 2 bumps i. -/
theorem direction_two_s0_j_ne (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 ≠ -1) :
    direction m 2 v = 0 := by
  simp only [direction, hs, ↓reduceIte, if_pos hj]

omit [NeZero m] in
/-- At s = 0, j = -1: cycle 2 bumps k. -/
theorem direction_two_s0_j_neg (v : Vertex m)
    (hs : fiber m v = 0) (hj : v.2.1 = -1) :
    direction m 2 v = 2 := by
  simp only [direction, hs, ↓reduceIte, hj, ne_eq, not_true_eq_false]

omit [NeZero m] in
/-- At 0 < s < m-1, i ≠ -1: cycle 2 bumps k. -/
theorem direction_two_mid_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 ≠ -1) :
    direction m 2 v = 2 := by
  simp only [direction, hs0, hsm, ↓reduceIte, if_pos hi]

omit [NeZero m] in
/-- At 0 < s < m-1, i = -1: cycle 2 bumps j. -/
theorem direction_two_mid_i_neg (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) (hi : v.1 = -1) :
    direction m 2 v = 1 := by
  simp only [direction, hs0, hsm, ↓reduceIte, hi, ne_eq, not_true_eq_false]

omit [NeZero m] in
/-- At s = -1: cycle 2 bumps i. -/
theorem direction_two_sm (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) :
    direction m 2 v = 0 := by
  simp only [direction]; split_ifs <;> simp_all

/-! ## Return map F and Hamiltonicity of cycle 2

The proof defines a return map F on the (i, j) coordinates at fiber 0,
then shows F has minimal period m² at every point, giving total period m³. -/

noncomputable section

/-- The return map for cycle 2 at fiber 0: maps (i, j) to the (i, j) coordinates
    after m steps of the cycle 2 step function. -/
def F (v : ZMod m × ZMod m) : ZMod m × ZMod m :=
  if v.2 = -1 then (v.1 + 1, if v.1 = -1 then v.2 - 2 else v.2)
  else (v.1 + 2, if v.1 = -2 then v.2 - 2 else v.2)

/-- After m-2 steps from fiber 1, i is unchanged and j shifts by -2 if i = -1. -/
lemma step_mid_phase (hm3 : 3 ≤ m) (v : Vertex m) (hv : fiber m v = 1) :
    let v' := (step m 2)^[m-2] v
    v'.1 = v.1 ∧ v'.2.1 = v.2.1 + (if v.1 = -1 then -2 else 0) := by
  have h_fiber_range : ∀ k < m - 2, (fiber m ((step m 2)^[k] v)) ≠ 0 ∧ (fiber m ((step m 2)^[k] v)) ≠ -1 := by
    intros k hk_lt
    have h_fiber : fiber m ((step m 2)^[k] v) = 1 + k := by
      convert iterate_fiber m 2 v k using 1; aesop
    constructor <;> intro h <;> simp_all +decide [ ZMod.neg_eq_self_iff ];
    · rw [ eq_comm ] at h_fiber;
      norm_cast at h_fiber;
      rw [ ZMod.natCast_eq_zero_iff ] at h_fiber; linarith [ Nat.le_of_dvd ( by linarith ) h_fiber, Nat.sub_add_cancel ( by linarith : 2 ≤ m ) ]
    · rw [ neg_eq_iff_add_eq_zero ] at h_fiber;
      norm_cast at h_fiber;
      rw [ ZMod.natCast_eq_zero_iff ] at h_fiber; linarith [ Nat.le_of_dvd ( by linarith ) h_fiber, Nat.sub_add_cancel ( by linarith : 2 ≤ m ) ]
  have h_step : ∀ k < m - 2, (step m 2)^[k] v = (v.1, v.2.1 + if v.1 = -1 then k else 0, v.2.2 + if v.1 ≠ -1 then k else 0) := by
    intro k hk_lt; induction' k <;> simp_all +decide [ Function.iterate_succ_apply' ];
    rename_i k ih; specialize ih ( Nat.lt_of_succ_lt hk_lt ); simp_all +decide [ step ];
    specialize h_fiber_range k ( Nat.lt_of_succ_lt hk_lt ); simp_all +decide [ fiber, direction ];
    split_ifs <;> simp_all +decide [ bump ]; ring;
    ring
  rcases m with ( _ | _ | _ | m ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
  split_ifs <;> simp_all +decide [ step ];
  · unfold direction; simp +decide [ *, bump ];
    norm_num [ add_assoc ];
    norm_cast
  · unfold direction; aesop

set_option maxHeartbeats 800000 in
/-- m steps of cycle 2 from fiber 0 corresponds to one application of F. -/
lemma step_pow_m_eq_F (hm : Odd m) (hm3 : 3 ≤ m) (v : Vertex m) (hv : fiber m v = 0) :
    let v' := (step m 2)^[m] v
    (v'.1, v'.2.1) = F m (v.1, v.2.1) := by
  set v1 := step m 2 v
  set vm1 := (step m 2)^[m-2] v1
  set vm := step m 2 vm1
  have hv1 : v1.1 = v.1 + (if v.2.1 = -1 then 0 else 1) ∧ v1.2.1 = v.2.1 ∧ v1.2.2 = v.2.2 + (if v.2.1 = -1 then 1 else 0) := by
    unfold v1 step bump direction; aesop
  have hvm1 : vm1.1 = v1.1 ∧ vm1.2.1 = v1.2.1 + (if v1.1 = -1 then -2 else 0) := by
    apply step_mid_phase m hm3 v1 (by
    convert fiber_step m 2 v using 1; aesop)
  have hvm : vm.1 = vm1.1 + 1 ∧ vm.2.1 = vm1.2.1 := by
    have hvm_fiber : fiber m vm1 = -1 := by
      have hv1_fiber : fiber m v1 = 1 := by
        convert fiber_step m 2 v using 1; aesop
      have hv1_fiber_step : fiber m vm1 = fiber m v1 + (m - 2) := by
        have hv1_fiber_step : ∀ k : ℕ, fiber m ((step m 2)^[k] v1) = fiber m v1 + k := by
          exact fun k ↦ iterate_fiber m 2 v1 k
        convert hv1_fiber_step ( m - 2 ) using 1; rw [ Nat.cast_sub ( by linarith ) ]; norm_num
      simp_all +decide [ fiber ];
      norm_num
    have hvm_dir : direction m 2 vm1 = 0 := by
      unfold direction; simp +decide [ hvm_fiber ];
      rcases m with ( _ | _ | m ) <;> norm_cast at *;
      simp +decide [ ZMod ]
    have hvm_step : vm = bump m vm1 (direction m 2 vm1) := by
      rfl
    simp [hvm_step, hvm_dir, bump]
  rcases m with ( _ | _ | m ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
  simp +zetaDelta at *;
  simp_all +decide [ Function.iterate_succ_apply', F ];
  split_ifs at * <;> simp_all +decide [ Function.iterate_succ_apply' ];
  all_goals erw [ Function.iterate_succ_apply' ] at *; simp_all +decide [ Function.iterate_succ_apply' ];
  · ring
  · ring
  · norm_num at *
  · grind +ring
  · ring

/-- F iterates through the row (adding 2 to i) for k < m steps when j ≠ -1. -/
lemma F_iterate_row_ne_neg_one (hm : Odd m) (y : ZMod m) (hy : y ≠ -1) (k : ℕ) (hk : k < m) :
    (F m)^[k] (0, y) = ((2 * k : ZMod m), y) := by
  induction' k with k ih;
  · norm_num +zetaDelta at *
  · rw [ Function.iterate_succ_apply', ih ( Nat.lt_of_succ_lt hk ) ]; simp +decide [ F, Nat.cast_add ]; ring;
    have h_contra : (2 * k + 2 : ZMod m) = 0 → k + 1 = 0 := by
      intro h
      have h_div : (m : ℕ) ∣ (2 * (k + 1)) := by
        simpa [ ← ZMod.natCast_eq_zero_iff ] using by linear_combination' h
      exact Nat.eq_zero_of_dvd_of_lt ( Nat.Coprime.dvd_of_dvd_mul_left ( by obtain ⟨ c, rfl ⟩ := hm; aesop ) h_div ) hk
    grind +ring

/-- F iterates through the row (adding 1 to i) for k < m steps when j = -1. -/
lemma F_iterate_row_neg_one (hm : Odd m) (k : ℕ) (hk : k < m) :
    (F m)^[k] (0, -1) = ((k : ZMod m), -1) := by
  induction k <;> simp_all +decide [ Function.iterate_succ_apply' ];
  rename_i n ih;
  rw [ ih ( Nat.lt_of_succ_lt hk ), F ];
  norm_num [ eq_neg_iff_add_eq_zero ];
  split_ifs <;> norm_num;
  norm_cast at *;
  rw [ ZMod.natCast_eq_zero_iff ] at *; exact absurd ‹_› ( Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) hk )

/-- m iterations of F starting from (0, y) result in (0, y-2). -/
lemma F_pow_m_apply (hm : Odd m) (y : ZMod m) :
    (F m)^[m] (0, y) = (0, y - 2) := by
  have h_split : (F m)^[m] (0, y) = (F m) ( (F m)^[m-1] (0, y) ) := by
    cases m <;> simp_all +decide [ Function.iterate_succ_apply' ]
  by_cases hy_neg_one : y = -1;
  · have h_apply_iterate_neg_one : (F m)^[m - 1] (0, y) = (-1, -1) := by
      have h_apply_iterate_neg_one : (F m)^[m - 1] (0, -1) = ((m - 1 : ZMod m), -1) := by
        convert F_iterate_row_neg_one m hm ( m - 1 ) ( Nat.sub_lt ( NeZero.pos m ) zero_lt_one ) using 1; norm_num [ Nat.cast_sub ( NeZero.pos m ) ];
        norm_num [ Nat.cast_pred ( NeZero.pos m ) ]
      aesop
    unfold F at *; aesop
  · have h_row : (F m)^[m-1] (0, y) = ((2 * (m - 1) : ZMod m), y) := by
      convert F_iterate_row_ne_neg_one m hm y hy_neg_one ( m - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero <| NeZero.ne m ) zero_lt_one ) using 1; norm_num [ Nat.cast_sub <| show 1 ≤ m from Nat.pos_of_ne_zero <| NeZero.ne m ]
    cases m <;> simp_all +decide [ two_mul, sub_add_eq_sub_sub ];
    unfold F; aesop

/-- k*m iterations of F starting from (0, y) result in (0, y - 2k). -/
lemma F_iterate_mul_m_apply (hm : Odd m) (k : ℕ) (y : ZMod m) :
    (F m)^[k * m] (0, y) = (0, y - 2 * k) := by
  induction' k with k ih generalizing y;
  · norm_num
  · rw [ Nat.succ_mul, add_comm, Function.iterate_add_apply, ih ];
    convert F_pow_m_apply m hm ( y - 2 * k ) using 1; push_cast; ring

/-- The minimal period of F starting at (0, y) is m*m. -/
lemma F_minimalPeriod_zero_fiber (hm : Odd m) (y : ZMod m) :
    Function.minimalPeriod (F m) (0, y) = m * m := by
  have h_iter : (F m)^[m * m] (0, y) = (0, y) := by
    rw [ F_iterate_mul_m_apply ]; norm_num [ mul_comm ];
    exact hm
  have h_min_period : ∀ d, 0 < d → d < m * m → (F m)^[d] (0, y) ≠ (0, y) := by
    intro d hd_pos hd_lt
    by_contra h_contra
    obtain ⟨q, r, hr⟩ : ∃ q r, d = q * m + r ∧ 0 ≤ r ∧ r < m := by
      exact ⟨ d / m, d % m, by rw [ Nat.div_add_mod' ], Nat.zero_le _, Nat.mod_lt _ <| NeZero.pos m ⟩
    have h_fr : (F m)^[r] (0, y - 2 * q) = (0, y) := by
      have h_fr : (F m)^[q * m] (0, y) = (0, y - 2 * q) := by
        exact F_iterate_mul_m_apply m hm q y
      generalize_proofs at *; (
      rw [ ← h_fr, ← Function.iterate_add_apply, add_comm, ← hr.1, h_contra ])
    have h_r_zero : r = 0 := by
      by_cases hy : y - 2 * q = -1 <;> simp_all +decide [ F_iterate_row_ne_neg_one, F_iterate_row_neg_one ];
      · rw [ ZMod.natCast_eq_zero_iff ] at *; exact Nat.eq_zero_of_dvd_of_lt h_fr.1 hr.2
      · have h_r_zero : r < m → 2 * r ≡ 0 [MOD m] → r = 0 := by
          intro hr_lt hr_mod
          have h_r_zero : m ∣ 2 * r := by
            exact Nat.dvd_of_mod_eq_zero hr_mod
          generalize_proofs at *; (
          exact Nat.eq_zero_of_dvd_of_lt ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime m 2 from hm.elim fun k hk => by aesop ) h_r_zero ) hr_lt |> fun h => by aesop;)
        generalize_proofs at *; (
        exact h_r_zero hr.2 ( by simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_fr.1 ) ▸ rfl;)
    have h_q_zero : q = 0 := by
      simp_all +decide [ ZMod.natCast_eq_zero_iff ];
      norm_cast at h_fr;
      rw [ ZMod.natCast_eq_zero_iff ] at h_fr; exact Nat.eq_zero_of_dvd_of_lt ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime m 2 from by rcases hm with ⟨ k, rfl ⟩; norm_num ) h_fr ) hd_lt
    have h_d_zero : d = 0 := by
      aesop
    exact hd_pos.ne' h_d_zero
  rw [ Function.minimalPeriod ];
  split_ifs with h <;> simp_all +decide [ Function.IsPeriodicPt ];
  · rw [ Nat.find_eq_iff ]; aesop
  · exact False.elim <| h ⟨ m * m, by nlinarith [ NeZero.pos m ], h_iter ⟩

/-- Projecting k*m steps to (i,j) coordinates equals k steps of F. -/
lemma step_iterate_m_mul_project (hm : Odd m) (hm3 : 3 ≤ m) (k : ℕ) (v : Vertex m) (hv : fiber m v = 0) :
    let v' := (step m 2)^[k * m] v
    (v'.1, v'.2.1) = (F m)^[k] (v.1, v.2.1) := by
  induction' k with k ih generalizing v;
  · norm_num +zetaDelta at *
  · have h_step : let v' := (step m 2)^[k * m] v;
      let v'' := (step m 2)^[m] v';
      (v''.1, v''.2.1) = F m (v'.1, v'.2.1) := by
        apply step_pow_m_eq_F m hm hm3;
        have h_fiber : ∀ k : ℕ, fiber m ((step m 2)^[k] v) = fiber m v + k := by
          exact fun k ↦ iterate_fiber m 2 v k
        aesop
    simp_all +decide [ add_mul, Function.iterate_add_apply ];
    rw [ ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply ];
    erw [ h_step, Function.iterate_succ_apply' ]

/-- Every point in the F-space has minimal period m². -/
lemma F_minimalPeriod_univ (hm : Odd m) (p : ZMod m × ZMod m) :
    Function.minimalPeriod (F m) p = m * m := by
  have h_minimal_period_zero : ∀ y : ZMod m, Function.minimalPeriod (F m) (0, y) = m * m := by
    exact fun y ↦ F_minimalPeriod_zero_fiber m hm y
  have h_orbit_eq : ∃ y : ZMod m, ∃ n : ℕ, (F m)^[n] (0, y) = p := by
    have h_F_iterate : ∀ y : ZMod m, y ≠ -1 → ∀ k : ℕ, k < m → (F m)^[k] (0, y) = ((2 * k : ZMod m), y) := by
      exact fun y a k a_1 ↦ F_iterate_row_ne_neg_one m hm y a k a_1
    by_cases hy : p.2 = -1;
    · have h_F_iterate_neg_one : ∀ k : ℕ, k < m → (F m)^[k] (0, -1) = ((k : ZMod m), -1) := by
        exact fun k a ↦ F_iterate_row_neg_one m hm k a
      use -1, p.1.val;
      convert h_F_iterate_neg_one p.1.val ( ZMod.val_lt p.1 ) using 1; aesop
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, k < m ∧ 2 * k ≡ p.1.val [ZMOD m] := by
        obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * k ≡ p.1.val [ZMOD m] := by
          obtain ⟨inv2, hinv2⟩ : ∃ inv2 : ℤ, 2 * inv2 ≡ 1 [ZMOD m] := by
            exact ⟨ ( m + 1 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hm ) ) ]; norm_num [ Int.ModEq ] ⟩
          exact ⟨ inv2 * p.1.val, by simpa [ mul_assoc ] using hinv2.mul_right _ ⟩
        exact ⟨ Int.toNat ( k % m ), by linarith [ Int.emod_lt_of_pos k ( Nat.cast_pos.mpr <| NeZero.pos m ), Int.toNat_of_nonneg <| Int.emod_nonneg k <| Nat.cast_ne_zero.mpr <| NeZero.ne m ], by simpa [ Int.ModEq, Int.mul_emod, Int.toNat_of_nonneg <| Int.emod_nonneg k <| Nat.cast_ne_zero.mpr <| NeZero.ne m ] using hk ⟩
      use p.2, k;
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ]
  obtain ⟨ y, n, rfl ⟩ := h_orbit_eq; rw [ ← h_minimal_period_zero y ];
  rw [ Function.minimalPeriod, Function.minimalPeriod ];
  split_ifs <;> simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt ];
  · congr! 2;
    constructor <;> intro h <;> have := h.2 <;> simp_all +decide [ ← Function.iterate_add_apply ];
    · have h_inj : Function.Injective (F m) := by
        intro x y hxy; simp_all +decide [ F ];
        grind
      exact Function.iterate_cancel_of_add h_inj this
    · rw [ add_comm, Function.iterate_add_apply, this ]
  · rename_i h₁ h₂; specialize h_minimal_period_zero y; simp_all +decide [ Function.minimalPeriod ]
  · rename_i h₁ h₂;
    contrapose! h₁;
    obtain ⟨ k, hk ⟩ := h₂;
    use k;
    simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt ];
    rw [ ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hk.2.eq ]

/-- The minimal period of step 2 on a vertex with fiber 0 is m³. -/
lemma cycle2_hamiltonian_fiber_zero (hm : Odd m) (hm3 : 3 ≤ m) (v : Vertex m) (hv : fiber m v = 0) :
    Function.minimalPeriod (step m 2) v = m ^ 3 := by
  set P := Function.minimalPeriod (step m 2) v
  have hP_div_m3 : P ∣ m ^ 3 := by
    refine' Function.IsPeriodicPt.minimalPeriod_dvd _;
    have h_F_m : (F m)^[m ^ 2] (v.1, v.2.1) = (v.1, v.2.1) := by
      have hF_periodic : Function.minimalPeriod (F m) (v.1, v.2.1) = m ^ 2 := by
        convert F_minimalPeriod_univ m hm ( v.1, v.2.1 ) using 1; ring!
      generalize_proofs at *; (
      exact hF_periodic ▸ Function.isPeriodicPt_minimalPeriod _ _)
    generalize_proofs at *; (
    have h_fiber : fiber m ((step m 2)^[m^3] v) = fiber m v := by
      rw [ iterate_fiber ]; aesop
    generalize_proofs at *; (
    have h_xy : ((step m 2)^[m^3] v).1 = v.1 ∧ ((step m 2)^[m^3] v).2.1 = v.2.1 := by
      have := step_iterate_m_mul_project m hm hm3 ( m ^ 2 ) v hv; simp_all +decide [ pow_succ, mul_assoc ]
    generalize_proofs at *; (
    have h_z : ((step m 2)^[m^3] v).2.2 = v.2.2 := by
      have h_z : ((step m 2)^[m^3] v).1 + ((step m 2)^[m^3] v).2.1 + ((step m 2)^[m^3] v).2.2 = v.1 + v.2.1 + v.2.2 := by
        exact h_fiber
      generalize_proofs at *; (
      aesop)
    generalize_proofs at *; (
    exact Prod.ext h_xy.1 ( Prod.ext h_xy.2 h_z )))))
  have hP_ge_m3 : m ^ 3 ∣ P := by
    have hP_div_m : m ∣ P := by
      have hP_fiber : (fiber m) ((step m 2)^[P] v) = (fiber m) v + P := by
        exact iterate_fiber m 2 v P
      generalize_proofs at *; (
      rw [ ← ZMod.natCast_eq_zero_iff ]; aesop;)
    obtain ⟨k, hk⟩ : ∃ k, P = k * m := by
      exact exists_eq_mul_left_of_dvd hP_div_m
    have hF_k : (F m)^[k] (v.1, v.2.1) = (v.1, v.2.1) := by
      have hF_k : (step m 2)^[k * m] v = v := by
        exact hk ▸ Function.isPeriodicPt_minimalPeriod _ _
      generalize_proofs at *; (
      convert congr_arg ( fun x : Vertex m => ( x.1, x.2.1 ) ) hF_k using 1
      generalize_proofs at *; (
      exact Eq.symm (step_iterate_m_mul_project m hm hm3 k v hv)))
    have hk_div_m2 : m ^ 2 ∣ k := by
      have hk_div_m2 : Function.minimalPeriod (F m) (v.1, v.2.1) = m ^ 2 := by
        convert F_minimalPeriod_univ m hm ( v.1, v.2.1 ) using 1; ring!
      exact hk_div_m2 ▸ Function.IsPeriodicPt.minimalPeriod_dvd ( by aesop )
    exact ⟨k / m ^ 2, by
      nlinarith [ Nat.div_mul_cancel hk_div_m2 ]⟩
  exact Nat.dvd_antisymm hP_div_m3 hP_ge_m3 ▸ rfl

end -- noncomputable section

/-- Cycle 2 is Hamiltonian for odd m ≥ 3. -/
theorem cycle2_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 2) := by
  have h_min_period_fiber_zero (v : Vertex m) (hv : fiber m v = 0) : Function.minimalPeriod (step m 2) v = m ^ 3 := by
    exact cycle2_hamiltonian_fiber_zero m hm hm3 v hv
  have h_orbit_size_fiber_zero (v : Vertex m) (hv : fiber m v = 0) : Finset.card (Finset.image (fun k => (step m 2)^[k] v) (Finset.range (m ^ 3))) = m ^ 3 := by
    have h_distinct : ∀ k1 k2 : ℕ, k1 < k2 → k2 < m ^ 3 → (step m 2)^[k1] v ≠ (step m 2)^[k2] v := by
      intros k1 k2 hk1k2 hk2m3 h_eq
      have h_period : (step m 2)^[k2 - k1] v = v := by
        have h_period : (step m 2)^[k2] v = (step m 2)^[k1] ((step m 2)^[k2 - k1] v) := by
          rw [ ← Function.iterate_add_apply, Nat.add_sub_of_le hk1k2.le ]
        generalize_proofs at *; (
        exact Function.Injective.iterate (step_injective m 2) k1 <| by aesop;)
      have := h_min_period_fiber_zero v hv ▸ Function.IsPeriodicPt.minimalPeriod_dvd ( show Function.IsPeriodicPt ( step m 2 ) ( k2 - k1 ) v from by simpa [ Function.IsPeriodicPt, Function.IsFixedPt ] using h_period ); simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      rw [ Nat.mod_eq_of_lt ] at this <;> omega
    rw [ Finset.card_image_of_injOn fun k1 hk1 k2 hk2 h => le_antisymm ( le_of_not_gt fun h' => h_distinct _ _ h' ( by linarith [ Finset.mem_range.mp hk1, Finset.mem_range.mp hk2 ] ) h.symm ) ( le_of_not_gt fun h' => h_distinct _ _ h' ( by linarith [ Finset.mem_range.mp hk1, Finset.mem_range.mp hk2 ] ) h ), Finset.card_range ]
  have h_orbit_eq_univ_fiber_zero : ∀ v : Vertex m, fiber m v = 0 → Finset.image (fun k => (step m 2)^[k] v) (Finset.range (m ^ 3)) = Finset.univ := by
    intros v hv; specialize h_orbit_size_fiber_zero v hv; exact Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) ( by rw [ h_orbit_size_fiber_zero, Finset.card_univ ]; norm_num [ pow_succ' ] )
  have h_all_in_orbit (v : Vertex m) : ∃ k < m ^ 3, (step m 2)^[k] (0, 0, 0) = v := by
    replace h_orbit_eq_univ_fiber_zero := Finset.ext_iff.mp ( h_orbit_eq_univ_fiber_zero ( 0, 0, 0 ) ( by simp +decide [ fiber ] ) ) v; aesop
  intro v
  obtain ⟨k, hk_lt, hk_eq⟩ := h_all_in_orbit v
  have h_min_period_eq : Function.minimalPeriod (step m 2) v = Function.minimalPeriod (step m 2) (0, 0, 0) := by
    rw [ ← hk_eq, Function.minimalPeriod_apply_iterate ];
    use m ^ 3;
    exact ⟨ pow_pos ( NeZero.pos m ) 3, by rw [ Function.IsPeriodicPt, Function.IsFixedPt ]; exact h_min_period_fiber_zero ( 0, 0, 0 ) ( by simp +decide [ fiber ] ) ▸ Function.isPeriodicPt_minimalPeriod _ _ ⟩
  exact h_min_period_eq.trans ( h_min_period_fiber_zero _ <| by simp +decide [ fiber ] )

end ClaudesCycles
