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

omit [NeZero m] in
/-- At s = 0: cycle 1 always bumps j. -/
theorem direction_one_s0 (v : Vertex m)
    (hs : fiber m v = 0) :
    direction m 1 v = 1 := by
  simp only [direction, hs, ↓reduceIte]

omit [NeZero m] in
/-- At 0 < s < m-1: cycle 1 always bumps i. -/
theorem direction_one_mid (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) :
    direction m 1 v = 0 := by
  simp only [direction, hs0, hsm, ↓reduceIte]

omit [NeZero m] in
/-- At s = -1, i ≠ 0: cycle 1 bumps k. -/
theorem direction_one_sm_i_ne (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 ≠ 0) :
    direction m 1 v = 2 := by
  simp only [direction]; split_ifs <;> simp_all

omit [NeZero m] in
/-- At s = -1, i = 0: cycle 1 bumps j. -/
theorem direction_one_sm_i0 (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v = -1) (hi : v.1 = 0) :
    direction m 1 v = 1 := by
  simp only [direction]; split_ifs <;> simp_all

/-! ## Step lemmas for cycle 1 -/

omit [NeZero m] in
/-- At s = 0, step 1 bumps j: (i, j, k) → (i, j+1, k). -/
theorem step1_c1 (v : Vertex m) (hs : fiber m v = 0) :
    step m 1 v = (v.1, v.2.1 + 1, v.2.2) := by
  simp only [step, direction_one_s0 m v hs, bump]

omit [NeZero m] in
/-- At mid fiber, step 1 bumps i: (i, j, k) → (i+1, j, k). -/
theorem step_mid_c1 (v : Vertex m)
    (hs0 : fiber m v ≠ 0) (hsm : fiber m v ≠ -1) :
    step m 1 v = (v.1 + 1, v.2.1, v.2.2) := by
  simp only [step, direction_one_mid m v hs0 hsm, bump]

omit [NeZero m] in
/-- After n mid-fiber steps for cycle 1 (from fiber=1), the vertex is
    (i+n, j, k) with fiber 1+n. -/
theorem iterate_mid_c1 (v : Vertex m) (hm3 : 3 ≤ m)
    (hfib : fiber m v = 1) (n : ℕ) (hn : n ≤ m - 2) :
    (step m 1)^[n] v = (v.1 + n, v.2.1, v.2.2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k < m - 2 := Nat.lt_of_succ_le hn
    rw [Function.iterate_succ_apply', ih (le_of_lt hk)]
    have hfib_k : fiber m (v.1 + ↑k, v.2.1, v.2.2) = 1 + (k : ZMod m) := by
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
    have hs0' : fiber m (v.1 + ↑k, v.2.1, v.2.2) ≠ 0 := by rw [hfib_k]; exact hne0
    have hsm' : fiber m (v.1 + ↑k, v.2.1, v.2.2) ≠ -1 := by rw [hfib_k]; exact hnem
    rw [step_mid_c1 m _ hs0' hsm']
    simp only [Prod.mk.injEq, true_and, and_true]
    push_cast; ring

/-! ## m-step formulas for cycle 1

From s=0 vertex (i, j, k):
  Step 1 (s=0): bump j → (i, j+1, k)
  Steps 2..m-1 (mid): bump i each → (i+(m-2), j+1, k)
  Step m (s=-1):
    If i+(m-2) ≠ 0 (i.e., i ≠ 2): bump k → (i-2, j+1, k+1)
    If i+(m-2) = 0 (i.e., i = 2): bump j → (0, j+2, k)
-/

omit [NeZero m] in
/-- Full m-step for cycle 1, generic case. From (i, j, k) with s=0, i-2 ≠ 0:
    after m steps → (i+(m-2), j+1, k+1). -/
theorem m_step_c1_ne (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 + ↑(m - 2 : ℕ) ≠ 0) :
    (step m 1)^[m] v = (v.1 + ↑(m - 2 : ℕ), v.2.1 + 1, v.2.2 + 1) := by
  have hiter : (step m 1)^[m] v = (step m 1)^[1 + (m - 2) + 1] v := by congr 2; omega
  rw [hiter, Function.iterate_add, Function.iterate_add, Function.comp_apply,
      Function.comp_apply]
  rw [Function.iterate_one, step1_c1 m v hs]
  have hfib1 : fiber m (v.1, v.2.1 + 1, v.2.2) = 1 := by
    have : fiber m (v.1, v.2.1 + 1, v.2.2) = fiber m v + 1 := by simp [fiber]; ring
    rw [this, hs, zero_add]
  rw [iterate_mid_c1 m (v.1, v.2.1 + 1, v.2.2) hm3 hfib1 (m - 2) le_rfl]
  -- After mid steps: (i+(m-2), j+1, k) with fiber = -1
  have hfib_last : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) = -1 := by
    have : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) = fiber m v + (↑(m - 2) + 1) := by
      simp [fiber]; ring
    rw [this, hs, zero_add, natCast_sub_eq_neg m 2 (by omega)]; ring
  have hne0 : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) ≠ 0 := by
    rw [hfib_last]; exact neg_one_ne_zero m (by omega)
  rw [step, direction_one_sm_i_ne m _ hne0 hfib_last hi, bump]

omit [NeZero m] in
/-- Full m-step for cycle 1, special case. From (i, j, k) with s=0, i-2 = 0:
    after m steps → (0, j+2, k). -/
theorem m_step_c1_eq (v : Vertex m) (hm3 : 3 ≤ m)
    (hs : fiber m v = 0) (hi : v.1 + ↑(m - 2 : ℕ) = 0) :
    (step m 1)^[m] v = (0, v.2.1 + 2, v.2.2) := by
  have hiter : (step m 1)^[m] v = (step m 1)^[1 + (m - 2) + 1] v := by congr 2; omega
  rw [hiter, Function.iterate_add, Function.iterate_add, Function.comp_apply,
      Function.comp_apply]
  rw [Function.iterate_one, step1_c1 m v hs]
  have hfib1 : fiber m (v.1, v.2.1 + 1, v.2.2) = 1 := by
    have : fiber m (v.1, v.2.1 + 1, v.2.2) = fiber m v + 1 := by simp [fiber]; ring
    rw [this, hs, zero_add]
  rw [iterate_mid_c1 m (v.1, v.2.1 + 1, v.2.2) hm3 hfib1 (m - 2) le_rfl]
  have hfib_last : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) = -1 := by
    have : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) = fiber m v + (↑(m - 2) + 1) := by
      simp [fiber]; ring
    rw [this, hs, zero_add, natCast_sub_eq_neg m 2 (by omega)]; ring
  have hne0 : fiber m (v.1 + ↑(m - 2), v.2.1 + 1, v.2.2) ≠ 0 := by
    rw [hfib_last]; exact neg_one_ne_zero m (by omega)
  rw [step, direction_one_sm_i0 m _ hne0 hfib_last hi, bump]
  simp only [Prod.mk.injEq, true_and, and_true]
  constructor
  · exact hi
  · ring

/-! ## Orbit analysis for cycle 1

Key formula: after k generic m-step rounds from (0, j, -j),
  (step m 1)^[m*k] (0, j, -j) = (-2*k, j+k, k-j)

After m rounds (one special at the end):
  (step m 1)^[m*m] (0, j, -j) = (0, j+1, -(j+1))

This proves the m²-step map shifts j by 1, giving period m on j,
hence total period m³. -/

omit [NeZero m] in
/-- Generic m-step rounds for cycle 1. Starting from (0, j, -j) with s=0,
    after k generic rounds (0 ≤ k ≤ m-1):
    (step m 1)^[m*k] (0, j, -j) = (-2*k, j+k, k-j). -/
theorem m_step_rounds_c1 (j : ZMod m) (hm : Odd m) (hm3 : 3 ≤ m)
    (k : ℕ) (hk : k ≤ m - 1) :
    (step m 1)^[m * k] ((0 : ZMod m), j, -j) =
      ((-2 * ↑k : ZMod m), j + ↑k, ↑k - j) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ m - 1 := by omega
    rw [show m * (n + 1) = m + m * n from by ring,
        Function.iterate_add, Function.comp_apply, ih hn]
    -- Need to show the vertex (-2*n, j+n, n-j) has fiber 0
    have hfib : fiber m ((-2 * ↑n : ZMod m), j + ↑n, ↑n - j) = 0 := by
      simp [fiber]; ring
    -- Need -2*n + (m-2) ≠ 0, i.e., -2*(n+1) ≠ 0 in ZMod m
    have hine : (-2 * ↑n : ZMod m) + ↑(m - 2 : ℕ) ≠ 0 := by
      intro h
      have h1 : (↑(2 * (n + 1) : ℕ) : ZMod m) = 0 := by
        have key : (↑(2 * (n + 1) : ℕ) : ZMod m) =
            -(-2 * (↑n : ZMod m) + ↑(m - 2 : ℕ)) := by
          rw [natCast_sub_eq_neg m 2 (by omega)]; push_cast; ring
        rw [key, h, neg_zero]
      rw [ZMod.natCast_eq_zero_iff] at h1
      exact absurd (Nat.le_of_dvd (by omega)
        (hm.coprime_two_left.symm.dvd_of_dvd_mul_left h1)) (by omega)
    rw [m_step_c1_ne m _ hm3 hfib hine]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [natCast_sub_eq_neg m 2 (by omega)]; push_cast; ring
    · push_cast; ring
    · push_cast; ring

omit [NeZero m] in
/-- After m m-step rounds from (0, j, -j), the special step at the end
    gives (0, j+1, -(j+1)). This is the key orbit lemma. -/
theorem m_squared_step_c1 (j : ZMod m) (hm : Odd m) (hm3 : 3 ≤ m) :
    (step m 1)^[m * m] ((0 : ZMod m), j, -j) = (0, j + 1, -(j + 1)) := by
  -- Decompose: m*m = m + m*(m-1). iterate_add gives f^[m](f^[m*(m-1)] v),
  -- applying (m-1) generic rounds first, then one special round.
  have hmm : m * m = m + m * (m - 1) :=
    calc m * m = m * ((m - 1) + 1) := by congr 1; omega
         _ = m * (m - 1) + m * 1 := Nat.mul_add m (m - 1) 1
         _ = m * (m - 1) + m := by rw [mul_one]
         _ = m + m * (m - 1) := Nat.add_comm _ _
  rw [hmm,
      Function.iterate_add, Function.comp_apply,
      m_step_rounds_c1 m j hm hm3 (m - 1) le_rfl]
  -- Now at (-2*(m-1), j+(m-1), (m-1)-j) = (2, j-1, -1-j)
  have hfib : fiber m ((-2 * ↑(m - 1 : ℕ) : ZMod m), j + ↑(m - 1 : ℕ), ↑(m - 1 : ℕ) - j) = 0 := by
    simp [fiber]; ring
  -- i-coord is -2*(m-1) = -2m+2 = 2. So i+(m-2) = 2+(m-2) = m = 0. Special case!
  have hieq : (-2 * ↑(m - 1 : ℕ) : ZMod m) + ↑(m - 2 : ℕ) = 0 := by
    rw [natCast_sub_eq_neg m 1 (by omega), natCast_sub_eq_neg m 2 (by omega)]
    push_cast; ring
  rw [m_step_c1_eq m _ hm3 hfib hieq]
  simp only [Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  · rw [natCast_sub_eq_neg m 1 (by omega)]; push_cast; ring
  · rw [natCast_sub_eq_neg m 1 (by omega)]; push_cast; ring

/-! ## Orbit iteration lemmas -/

omit [NeZero m] in
/-- After q applications of the m²-step map from (0, j, -j):
    (step m 1)^[m²·q] (0, j, -j) = (0, j+q, -(j+q)). -/
theorem iterate_m_squared_c1 (j : ZMod m) (hm : Odd m) (hm3 : 3 ≤ m) (q : ℕ) :
    (step m 1)^[m * m * q] ((0 : ZMod m), j, -j) =
      (0, j + ↑q, -(j + ↑q)) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [show m * m * (n + 1) = m * m + m * m * n from by ring,
        Function.iterate_add, Function.comp_apply, ih]
    have h := m_squared_step_c1 m (j + ↑n) hm hm3
    convert h using 2 <;> push_cast <;> ring

omit [NeZero m] in
/-- Orbit from (0,0,0): after m*(m*q+r) steps (r ≤ m-1),
    the vertex is (-2r, q+r, r-q). -/
theorem orbit_formula_c1 (hm : Odd m) (hm3 : 3 ≤ m)
    (q : ℕ) (r : ℕ) (hr : r ≤ m - 1) :
    (step m 1)^[m * (m * q + r)] ((0 : ZMod m), 0, 0) =
      ((-2 * ↑r : ZMod m), (↑q : ZMod m) + ↑r, (↑r : ZMod m) - ↑q) := by
  rw [show m * (m * q + r) = m * r + m * m * q from by ring,
      Function.iterate_add, Function.comp_apply]
  have hbase : (step m 1)^[m * m * q] ((0 : ZMod m), 0, 0) =
      ((0 : ZMod m), (↑q : ZMod m), -(↑q : ZMod m)) := by
    have h := iterate_m_squared_c1 m 0 hm hm3 q
    simp only [neg_zero, zero_add] at h; exact h
  rw [hbase]
  exact m_step_rounds_c1 m (↑q : ZMod m) hm hm3 r hr

/-! ## Hamiltonicity of cycle 1

Strategy:
1. Show minimalPeriod (step m 1) (0,0,0) = m³.
2. From orbit_formula_c1: if f^[m*ℓ] (0,0,0) = (0,0,0), then
   writing ℓ = m*q + r, the formula gives r=0 and q=0 (mod m),
   so m² | ℓ and m³ | n.
3. Extend to all vertices via minimalPeriod_apply_iterate. -/

omit [NeZero m] in
/-- 2*a = 0 in ZMod m with m odd implies a = 0. -/
theorem two_mul_eq_zero_of_odd (hm : Odd m) (a : ZMod m)
    (h : 2 * a = 0) : a = 0 := by
  have hcop : Nat.Coprime 2 m := hm.coprime_two_left
  set u := ZMod.unitOfCoprime 2 hcop
  have h2u : (↑u : ZMod m) = 2 := rfl
  have : a = ↑u⁻¹ * (↑u * a) := by
    rw [← mul_assoc, show ↑u⁻¹ * ↑u = (1 : ZMod m) from by exact_mod_cast u.inv_mul, one_mul]
  rw [this, h2u, h, mul_zero]

/-- Cycle 1 is Hamiltonian for odd m ≥ 3. -/
theorem cycle1_hamiltonian (hm : Odd m) (hm3 : 3 ≤ m) :
    IsHamiltonian m (step m 1) := by
  set f := step m 1
  set v₀ : Vertex m := (0, 0, 0)
  have hcard : Fintype.card (Vertex m) = m ^ 3 := by
    simp [Vertex, Fintype.card_prod, ZMod.card]; ring
  have hper : ∀ x : Vertex m, x ∈ Function.periodicPts f :=
    (step_injective m 1).mem_periodicPts
  -- Step 1: minimalPeriod at v₀ = m³
  have h0 : Function.minimalPeriod f v₀ = m ^ 3 := by
    apply le_antisymm
    · exact hcard ▸ Function.minimalPeriod_le_card
    · -- Lower bound: m³ ≤ minimalPeriod
      have hp_pos : 0 < Function.minimalPeriod f v₀ :=
        Function.minimalPeriod_pos_of_mem_periodicPts (hper v₀)
      have hp_period : f^[Function.minimalPeriod f v₀] v₀ = v₀ :=
        Function.isPeriodicPt_minimalPeriod f v₀
      -- From fiber: m ∣ minimalPeriod
      have hm_dvd : m ∣ Function.minimalPeriod f v₀ := by
        have hfib := iterate_fiber m 1 v₀ (Function.minimalPeriod f v₀)
        rw [hp_period] at hfib
        have h0' : fiber m v₀ + 0 = fiber m v₀ + ↑(Function.minimalPeriod f v₀) := by
          rw [add_zero]; exact hfib
        have : (↑(Function.minimalPeriod f v₀) : ZMod m) = 0 :=
          (add_left_cancel h0').symm
        rwa [ZMod.natCast_eq_zero_iff] at this
      obtain ⟨ℓ, hℓ⟩ := hm_dvd
      have hℓ_pos : 0 < ℓ := by
        rcases Nat.eq_zero_or_pos ℓ with rfl | h
        · simp at hℓ; omega
        · exact h
      -- Euclidean division: ℓ = m * q + r
      have hr_lt : ℓ % m < m := Nat.mod_lt ℓ (by omega)
      have hℓ_eq : ℓ = m * (ℓ / m) + ℓ % m := (Nat.div_add_mod ℓ m).symm
      -- Apply orbit formula
      have hp_eq : Function.minimalPeriod f v₀ = m * (m * (ℓ / m) + ℓ % m) := by
        rw [hℓ]; congr 1
      have horbit_eq : f^[m * (m * (ℓ / m) + ℓ % m)] v₀ = v₀ := by
        rw [← hp_eq]; exact hp_period
      have horbit := orbit_formula_c1 m hm hm3 (ℓ / m) (ℓ % m) (by omega)
      rw [horbit_eq] at horbit
      -- horbit : (0, 0, 0) = (-2*r, q+r, r-q)
      have h_i : (-2 * (↑(ℓ % m) : ZMod m)) = 0 :=
        (Prod.mk.inj horbit.symm).1
      have h_j : (↑(ℓ / m) : ZMod m) + ↑(ℓ % m) = 0 :=
        (Prod.mk.inj (Prod.mk.inj horbit.symm).2).1
      -- From h_i: 2*r = 0, so r = 0 (m is odd)
      have hr0_zmod : (↑(ℓ % m) : ZMod m) = 0 := by
        apply two_mul_eq_zero_of_odd m hm
        have : 2 * (↑(ℓ % m) : ZMod m) = -(-2 * ↑(ℓ % m)) := by ring
        rw [this, h_i, neg_zero]
      have hr0 : ℓ % m = 0 := by
        rw [ZMod.natCast_eq_zero_iff] at hr0_zmod
        exact Nat.eq_zero_of_dvd_of_lt hr0_zmod hr_lt
      -- From h_j with r=0: q = 0 mod m
      have hq0_zmod : (↑(ℓ / m) : ZMod m) = 0 := by
        rw [hr0] at h_j; simpa using h_j
      rw [ZMod.natCast_eq_zero_iff] at hq0_zmod
      obtain ⟨s, hs⟩ := hq0_zmod
      -- minimalPeriod = m * (m * (m * s) + 0) = m³ * s ≥ m³
      rw [hp_eq, hr0, hs]
      change m ^ 3 ≤ m * (m * (m * s) + 0)
      rw [add_zero]
      have hs_pos : 0 < s := by
        rcases Nat.eq_zero_or_pos s with rfl | h
        · simp only [mul_zero] at hs
          rw [hs, hr0] at hℓ_eq; simp only [mul_zero, add_zero] at hℓ_eq; omega
        · exact h
      have : m * (m * (m * s)) = m ^ 3 * s := by ring
      rw [this]
      exact Nat.le_mul_of_pos_right _ hs_pos
  -- Step 2: extend to all vertices
  intro v
  have hsurj : ∀ w : Vertex m, ∃ n, f^[n] v₀ = w := by
    intro w
    have hinj : Function.Injective (fun n : Fin (m ^ 3) => f^[n.val] v₀) := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ heq
      simp only at heq
      have ha' : a < Function.minimalPeriod f v₀ := by rw [h0]; exact ha
      have hb' : b < Function.minimalPeriod f v₀ := by rw [h0]; exact hb
      exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        ha' hb').mp heq)
    have hcard_eq : Fintype.card (Fin (m ^ 3)) = Fintype.card (Vertex m) := by
      simp [Fintype.card_fin, hcard]
    have hsurj := (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hcard_eq)).mp hinj
    obtain ⟨n, rfl⟩ := hsurj w
    exact ⟨n.val, rfl⟩
  obtain ⟨n, rfl⟩ := hsurj v
  exact (Function.minimalPeriod_apply_iterate (hper v₀) n).trans h0

end ClaudesCycles
