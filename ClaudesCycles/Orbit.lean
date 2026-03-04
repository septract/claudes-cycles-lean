/-
# Orbit Infrastructure for Claude's Cycles

Shared machinery for proving Hamiltonicity: fiber iteration lemmas,
the "advance by 2" argument, and the Hamiltonicity criterion.
-/
import ClaudesCycles.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

omit [NeZero m] in
/-- After n steps, the fiber advances by n. -/
theorem iterate_fiber (c : Fin 3) (v : Vertex m) (n : ℕ) :
    fiber m ((step m c)^[n] v) = fiber m v + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fiber_step, ih]
    push_cast
    ring

omit [NeZero m] in
/-- After m steps, the fiber returns to its original value. -/
theorem iterate_m_fiber (c : Fin 3) (v : Vertex m) :
    fiber m ((step m c)^[m] v) = fiber m v := by
  rw [iterate_fiber]
  simp

omit [NeZero m] in
/-- Two orbit points with the same fiber differ by a multiple of m steps. -/
theorem fiber_eq_of_iterate (c : Fin 3) (v : Vertex m) {a b : ℕ}
    (h : fiber m ((step m c)^[a] v) = fiber m ((step m c)^[b] v)) :
    (a : ZMod m) = (b : ZMod m) := by
  rw [iterate_fiber, iterate_fiber] at h
  exact add_left_cancel h

/-- The orbit is Hamiltonian iff it has period m³. Since step c is a bijection,
  this means the permutation has a single cycle. We state it as:
  step c has minimal period m³ at every vertex. -/
@[tcb] def IsHamiltonian (f : Vertex m → Vertex m) : Prop :=
  ∀ v, Function.minimalPeriod f v = m ^ 3

/-- A Hamiltonian function visits all vertices from any starting point. -/
theorem IsHamiltonian.surj_orbit {f : Vertex m → Vertex m} (hf : IsHamiltonian m f)
    (_hbij : Function.Bijective f) (v : Vertex m) :
    ∀ w, ∃ n, n < m ^ 3 ∧ f^[n] v = w := by
  intro w
  -- The map n ↦ f^[n] v on {0, ..., m^3 - 1} is injective
  -- (from minimalPeriod = m^3) and maps into Vertex m of size m^3,
  -- so it's surjective.
  have hcard : Fintype.card (Vertex m) = m ^ 3 := by
    simp [Vertex, Fintype.card_prod, ZMod.card]; ring
  -- Define g : Fin (m^3) → Vertex m by g(n) = f^[n] v
  have hper := hf v  -- minimalPeriod f v = m ^ 3
  -- g is injective by iterate_injOn_Iio_minimalPeriod
  have hinj : Function.Injective (fun n : Fin (m ^ 3) => f^[n.val] v) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    simp only at heq
    have := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (hper ▸ ha) (hper ▸ hb)).mp heq
    exact Fin.ext this
  -- Fin (m^3) and Vertex m have the same cardinality
  have hcard_eq : Fintype.card (Fin (m ^ 3)) = Fintype.card (Vertex m) := by
    simp [Fintype.card_fin, hcard]
  -- Injective on same-size finite type → surjective
  have hsurj := (Finite.injective_iff_surjective_of_equiv
    (Fintype.equivOfCardEq hcard_eq)).mp hinj
  obtain ⟨n, rfl⟩ := hsurj w
  exact ⟨n.val, n.isLt, rfl⟩

omit [NeZero m] in
/-- Key arithmetic lemma: in ZMod m with m odd, adding 2 generates all of ZMod m.
  More precisely, the additive order of 2 in ZMod m equals m when m is odd. -/
theorem ZMod.addOrderOf_two (hm : Odd m) (hm1 : 1 < m) :
    addOrderOf (2 : ZMod m) = m := by
  rw [addOrderOf_eq_iff (by omega : 0 < m)]
  constructor
  · -- m • 2 = 0 in ZMod m
    rw [nsmul_eq_mul, mul_comm, ← Nat.cast_ofNat, ← Nat.cast_mul,
        ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left m 2
  · -- For 0 < k < m, k • 2 ≠ 0
    intro k hkm hkpos
    rw [nsmul_eq_mul, mul_comm, Ne, ← sub_eq_zero, sub_zero]
    -- Goal: ¬ ((2 : ZMod m) * ↑k = 0)
    intro heq
    rw [show (2 : ZMod m) * (k : ZMod m) = ((2 * k : ℕ) : ZMod m) from by push_cast; ring,
        ZMod.natCast_eq_zero_iff] at heq
    -- m | 2 * k, and since gcd(2,m) = 1 (m is odd), m | k.
    have hgcd : Nat.Coprime m 2 := hm.coprime_two_left.symm
    have hdvd := hgcd.dvd_of_dvd_mul_left heq
    exact absurd (Nat.le_of_dvd hkpos hdvd) (not_le.mpr hkm)

/-- The orbit of repeatedly adding 2 covers all of ZMod m when m is odd. -/
theorem ZMod.orbit_add_two_surj (hm : Odd m) (_hm1 : 1 < m) (x : ZMod m) :
    ∀ y : ZMod m, ∃ n : ℕ, n < m ∧ x + 2 * (n : ZMod m) = y := by
  intro y
  -- Since gcd(2,m) = 1, 2 is invertible in ZMod m.
  have hcop : Nat.Coprime 2 m := hm.coprime_two_left
  set u := ZMod.unitOfCoprime 2 hcop
  -- Let z = (y - x) / 2, take n = ZMod.val z
  set z := ↑u⁻¹ * (y - x) with hz_def
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  have h2 : (2 : ZMod m) * z = y - x := by
    rw [hz_def, ← mul_assoc, show (2 : ZMod m) = ↑u from rfl]
    simp
  have hzv : (z.val : ZMod m) = z := ZMod.natCast_zmod_val z
  rw [hzv, h2, add_sub_cancel]

/-! ## Arithmetic helpers for ZMod -/

omit [NeZero m] in
/-- A nonzero natural number less than m is nonzero in ZMod m. -/
theorem natCast_ne_zero_of_lt (n : ℕ) (hn0 : 0 < n) (hnm : n < m) :
    (n : ZMod m) ≠ 0 := by
  intro h; rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hn0 h) (not_le.mpr hnm)

omit [NeZero m] in
/-- 0 ≠ -1 in ZMod m when m ≥ 2. -/
theorem zero_ne_neg_one (hm : 2 ≤ m) : (0 : ZMod m) ≠ -1 := by
  intro h
  have h1 : (1 : ZMod m) = 0 := by
    have : (0 : ZMod m) + 1 = (-1 : ZMod m) + 1 := congr_arg (· + 1) h
    simpa using this
  have h2 : ((1 : ℕ) : ZMod m) = 0 := by exact_mod_cast h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)

omit [NeZero m] in
/-- -1 ≠ 0 in ZMod m when m ≥ 2. -/
theorem neg_one_ne_zero (hm : 2 ≤ m) : (-1 : ZMod m) ≠ 0 :=
  Ne.symm (zero_ne_neg_one m hm)

omit [NeZero m] in
/-- Cast of (m - k) to ZMod m equals -k when k ≤ m. -/
theorem natCast_sub_eq_neg (k : ℕ) (hk : k ≤ m) :
    ((m - k : ℕ) : ZMod m) = -(k : ZMod m) :=
  eq_neg_of_add_eq_zero_left (by
    have h : m - k + k = m := Nat.sub_add_cancel hk
    have : ((m - k + k : ℕ) : ZMod m) = 0 := by rw [h]; exact ZMod.natCast_self m
    push_cast at this; exact this)

end ClaudesCycles
