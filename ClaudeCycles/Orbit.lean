/-
# Orbit Infrastructure for Claude's Cycles

Shared machinery for proving Hamiltonicity: fiber iteration lemmas,
the "advance by 2" argument, and the Hamiltonicity criterion.
-/
import ClaudeCycles.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace ClaudeCycles

variable (m : ℕ) [NeZero m]

/-- After n steps, the fiber advances by n. -/
theorem iterate_fiber (c : Fin 3) (v : Vertex m) (n : ℕ) :
    fiber m ((step m c)^[n] v) = fiber m v + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fiber_step, ih]
    push_cast
    ring

/-- After m steps, the fiber returns to its original value. -/
theorem iterate_m_fiber (c : Fin 3) (v : Vertex m) :
    fiber m ((step m c)^[m] v) = fiber m v := by
  rw [iterate_fiber]
  simp

/-- Two orbit points with the same fiber differ by a multiple of m steps. -/
theorem fiber_eq_of_iterate (c : Fin 3) (v : Vertex m) {a b : ℕ}
    (h : fiber m ((step m c)^[a] v) = fiber m ((step m c)^[b] v)) :
    (a : ZMod m) = (b : ZMod m) := by
  rw [iterate_fiber, iterate_fiber] at h
  exact add_left_cancel h

/-- The orbit is Hamiltonian iff it has period m³. Since step c is a bijection,
  this means the permutation has a single cycle. We state it as:
  step c has minimal period m³ at every vertex. -/
def IsHamiltonian (f : Vertex m → Vertex m) : Prop :=
  ∀ v, Function.minimalPeriod f v = m ^ 3

/-- A Hamiltonian function visits all vertices from any starting point. -/
theorem IsHamiltonian.surj_orbit {f : Vertex m → Vertex m} (hf : IsHamiltonian m f)
    (hbij : Function.Bijective f) (v : Vertex m) :
    ∀ w, ∃ n, n < m ^ 3 ∧ f^[n] v = w := by
  intro w
  -- Since f is bijective and has minimal period m³ at v,
  -- the orbit of v has exactly m³ elements = |Vertex m|,
  -- so every vertex is in the orbit.
  sorry

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

end ClaudeCycles
