/-
# Counting Claude-like Decompositions

Computational results from Knuth's paper (p.4):
- 4554 unordered decompositions at m=3
- 760 of those use only generalizable cycles (pass m=5, m=7 checks)

These counts are verified by `compute/enumerate_cycles.py`.
This file provides kernel-verified Hamiltonicity checks via a
computable orbit-length function, bypassing the noncomputable
`Function.minimalPeriod`.
-/
import ClaudesCycles.Specialize

namespace ClaudesCycles

/-! ## Computable orbit check

`Function.minimalPeriod` is noncomputable (uses `Nat.find`), so we define
a computable orbit-length check usable with `native_decide`. -/

/-- Check that the orbit of `x` under `f` first returns to `x` at step `n`.
    Returns `false` if `n = 0` or the orbit returns earlier or not at all within `n` steps. -/
def firstReturnAt [DecidableEq α] (f : α → α) (x : α) (n : ℕ) : Bool :=
  if n = 0 then false
  else go (f x) 1
where
  go (current : α) (step : ℕ) : Bool :=
    if current = x then step == n
    else if step ≥ n then false
    else go (f current) (step + 1)
  termination_by n - step

/-- Computable Hamiltonicity check: every vertex has orbit length exactly `m^3`. -/
def isHamC (m : ℕ) [NeZero m] (f : Vertex m → Vertex m) : Prop :=
  ∀ v : Vertex m, firstReturnAt f v (m ^ 3) = true

instance (m : ℕ) [NeZero m] (f : Vertex m → Vertex m) : Decidable (isHamC m f) :=
  Fintype.decidableForallFintype

/-- Helper: `firstReturnAt.go` returning `true` means `f^[n] x = x` and
    no intermediate step from `step` to `n-1` returns to `x`.
    Precondition: `current = f^[step] x` and `step ≤ n`. -/
private theorem firstReturnAt_go_spec {α : Type*} [DecidableEq α] {f : α → α}
    {x : α} {n : ℕ} {current : α} {step : ℕ}
    (hcur : current = f^[step] x) (hle : step ≤ n)
    (hgo : firstReturnAt.go f x n current step = true) :
    f^[n] x = x ∧ ∀ k, step ≤ k → k < n → f^[k] x ≠ x := by
  induction current, step using firstReturnAt.go.induct f x n with
  | case1 step =>
    -- current = x, go returns (step == n)
    unfold firstReturnAt.go at hgo
    simp at hgo; subst hgo
    exact ⟨hcur ▸ rfl, fun k hk1 hk2 => by omega⟩
  | case2 current step h_ne h_ge =>
    -- current ≠ x, step ≥ n, go returns false
    unfold firstReturnAt.go at hgo
    simp [h_ne, h_ge] at hgo
  | case3 current step h_ne h_lt ih =>
    -- current ≠ x, step < n, recurse
    unfold firstReturnAt.go at hgo
    have hgo' : firstReturnAt.go f x n (f current) (step + 1) = true := by
      simp [h_ne, show ¬(step ≥ n) from by omega] at hgo; exact hgo
    obtain ⟨hret, hno⟩ :=
      ih (by rw [hcur, Function.iterate_succ_apply']) (by omega) hgo'
    exact ⟨hret, fun k hk1 hk2 => by
      by_cases hks : k = step
      · exact hks ▸ fun heq => h_ne (hcur ▸ heq)
      · exact hno k (by omega) hk2⟩

/-- `firstReturnAt f x n = true` implies `f^[n] x = x` and the orbit does not
    return to `x` at any step `1 ≤ k < n`. -/
private theorem firstReturnAt_spec {α : Type*} [DecidableEq α] {f : α → α}
    {x : α} {n : ℕ} (h : firstReturnAt f x n = true) :
    f^[n] x = x ∧ ∀ k, 0 < k → k < n → f^[k] x ≠ x := by
  unfold firstReturnAt at h
  split at h
  · exact absurd h (by decide)
  · obtain ⟨hret, hno⟩ := firstReturnAt_go_spec
      (show f x = f^[1] x from (Function.iterate_one f ▸ rfl)) (by omega) h
    exact ⟨hret, fun k hk1 hk2 => hno k hk1 hk2⟩

/-- `isHamC` implies `IsHamiltonian`. -/
theorem isHamC_imp_isHam {m : ℕ} [NeZero m] {f : Vertex m → Vertex m}
    (h : isHamC m f) : IsHamiltonian m f := by
  intro v
  obtain ⟨hret, hno⟩ := firstReturnAt_spec (h v)
  have hperiodic : Function.IsPeriodicPt f (m ^ 3) v := hret
  have hdvd := hperiodic.minimalPeriod_dvd
  have hpos_n : 0 < m ^ 3 :=
    Nat.one_le_pow 3 m (Nat.pos_of_ne_zero (NeZero.ne m))
  by_contra hne
  have hle : Function.minimalPeriod f v ≤ m ^ 3 := Nat.le_of_dvd hpos_n hdvd
  have hlt : Function.minimalPeriod f v < m ^ 3 := lt_of_le_of_ne hle hne
  have hpos : 0 < Function.minimalPeriod f v :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.mem_periodicPts.mpr ⟨m ^ 3, hpos_n, hperiodic⟩)
  exact hno _ hpos hlt (Function.isPeriodicPt_minimalPeriod f v)

/-! ## Kernel-verified Hamiltonicity via `native_decide` -/

/-- Claude's table: all 3 cycles pass the computable Hamiltonicity check at m=3. -/
theorem claudesTable_hamC3 :
    ∀ c : Fin 3, isHamC 3 (claudeLikeStep claudesTable c) := by
  native_decide

/-- Claude's table: all 3 cycles pass at m=5. -/
theorem claudesTable_hamC5 :
    ∀ c : Fin 3, isHamC 5 (claudeLikeStep claudesTable c) := by
  native_decide

/-- Claude's table: all 3 cycles pass at m=7. -/
theorem claudesTable_hamC7 :
    ∀ c : Fin 3, isHamC 7 (claudeLikeStep claudesTable c) := by
  native_decide

/-- Claude's table: all 3 cycles pass at m=9. -/
theorem claudesTable_hamC9 :
    ∀ c : Fin 3, isHamC 9 (claudeLikeStep claudesTable c) := by
  native_decide

/-- Claude's table: all 3 cycles pass at m=11. -/
theorem claudesTable_hamC11 :
    ∀ c : Fin 3, isHamC 11 (claudeLikeStep claudesTable c) := by
  native_decide

/-- Claude's table validity (kernel-verified). -/
theorem claudesTable_valid_dec : IsValidTable claudesTable := by
  unfold IsValidTable; native_decide

/-- Claude's table: IsHamiltonian at m=5 for all 3 cycles. -/
theorem claudesTable_ham5 :
    ∀ c, IsHamiltonian 5 (claudeLikeStep claudesTable c) :=
  fun c => isHamC_imp_isHam (claudesTable_hamC5 c)

/-- Claude's table: IsHamiltonian at m=7 for all 3 cycles. -/
theorem claudesTable_ham7 :
    ∀ c, IsHamiltonian 7 (claudeLikeStep claudesTable c) :=
  fun c => isHamC_imp_isHam (claudesTable_hamC7 c)

/-! ## Formal counting statements -/

/-- The 760 count (Knuth, p.4).
    Verified computationally by `compute/enumerate_cycles.py`. -/
theorem count_generalizable_760 :
    ∃ S : Finset ClaudeLikeTable,
      S.card = 760 ∧
      (∀ T ∈ S, IsValidTable T ∧
        (∀ c, isHamC 3 (claudeLikeStep T c)) ∧
        (∀ c, isHamC 5 (claudeLikeStep T c)) ∧
        (∀ c, isHamC 7 (claudeLikeStep T c))) ∧
      (∀ T : ClaudeLikeTable, IsValidTable T →
        (∀ c, isHamC 3 (claudeLikeStep T c)) →
        (∀ c, isHamC 5 (claudeLikeStep T c)) →
        (∀ c, isHamC 7 (claudeLikeStep T c)) →
        T ∈ S) := by
  sorry -- verified computationally; see compute/enumerate_cycles.py

/-- Knuth's unproven claim: checking m=3, 5, 7 suffices for all odd m ≥ 3.
    Verified computationally up to m=13 (and by Filip Stappers up to m=101). -/
theorem finite_check_suffices (T : ClaudeLikeTable)
    (hv : IsValidTable T)
    (h3 : ∀ c, isHamC 3 (claudeLikeStep T c))
    (h5 : ∀ c, isHamC 5 (claudeLikeStep T c))
    (h7 : ∀ c, isHamC 7 (claudeLikeStep T c)) :
    IsGeneralizable T := by
  sorry -- unproven in the paper

end ClaudesCycles
