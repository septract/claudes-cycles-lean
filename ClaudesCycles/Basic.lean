/-
# Basic Properties of Claude's Cycles

fiber_bump, fiber_step, direction_perm, step_injective.
-/
import ClaudesCycles.Defs
import Mathlib.Data.Fintype.Card

namespace ClaudesCycles

variable (m : ℕ) [NeZero m]

/-- Bumping any coordinate increases the fiber by 1. -/
@[simp]
theorem fiber_bump (v : Vertex m) (d : Fin 3) :
    fiber m (bump m v d) = fiber m v + 1 := by
  simp only [fiber, bump]
  fin_cases d <;> simp [add_comm, add_assoc, add_left_comm]

/-- Stepping any cycle increases the fiber by 1. -/
@[simp]
theorem fiber_step (c : Fin 3) (v : Vertex m) :
    fiber m (step m c v) = fiber m v + 1 := by
  simp [step]

/-- At each vertex, the three cycles bump distinct coordinates. -/
theorem direction_injective (v : Vertex m) :
    Function.Injective (fun c => direction m c v) := by
  intro c₁ c₂ h
  simp only [direction] at h
  fin_cases c₁ <;> fin_cases c₂ <;> simp_all <;>
    split_ifs at h <;> simp_all

/-- The direction function at each vertex is a bijection Fin 3 → Fin 3. -/
theorem direction_bijective (v : Vertex m) :
    Function.Bijective (fun c => direction m c v) :=
  (Finite.injective_iff_bijective).mp (direction_injective m v)

/-- Bumping is injective per coordinate. -/
theorem bump_injective (d : Fin 3) :
    Function.Injective (fun v : Vertex m => bump m v d) := by
  intro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩ h
  simp only [bump] at h
  fin_cases d <;> simp_all [Prod.mk.injEq]

-- Large case split on 3 cycles × fiber regions × direction pairs
set_option maxHeartbeats 800000 in
/-- step c is injective on Vertex m. The pivot coordinate (preserved by both
  bumps) determines the direction within each fiber region, so different
  directions force a contradiction. -/
theorem step_injective (c : Fin 3) :
    Function.Injective (step m c) := by
  intro v w hvw
  have hf : fiber m v = fiber m w :=
    add_right_cancel (show fiber m v + 1 = fiber m w + 1 by
      rw [← fiber_step m c v, ← fiber_step m c w, hvw])
  unfold step at hvw
  by_cases hd : direction m c v = direction m c w
  · rw [hd] at hvw; exact bump_injective m (direction m c w) hvw
  · exfalso
    simp only [direction] at hd
    simp only [bump] at hvw
    fin_cases c <;> (
      simp only [direction] at hvw
      split_ifs at hd hvw <;> simp_all (config := { decide := true }) [Prod.ext_iff])

/-- step c is bijective on the finite type Vertex m. -/
theorem step_bijective (c : Fin 3) :
    Function.Bijective (step m c) :=
  (Finite.injective_iff_bijective).mp (step_injective m c)

/-- step c as an equivalence (permutation) on Vertex m. -/
noncomputable def stepEquiv (c : Fin 3) : Equiv.Perm (Vertex m) :=
  Equiv.ofBijective (step m c) (step_bijective m c)

end ClaudesCycles
