/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: interior support bound u + v < 264/5. -/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleGeometry

/-!
# Genuine coverage by the four closed dyadic children

The actual midpoint split covers every point of the parent rectangle. A separate
lower-corner inequality excludes rectangles lying beyond the strict support
triangle. These geometric statements allow the recorded finite subdivision to
be assembled without trusting an external coverage checker.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square.GeneratorRectangle

/-- One actual closed dyadic child, with unchanged integer cell coordinates. -/
def child (T : GeneratorRectangle) (a b : Fin 2) : GeneratorRectangle :=
  ⟨T.cellU, T.cellV, T.depth + 1, 2 * T.indexU + a, 2 * T.indexV + b⟩

theorem width_child (T : GeneratorRectangle) (a b : Fin 2) :
    (T.child a b).width = T.radius := by
  simp only [child, width, radius, pow_succ]
  ring

theorem lowerU_child (T : GeneratorRectangle) (a b : Fin 2) :
    (T.child a b).lowerU = T.lowerU + (a.val : ℚ) * T.radius := by
  rw [lowerU, width_child]
  simp only [child, lowerU, radius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem lowerV_child (T : GeneratorRectangle) (a b : Fin 2) :
    (T.child a b).lowerV = T.lowerV + (b.val : ℚ) * T.radius := by
  rw [lowerV, width_child]
  simp only [child, lowerV, radius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The true four closed children cover the entire actual parent rectangle. -/
theorem Contains.child_coverage {T : GeneratorRectangle} {u v : ℝ}
    (h : T.Contains u v) :
    (T.child 0 0).Contains u v ∨ (T.child 0 1).Contains u v ∨
      (T.child 1 0).Contains u v ∨ (T.child 1 1).Contains u v := by
  have hu₀ := h.1
  have hu₁ := h.2.1
  have hv₀ := h.2.2.1
  have hv₁ := h.2.2.2
  have hhalf : (T.width : ℝ) = 2 * (T.radius : ℝ) := by
    simp only [radius, Rat.cast_div, Rat.cast_ofNat]
    ring
  simp only [Rat.cast_add] at hu₁ hv₁
  by_cases hu : u ≤ (T.centerU : ℝ) <;> by_cases hv : v ≤ (T.centerV : ℝ)
  · apply Or.inl
    simp only [Contains, lowerU_child, lowerV_child, width_child,
      Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, Rat.cast_add]
    simp only [centerU, centerV, Rat.cast_add] at hu hv
    exact ⟨hu₀, hu, hv₀, hv⟩
  · apply Or.inr ∘ Or.inl
    simp only [Contains, lowerU_child, lowerV_child, width_child,
      Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      add_zero, Rat.cast_add]
    simp only [centerU, centerV, Rat.cast_add] at hu hv
    exact ⟨hu₀, hu, by linarith, by linarith⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    simp only [Contains, lowerU_child, lowerV_child, width_child,
      Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      add_zero, Rat.cast_add]
    simp only [centerU, centerV, Rat.cast_add] at hu hv
    exact ⟨by linarith, by linarith, hv₀, hv⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    simp only [Contains, lowerU_child, lowerV_child, width_child,
      Fin.val_one, Nat.cast_one, one_mul, Rat.cast_add]
    simp only [centerU, centerV, Rat.cast_add] at hu hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A lower-corner check excludes every point of an actual exterior rectangle. -/
theorem not_contains_of_lower_sum_le {T : GeneratorRectangle} {u v : ℝ}
    (hT : 264 / 5 ≤ T.lowerU + T.lowerV) (hr : u + v < 264 / 5) : ¬ T.Contains u v := by
  intro h
  have hT' : ((264 / 5 : ℚ) : ℝ) ≤ ((T.lowerU + T.lowerV : ℚ) : ℝ) := by exact_mod_cast hT
  have hl := h.lower_sum_le
  push_cast at hT' hl
  linarith

end PartialBalayage.Maximal.Square.GeneratorRectangle
