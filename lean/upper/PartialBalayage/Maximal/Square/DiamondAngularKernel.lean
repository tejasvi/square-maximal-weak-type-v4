/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialGeneratorDefinitions
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual crossed-axis angular cancellation

Translation of each crossed-axis half-line gives the same absolutely integrable symmetric
kernel. Its two signed contributions therefore cancel exactly. This is the physical-space
cancellation used when differentiating the genuine two-coordinate diamond generator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual symmetric crossed-axis kernel on the positive half-line. -/
def diamondCrossedAxisKernel (α u v q : ℝ) : ℝ :=
  (q + u) ^ (-1 - α) * (q + v) ^ (-1 - α)

/-- The common crossed-axis expression is a genuinely convergent integral. -/
theorem integrableOn_diamondCrossedAxisKernel {α u v : ℝ}
    (hα : 0 < α) (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (diamondCrossedAxisKernel α u v) (Ioi 0) := by
  have hi := (integrableOn_add_rpow_Ioi_of_lt
    (by linarith : -1 - α < -1) (by linarith : -u < 0)).const_mul (v ^ (-1 - α))
  apply hi.mono' (by unfold diamondCrossedAxisKernel; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hqpos : 0 < q := hq
  have hqu : 0 ≤ q + u := by linarith
  have hqv : 0 ≤ q + v := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos hv
    (by linarith : v ≤ q + v) (by linarith : -1 - α ≤ 0)
  rw [diamondCrossedAxisKernel, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hqu _) (Real.rpow_nonneg hqv _))]
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hqu _)).trans_eq (mul_comm _ _)

/-- Actual translation transports a positive half-line to its genuine shifted half-line. -/
theorem integral_Ioi_shift_right (f : ℝ → ℝ) (u : ℝ) :
    (∫ q in Ioi 0, f (q + u)) = ∫ t in Ioi u, f t := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) u).integral_comp
    (Homeomorph.addRight u).isClosedEmbedding.measurableEmbedding ((Ioi u).indicator f)
  have he : (fun q ↦ (Ioi u).indicator f (q + u)) =
      (Ioi 0).indicator (fun q ↦ f (q + u)) := by
    funext q
    simp only [indicator_apply, mem_Ioi]
    congr 1
    exact propext (by constructor <;> intro h <;> linarith : u < q + u ↔ 0 < q)
  rw [he, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

/-- Each true crossed-axis tail has the common symmetric integral after an actual translation. -/
theorem integral_diamond_crossed_axis (α u v : ℝ) :
    (∫ t in Ioi u, t ^ (-1 - α) * (t - u + v) ^ (-1 - α)) =
      ∫ q in Ioi 0, diamondCrossedAxisKernel α u v q := by
  rw [← integral_Ioi_shift_right _ u]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro q _
  simp only [diamondCrossedAxisKernel, add_sub_cancel_right]

/-- The actual two crossed-axis angular integrals cancel, including their true joining points. -/
theorem diamond_crossed_axis_cancellation (α u v : ℝ) :
    (∫ t in Ioi u, t ^ (-1 - α) * (t - u + v) ^ (-1 - α)) -
      (∫ t in Ioi v, t ^ (-1 - α) * (t - v + u) ^ (-1 - α)) = 0 := by
  rw [integral_diamond_crossed_axis, integral_diamond_crossed_axis]
  have he : diamondCrossedAxisKernel α u v = diamondCrossedAxisKernel α v u := by
    funext q
    exact mul_comm _ _
  rw [he, sub_self]

end PartialBalayage.Maximal.Square
