/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.KernelMass
public import PartialBalayage.Maximal.Square.DiamondAverageCap

/-!
# Positive exact coefficient of the original square kernel

The genuine unit diamond has area two and its indicator is dominated by
the original kernel. The actual half-mass coefficient is therefore at
least one, as well as strictly below the table's rational target.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The original unit diamond indicator has its true planar integral two. -/
theorem integral_euclideanDiamondIndicator_one :
    (∫ x, euclideanDiamondIndicator 1 x) = 2 := by
  rw [euclideanDiamondIndicator,
    integral_indicator (measurableSet_closedEuclideanDiamond 0 1), integral_const]
  change (volume.restrict (closedEuclideanDiamond 0 1) Set.univ).toReal * 1 = 2
  rw [Measure.restrict_apply_univ, volume_closedEuclideanDiamond 0 (by norm_num)]
  norm_num

/-- Genuine indicator domination bounds the original kernel half-mass below by one. -/
theorem one_le_half_integral_euclideanKernel [KernelMajorizationFacts] : 1 ≤ (∫ x, euclideanKernel x) / 2 := by
  have hmajor (x : EuclideanSpace ℝ (Fin 2)) :
      euclideanDiamondIndicator 1 x ≤ euclideanKernel x := by
    simpa only [dilatedComparisonKernel, inv_one, one_smul] using
      euclideanDiamondIndicator_le_dilatedKernel (by norm_num : (0 : ℝ) < 1) x
  have h := integral_mono (integrable_euclideanDiamondIndicator (by norm_num : (0 : ℝ) ≤ 1))
    integrable_euclideanKernel hmajor
  rw [integral_euclideanDiamondIndicator_one] at h
  linarith

theorem half_integral_euclideanKernel_pos [KernelMajorizationFacts] : 0 < (∫ x, euclideanKernel x) / 2 :=
  zero_lt_one.trans_le one_le_half_integral_euclideanKernel

end PartialBalayage.Maximal.Square
