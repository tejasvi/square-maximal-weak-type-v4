/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5; squareIntrinsicConstant_pos now comes from GeneratorConstantBound. -/
module

public import PartialBalayage.Maximal.Square.DiamondCoordinateProfiles
public import PartialBalayage.Maximal.Square.DiagonalIntegralEvaluation

/-!
# The actual punctured diamond generator

Reflection of the original Euclidean coordinate lines and the convergent paired integral
identify the actual generator with the intrinsic-plus-incoming density in the interior.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem stableGeneratorIntegral_coordinateLine_diamondTruncatedPower (α R : ℝ)
    (x : E) (i : Fin 2) :
    stableGeneratorIntegral α (coordinateLine (diamondTruncatedPower α R) x i) =
      stableGeneratorIntegral α
        (diamondCoordinateTruncatedProfile α R |x i| |x (1 - i)|) := by
  unfold stableGeneratorIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    dsimp only
    rw [coordinateSecondDifference_diamondTruncatedPower])

/-- The actual Euclidean generator is the exact radial model off the two coordinate axes. -/
theorem coordinateStableGenerator_diamondTruncatedPower_eq_interior (x : E)
    (hx₀ : x 0 ≠ 0) (hx₁ : x 1 ≠ 0)
    (hr : diamondRadius (x 0) (x 1) < supportRadius) :
    coordinateStableGenerator (47 / 40) (diamondTruncatedPower (47 / 40) supportRadius) x =
      diamondInteriorSourceModel x := by
  have hu : 0 < |x 0| := abs_pos.mpr hx₀
  have hv : 0 < |x 1| := abs_pos.mpr hx₁
  have ht := stableGeneratorIntegral_diamondTruncated_pair
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num : (47 / 40 : ℝ) < 2)
    supportRadius_pos hu hv hr
  unfold coordinateStableGenerator
  simp only [Fin.sum_univ_two, stableGeneratorIntegral_coordinateLine_diamondTruncatedPower]
  change stableNormalization (47 / 40) *
    (stableGeneratorIntegral (47 / 40)
      (diamondCoordinateTruncatedProfile (47 / 40) supportRadius |x 0| |x 1|) +
    stableGeneratorIntegral (47 / 40)
      (diamondCoordinateTruncatedProfile (47 / 40) supportRadius |x 1| |x 0|)) = _
  rw [ht, diamondPairedGenerator_eq_intrinsic hu hv]
  unfold diamondInteriorSourceModel diamondRadius
  ring

/-- The genuine radial generator is nonnegative at every point off the axes. -/
theorem coordinateStableGenerator_diamondTruncatedPower_nonneg (x : E)
    (hx₀ : x 0 ≠ 0) (hx₁ : x 1 ≠ 0) :
    0 ≤ coordinateStableGenerator (47 / 40) (diamondTruncatedPower (47 / 40) supportRadius) x := by
  by_cases hr : diamondRadius (x 0) (x 1) < supportRadius
  · rw [coordinateStableGenerator_diamondTruncatedPower_eq_interior x hx₀ hx₁ hr]
    have hd : |(|x 0| - |x 1|)| ≤ supportRadius := by
      have he := abs_sub |x 0| |x 1|
      simp only [abs_abs] at he
      exact he.trans hr.le
    unfold diamondInteriorSourceModel
    exact mul_nonneg
      (stableNormalization_pos (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num)).le
      (add_nonneg (mul_nonneg squareIntrinsicConstant_pos.le
        (Real.rpow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) _))
        (radialIncomingTail_nonneg (by norm_num) supportRadius_pos hr.le hd))
  · exact coordinateStableGenerator_diamondTruncatedPower_nonneg_exterior
      (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num) supportRadius_pos x (le_of_not_gt hr)

end PartialBalayage.Maximal.Square
