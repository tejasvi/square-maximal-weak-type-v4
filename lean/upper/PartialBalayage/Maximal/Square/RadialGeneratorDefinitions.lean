/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5 (exponent -47/20 in the interior model). -/
module

public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.GeneratorConstantBound
public import PartialBalayage.Maximal.Square.GeneratorScaling

/-!
# Genuine diamond profiles and incoming-jump formulas

These explicit physical-space functions define the homogeneous diamond power, its positive
truncation, and the actual four-direction incoming tail. The radial density model records
the intended punctured source. Its distributional identification is a separate theorem;
no generator or source identity is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The true homogeneous diamond power with the standard harmless origin convention. -/
def diamondPower (α : ℝ) (x : E) : ℝ := (diamondRadius (x 0) (x 1)) ^ (-α)

/-- The unscaled positive truncation of the actual diamond power. -/
def diamondTruncatedPower (α R : ℝ) (x : E) : ℝ :=
  max (diamondPower α x - R ^ (-α)) 0

/-- The exact four-direction incoming-jump tail in the strict diamond interior. -/
def radialIncomingTail (α R r d : ℝ) : ℝ :=
  ∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) *
    (2 * (q - r) ^ (-1 - α) + (q - d) ^ (-1 - α) + (q + d) ^ (-1 - α))

/-- The explicit intrinsic-plus-incoming density model for the true unscaled radial base. -/
def diamondInteriorSourceModel (x : E) : ℝ :=
  stableNormalization (47 / 40) *
    (squareIntrinsicConstant * (diamondRadius (x 0) (x 1)) ^ (-47 / 20 : ℝ) +
      radialIncomingTail (47 / 40) supportRadius (diamondRadius (x 0) (x 1))
        (|x 0| - |x 1|))

/-- The concrete punctured radial density model. Its axis and boundary values are harmless
Lebesgue representatives; the distributional source theorem is proved separately. -/
def diamondTruncatedSourceModel (x : E) : ℝ :=
  if x = 0 then 0
  else if diamondRadius (x 0) (x 1) < supportRadius then diamondInteriorSourceModel x
  else if supportRadius < diamondRadius (x 0) (x 1) then
    coordinateStableGenerator (47 / 40) (diamondTruncatedPower (47 / 40) supportRadius) x
  else 0

theorem radialBase_eq_coefficient_diamondTruncatedPower (x : E) :
    radialBase (x 0) (x 1) =
      radialCoefficient * diamondTruncatedPower (47 / 40) supportRadius x := rfl

theorem diamondTruncatedPower_nonneg (α R : ℝ) (x : E) :
    0 ≤ diamondTruncatedPower α R x := le_max_right _ _

/-- The actual incoming tail has a nonnegative integrand whenever the truncation is positive. -/
theorem radialIncomingTail_nonneg {α R r d : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    (hr : r ≤ R) (hd : |d| ≤ R) :
    0 ≤ radialIncomingTail α R r d := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hpow := Real.rpow_le_rpow_of_nonpos hR hq.le (neg_nonpos.mpr hα)
  have hqr : 0 ≤ q - r := sub_nonneg.mpr (hr.trans hq.le)
  have hqd : 0 ≤ q - d := sub_nonneg.mpr ((le_abs_self d).trans (hd.trans hq.le))
  have hqnd : 0 ≤ q + d := by linarith [(abs_le.mp hd).1, (show R < q from hq)]
  exact mul_nonneg (sub_nonneg.mpr hpow)
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hqr _))
      (Real.rpow_nonneg hqd _)) (Real.rpow_nonneg hqnd _))

/-- The genuine positive truncation vanishes at and beyond its diamond support. -/
theorem diamondTruncatedPower_eq_zero_of_radius_le {α R : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (x : E) (hx : R ≤ diamondRadius (x 0) (x 1)) :
    diamondTruncatedPower α R x = 0 := by
  have hp := Real.rpow_le_rpow_of_nonpos hR hx (neg_nonpos.mpr hα)
  exact max_eq_right (sub_nonpos.mpr hp)

/-- The true exterior coordinate second-difference integral is nonnegative. -/
theorem coordinateStableGenerator_diamondTruncatedPower_nonneg_exterior
    {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (x : E)
    (hx : R ≤ diamondRadius (x 0) (x 1)) :
    0 ≤ coordinateStableGenerator α (diamondTruncatedPower α R) x := by
  unfold coordinateStableGenerator
  apply mul_nonneg (stableNormalization_pos hα0 hα2).le
  apply Finset.sum_nonneg
  intro i _
  unfold stableGeneratorIntegral
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [stableSecondDifference, coordinateLine, zero_smul, add_zero,
    diamondTruncatedPower_eq_zero_of_radius_le hα0.le hR x hx, smul_eq_mul,
    mul_zero, sub_zero]
  exact mul_nonneg (Real.rpow_nonneg ht.le _)
    (add_nonneg (diamondTruncatedPower_nonneg _ _ _) (diamondTruncatedPower_nonneg _ _ _))

end PartialBalayage.Maximal.Square
