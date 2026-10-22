/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5; splineGeneratorPower is the fourth difference of |x|^(73/40) and the finite spline integral has coefficients 80/47 and 2560000/792561. -/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorFinite

/-!
# Genuine fourth-difference cancellation in the spline generator

The first three large-argument primitive terms cancel algebraically. The absolute
cubic term is exactly twelve times the actual spline value and therefore cancels
against the true compact-support tail.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual compact spline's symmetric second difference. -/
def cubicSplineSecondDifference (x t : ℝ) : ℝ :=
  cubicSpline (x + t) + cubicSpline (x - t) - 2 * cubicSpline x

/-- The exact fourth difference of the power `73/40`. -/
def splineGeneratorPower (x : ℝ) : ℝ :=
  |x + 2| ^ (73 / 40 : ℝ) - 4 * |x + 1| ^ (73 / 40 : ℝ) +
    6 * |x| ^ (73 / 40 : ℝ) - 4 * |x - 1| ^ (73 / 40 : ℝ) + |x - 2| ^ (73 / 40 : ℝ)

theorem cubicSplineSecondDifference_eq_fourth_difference (x t : ℝ) :
    cubicSplineSecondDifference x t =
      (truncatedCubicSecondDifference (x + 2) t -
        4 * truncatedCubicSecondDifference (x + 1) t +
        6 * truncatedCubicSecondDifference x t -
        4 * truncatedCubicSecondDifference (x - 1) t +
        truncatedCubicSecondDifference (x - 2) t) / 6 := by
  unfold cubicSplineSecondDifference
  rw [cubicSpline_eq_positivePart_formula (x + t),
    cubicSpline_eq_positivePart_formula (x - t), cubicSpline_eq_positivePart_formula x]
  have hadd (a : ℝ) : x + t + a = (x + a) + t := by ring
  have hsub (a : ℝ) : x - t + a = (x + a) - t := by ring
  have hsubadd (a : ℝ) : x + t - a = (x - a) + t := by ring
  have hsubsub (a : ℝ) : x - t - a = (x - a) - t := by ring
  simp only [truncatedCubicSecondDifference, positivePartPower]
  rw [hadd 2, hadd 1, hsub 2, hsub 1, hsubadd 1, hsubadd 2, hsubsub 1, hsubsub 2]
  ring

theorem weighted_cubicSplineSecondDifference_eq_fourth_difference (x t : ℝ) :
    t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t =
      (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 2) t -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 1) t) +
        6 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference x t) -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 1) t) +
        t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 2) t) / 6 := by
  rw [cubicSplineSecondDifference_eq_fourth_difference]
  ring

theorem abs_cube_eq_positivePartPower (z : ℝ) :
    |z| ^ (3 : ℕ) = 2 * positivePartPower 3 z - z ^ (3 : ℕ) := by
  unfold positivePartPower
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz]
    ring
  · rw [abs_of_nonpos hz, max_eq_right hz]
    ring

/-- The actual far primitive terms cancel, leaving the exact spline-value tail. -/
theorem fourth_difference_truncatedCubicGeneratorPrimitive (x T : ℝ) :
    (truncatedCubicGeneratorPrimitive (x + 2) T -
      4 * truncatedCubicGeneratorPrimitive (x + 1) T +
      6 * truncatedCubicGeneratorPrimitive x T -
      4 * truncatedCubicGeneratorPrimitive (x - 1) T +
      truncatedCubicGeneratorPrimitive (x - 2) T) / 6 =
        (80 / 47 : ℝ) * cubicSpline x * T ^ (-47 / 40 : ℝ) := by
  simp only [truncatedCubicGeneratorPrimitive, abs_cube_eq_positivePartPower,
    positivePartPower]
  rw [cubicSpline_eq_positivePart_formula]
  ring

private theorem spline_join_bound {x T : ℝ} (hx : |x| + 2 ≤ T)
    {c : ℝ} (hc : |c| ≤ 2) : |x + c| ≤ T :=
  (abs_add_le x c).trans (by linarith)

theorem intervalIntegrable_weighted_cubicSplineSecondDifference {x T : ℝ}
    (hT : 0 < T) (hxT : |x| + 2 ≤ T) : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) volume 0 T := by
  have hi (c : ℝ) (hc : |c| ≤ 2) :=
    intervalIntegrable_weighted_truncatedCubic hT (spline_join_bound hxT hc)
  have hi₂ := hi 2 (by norm_num)
  have hi₁ := hi 1 (by norm_num)
  have hi₀ : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference x t) volume 0 T := by
    simpa only [add_zero] using hi 0 (by norm_num)
  have hiNeg1 : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference (x - 1) t) volume 0 T := by
    simpa only [sub_eq_add_neg] using hi (-1) (by norm_num)
  have hiNeg2 : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference (x - 2) t) volume 0 T := by
    simpa only [sub_eq_add_neg] using hi (-2) (by norm_num)
  have heq : (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      fun t : ℝ ↦ (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 2) t -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 1) t) +
        6 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference x t) -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 1) t) +
        t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 2) t) / 6 :=
    funext (weighted_cubicSplineSecondDifference_eq_fourth_difference x)
  rw [heq]
  exact (((hi₂.sub (hi₁.const_mul 4)).add (hi₀.const_mul 6)).sub
    (hiNeg1.const_mul 4) |>.add hiNeg2).div_const 6

/-- The exact finite integral of the actual spline, including all joining points. -/
theorem integral_weighted_cubicSplineSecondDifference {x T : ℝ}
    (hT : 0 < T) (hxT : |x| + 2 ≤ T) :
    (∫ t in (0 : ℝ)..T, t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      (80 / 47 : ℝ) * cubicSpline x * T ^ (-47 / 40 : ℝ) +
        (2560000 / 792561 : ℝ) * splineGeneratorPower x := by
  have hi (c : ℝ) (hc : |c| ≤ 2) :=
    intervalIntegrable_weighted_truncatedCubic hT (spline_join_bound hxT hc)
  have hi₂ := hi 2 (by norm_num)
  have hi₁ := hi 1 (by norm_num)
  have hi₀ : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference x t) volume 0 T := by
    simpa only [add_zero] using hi 0 (by norm_num)
  have hiNeg1 : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference (x - 1) t) volume 0 T := by
    simpa only [sub_eq_add_neg] using hi (-1) (by norm_num)
  have hiNeg2 : IntervalIntegrable (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference (x - 2) t) volume 0 T := by
    simpa only [sub_eq_add_neg] using hi (-2) (by norm_num)
  have heq : (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      fun t : ℝ ↦ (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 2) t -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x + 1) t) +
        6 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference x t) -
        4 * (t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 1) t) +
        t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference (x - 2) t) / 6 :=
    funext (weighted_cubicSplineSecondDifference_eq_fourth_difference x)
  rw [heq, intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (((hi₂.sub (hi₁.const_mul 4)).add (hi₀.const_mul 6)).sub (hiNeg1.const_mul 4)) hiNeg2,
    intervalIntegral.integral_sub ((hi₂.sub (hi₁.const_mul 4)).add (hi₀.const_mul 6))
      (hiNeg1.const_mul 4),
    intervalIntegral.integral_add (hi₂.sub (hi₁.const_mul 4)) (hi₀.const_mul 6),
    intervalIntegral.integral_sub hi₂ (hi₁.const_mul 4)]
  simp only [intervalIntegral.integral_const_mul]
  have hx₂ := spline_join_bound hxT (by norm_num : |(2 : ℝ)| ≤ 2)
  have hx₁ := spline_join_bound hxT (by norm_num : |(1 : ℝ)| ≤ 2)
  have hx₀ : |x| ≤ T := by linarith [abs_nonneg x]
  have hxNeg1 : |x - 1| ≤ T := by
    simpa only [sub_eq_add_neg] using spline_join_bound hxT (by norm_num : |(-1 : ℝ)| ≤ 2)
  have hxNeg2 : |x - 2| ≤ T := by
    simpa only [sub_eq_add_neg] using spline_join_bound hxT (by norm_num : |(-2 : ℝ)| ≤ 2)
  rw [integral_weighted_truncatedCubic hT hx₂, integral_weighted_truncatedCubic hT hx₁,
    integral_weighted_truncatedCubic hT hx₀, integral_weighted_truncatedCubic hT hxNeg1,
    integral_weighted_truncatedCubic hT hxNeg2]
  have hp := fourth_difference_truncatedCubicGeneratorPrimitive x T
  unfold splineGeneratorPower
  linarith

end PartialBalayage.Maximal.Square
