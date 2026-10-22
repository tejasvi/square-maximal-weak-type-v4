/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5; the generator of the cubic spline is 2560000/792561 times the fourth difference of |x|^(73/40). -/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCancellation

/-!
# The exact genuine stable generator of the cardinal cubic spline

The full singular integral is integrable. Its finite polynomial primitive and actual
compact-support tail cancel, proving the exact physical-space formula with coefficient
`2560000/792561` and no generator certificate assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

theorem cubicSplineSecondDifference_eq_tail {x T t : ℝ}
    (hT : |x| + 2 ≤ T) (ht : T < t) :
    cubicSplineSecondDifference x t = -2 * cubicSpline x := by
  have h₁ : 2 ≤ |x + t| := by
    linarith [neg_abs_le x, le_abs_self (x + t)]
  have h₂ : 2 ≤ |x - t| := by
    linarith [le_abs_self x, neg_le_abs (x - t)]
  unfold cubicSplineSecondDifference
  rw [cubicSpline_eq_zero_of_two_le_abs h₁, cubicSpline_eq_zero_of_two_le_abs h₂]
  ring

theorem integrableOn_weighted_cubicSplineSecondDifference_tail {x T : ℝ}
    (hT : 0 < T) (hxT : |x| + 2 ≤ T) : IntegrableOn
      (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) (Ioi T) := by
  have hi : IntegrableOn (fun t : ℝ ↦ (-2 * cubicSpline x) * t ^ (-87 / 40 : ℝ))
      (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-87 / 40 : ℝ) < -1) hT).const_mul
      (-2 * cubicSpline x)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [cubicSplineSecondDifference_eq_tail hxT ht]
  ring

theorem integral_weighted_cubicSplineSecondDifference_tail {x T : ℝ}
    (hT : 0 < T) (hxT : |x| + 2 ≤ T) :
    (∫ t in Ioi T, t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      -(80 / 47 : ℝ) * cubicSpline x * T ^ (-47 / 40 : ℝ) := by
  have heq : (∫ t in Ioi T, t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      ∫ t in Ioi T, (-2 * cubicSpline x) * t ^ (-87 / 40 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [cubicSplineSecondDifference_eq_tail hxT ht]
    ring
  rw [heq, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-87 / 40 : ℝ) < -1) hT]
  norm_num only [show (-87 / 40 : ℝ) + 1 = -47 / 40 by norm_num]
  ring

/-- The actual full singular integral of the translated spline exists. -/
theorem integrableOn_weighted_cubicSplineSecondDifference (x : ℝ) : IntegrableOn
    (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) (Ioi 0) := by
  let T : ℝ := |x| + 3
  have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg x]
  have hxT : |x| + 2 ≤ T := by dsimp [T]; linarith
  have hnear := intervalIntegrable_weighted_cubicSplineSecondDifference hT hxT
  have hnear' : IntegrableOn (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      cubicSplineSecondDifference x t) (Ioc 0 T) := by
    simpa only [uIoc_of_le hT.le] using hnear.def'
  have hfar := integrableOn_weighted_cubicSplineSecondDifference_tail hT hxT
  rw [← Ioc_union_Ioi_eq_Ioi hT.le, integrableOn_union]
  exact ⟨hnear', hfar⟩

/-- The actual full physical singular integral has the exact source formula. -/
theorem integral_weighted_cubicSplineSecondDifference_full (x : ℝ) :
    (∫ t in Ioi 0, t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t) =
      (2560000 / 792561 : ℝ) * splineGeneratorPower x := by
  let T : ℝ := |x| + 3
  have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg x]
  have hxT : |x| + 2 ≤ T := by dsimp [T]; linarith
  have hnear := intervalIntegrable_weighted_cubicSplineSecondDifference hT hxT
  have hnear' : IntegrableOn (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) *
      cubicSplineSecondDifference x t) (Ioc 0 T) := by
    simpa only [uIoc_of_le hT.le] using hnear.def'
  rw [← Ioc_union_Ioi_eq_Ioi hT.le,
    setIntegral_union (by
      apply disjoint_left.mpr
      intro t ht ht'
      exact (not_lt_of_ge ht.2) ht') measurableSet_Ioi hnear'
        (integrableOn_weighted_cubicSplineSecondDifference_tail hT hxT),
    ← intervalIntegral.integral_of_le hT.le,
    integral_weighted_cubicSplineSecondDifference hT hxT,
    integral_weighted_cubicSplineSecondDifference_tail hT hxT]
  ring

/-- The true stable generator, in the project's physical normalization. -/
theorem stableGeneratorIntegral_cubicSpline (x : ℝ) :
    PartialBalayage.Linear.stableGeneratorIntegral (47 / 40 : ℝ)
      (fun t : ℝ ↦ cubicSpline (x + t)) =
        (2560000 / 792561 : ℝ) * splineGeneratorPower x := by
  have heq : (fun t : ℝ ↦ t ^ (-1 - (47 / 40 : ℝ)) •
      PartialBalayage.Linear.stableSecondDifference (fun t : ℝ ↦ cubicSpline (x + t)) t) =
      fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * cubicSplineSecondDifference x t := by
    funext t
    simp only [PartialBalayage.Linear.stableSecondDifference, cubicSplineSecondDifference,
      smul_eq_mul, add_zero, ← sub_eq_add_neg, show (-1 - (47 / 40 : ℝ)) = -87 / 40 by norm_num]
  unfold PartialBalayage.Linear.stableGeneratorIntegral
  rw [heq]
  exact integral_weighted_cubicSplineSecondDifference_full x

end PartialBalayage.Maximal.Square
