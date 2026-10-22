/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplinePotential

/-!
# Exact evaluation of the actual spline's power potential

The continuous second derivative is integrated as five genuine hinges. The common
upper endpoint cancels by the fourth-difference coefficients. The lower endpoints
give the exact coefficient `25/36` in the power potential.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

theorem mul_signedRealPower {p : ℝ} (hp : 0 < p) (z : ℝ) :
    z * signedRealPower p z = |z| ^ (p + 1) := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · simp only [signedRealPower, max_eq_right hz.le, max_eq_left (neg_nonneg.mpr hz.le),
      Real.zero_rpow hp.ne', zero_sub, abs_of_neg hz]
    rw [Real.rpow_add (neg_pos.mpr hz), Real.rpow_one]
    ring
  · subst z
    simp only [signedRealPower, neg_zero, max_self, Real.zero_rpow hp.ne',
      sub_self, mul_zero, abs_zero, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  · simp only [signedRealPower, max_eq_left hz.le, max_eq_right (neg_nonpos.mpr hz.le),
      Real.zero_rpow hp.ne', sub_zero, abs_of_pos hz]
    rw [Real.rpow_add hz, Real.rpow_one]
    ring

theorem splineHingePrimitive_lower (x c : ℝ) :
    splineHingePrimitive x c (-c) = -(25 / 36 : ℝ) * |x + c| ^ (9 / 5 : ℝ) := by
  have hm := mul_signedRealPower (by norm_num : (0 : ℝ) < 4 / 5) (-(x + c))
  rw [abs_neg, show (4 / 5 : ℝ) + 1 = 9 / 5 by norm_num] at hm
  unfold splineHingePrimitive
  rw [show -c - x = -(x + c) by ring, abs_neg]
  nlinarith

theorem intervalIntegrable_splineHinge (x c a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ max (s + c) 0 * |s - x| ^ (-1 / 5 : ℝ))
      volume a b :=
  (intervalIntegrable_abs_sub_rpow (by norm_num : (-1 : ℝ) < -1 / 5) x a b)
    |>.continuousOn_mul ((continuous_id.add continuous_const).max continuous_const).continuousOn

/-- Each actual hinge gives a primitive difference on the fixed spline support interval. -/
theorem integral_splineHinge_on_support {c : ℝ} (hc₀ : -2 ≤ c) (hc₁ : c ≤ 2) (x : ℝ) :
    (∫ s in (-2 : ℝ)..2, max (s + c) 0 * |s - x| ^ (-1 / 5 : ℝ)) =
      splineHingePrimitive x c 2 + (25 / 36 : ℝ) * |x + c| ^ (9 / 5 : ℝ) := by
  have hzero : (∫ s in (-2 : ℝ)..(-c),
      max (s + c) 0 * |s - x| ^ (-1 / 5 : ℝ)) = 0 := by
    calc
      _ = ∫ s in (-2 : ℝ)..(-c), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : (-2 : ℝ) ≤ -c)] at hs
        simp only [max_eq_right (by linarith [hs.2] : s + c ≤ 0), zero_mul]
      _ = 0 := by simp
  have hright : (∫ s in (-c)..(2 : ℝ),
      max (s + c) 0 * |s - x| ^ (-1 / 5 : ℝ)) =
      ∫ s in (-c)..(2 : ℝ), (s + c) * |s - x| ^ (-1 / 5 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith : -c ≤ (2 : ℝ))] at hs
    dsimp only
    rw [max_eq_left (by linarith [hs.1] : 0 ≤ s + c)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_splineHinge x c (-2) (-c))
      (intervalIntegrable_splineHinge x c (-c) 2), hzero, zero_add, hright,
    integral_splineHinge (by linarith : -c ≤ (2 : ℝ)), splineHingePrimitive_lower]
  ring

theorem cubicSplineSecond_eq_zero_of_two_le_abs {s : ℝ} (hs : 2 ≤ |s|) :
    cubicSplineSecond s = 0 := by
  unfold cubicSplineSecond
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    simp only [max_eq_left (by linarith : 0 ≤ s + 2),
      max_eq_left (by linarith : 0 ≤ s + 1), max_eq_left h,
      max_eq_left (by linarith : 0 ≤ s - 1), max_eq_left (by linarith : 0 ≤ s - 2)]
    ring
  · rw [abs_of_nonpos h] at hs
    simp only [max_eq_right (by linarith : s + 2 ≤ 0),
      max_eq_right (by linarith : s + 1 ≤ 0), max_eq_right h,
      max_eq_right (by linarith : s - 1 ≤ 0), max_eq_right (by linarith : s - 2 ≤ 0)]
    ring

theorem integrable_cubicSplineSecond_potential (x : ℝ) :
    Integrable (fun s : ℝ ↦ cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ)) := by
  have hi : IntervalIntegrable
      (fun s : ℝ ↦ cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ)) volume (-2) 2 :=
    (intervalIntegrable_abs_sub_rpow (by norm_num : (-1 : ℝ) < -1 / 5) x (-2) 2)
      |>.continuousOn_mul continuous_cubicSplineSecond.continuousOn
  apply hi.def'.integrable_of_forall_notMem_eq_zero
  intro s hs
  rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2), mem_Ioc, not_and_or] at hs
  have hab : 2 ≤ |s| := by
    rcases hs with hs | hs
    · rw [abs_of_nonpos (by linarith : s ≤ 0)]
      linarith
    · exact (by linarith : (2 : ℝ) ≤ s).trans (le_abs_self s)
  rw [cubicSplineSecond_eq_zero_of_two_le_abs hab, zero_mul]

/-- The exact actual full power potential of the spline's second derivative. -/
theorem integral_cubicSplineSecond_potential (x : ℝ) :
    (∫ s : ℝ, cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ)) =
      (25 / 36 : ℝ) * (|x + 2| ^ (9 / 5 : ℝ) - 4 * |x + 1| ^ (9 / 5 : ℝ) +
        6 * |x| ^ (9 / 5 : ℝ) - 4 * |x - 1| ^ (9 / 5 : ℝ) +
          |x - 2| ^ (9 / 5 : ℝ)) := by
  have hi (c : ℝ) := intervalIntegrable_splineHinge x c (-2) 2
  have htotal : (∫ s : ℝ, cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ)) =
      ∫ s in (-2 : ℝ)..2, cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro s hs
    simp only [mem_Ioc, not_and_or] at hs
    have hab : 2 ≤ |s| := by
      rcases hs with hs | hs
      · rw [abs_of_nonpos (by linarith : s ≤ 0)]
        linarith
      · exact (by linarith : (2 : ℝ) ≤ s).trans (le_abs_self s)
    rw [cubicSplineSecond_eq_zero_of_two_le_abs hab, zero_mul]
  have heq : (fun s : ℝ ↦ cubicSplineSecond s * |s - x| ^ (-1 / 5 : ℝ)) =
      fun s : ℝ ↦ max (s + 2) 0 * |s - x| ^ (-1 / 5 : ℝ) -
        4 * (max (s + 1) 0 * |s - x| ^ (-1 / 5 : ℝ)) +
        6 * (max (s + 0) 0 * |s - x| ^ (-1 / 5 : ℝ)) -
        4 * (max (s + (-1)) 0 * |s - x| ^ (-1 / 5 : ℝ)) +
        max (s + (-2)) 0 * |s - x| ^ (-1 / 5 : ℝ) := by
    funext s
    simp only [cubicSplineSecond, add_zero, ← sub_eq_add_neg]
    ring
  rw [htotal, heq,
    intervalIntegral.integral_add
      (((hi 2).sub ((hi 1).const_mul 4)).add ((hi 0).const_mul 6)
        |>.sub ((hi (-1)).const_mul 4)) (hi (-2)),
    intervalIntegral.integral_sub
      (((hi 2).sub ((hi 1).const_mul 4)).add ((hi 0).const_mul 6))
      ((hi (-1)).const_mul 4),
    intervalIntegral.integral_add ((hi 2).sub ((hi 1).const_mul 4))
      ((hi 0).const_mul 6),
    intervalIntegral.integral_sub (hi 2) ((hi 1).const_mul 4)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_splineHinge_on_support (by norm_num : (-2 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 2),
    integral_splineHinge_on_support (by norm_num : (-2 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 2),
    integral_splineHinge_on_support (by norm_num : (-2 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 2),
    integral_splineHinge_on_support (by norm_num : (-2 : ℝ) ≤ -1)
      (by norm_num : (-1 : ℝ) ≤ 2),
    integral_splineHinge_on_support (by norm_num : (-2 : ℝ) ≤ -2)
      (by norm_num : (-2 : ℝ) ≤ 2)]
  simp only [splineHingePrimitive, add_zero, ← sub_eq_add_neg]
  ring

end PartialBalayage.Maximal.Square
