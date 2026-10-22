/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CubicSpline
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Genuine twice continuous differentiability of the cubic spline

The truncated cubic is twice continuously differentiable even at its joining point.
The actual cardinal spline inherits this regularity from its proved fourth-difference
formula, so its fractional generator has no unaccounted corner distributions.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology ContDiff NNReal

namespace PartialBalayage.Maximal.Square

/-- The actual truncated natural power. -/
def positivePartPower (n : ℕ) (x : ℝ) : ℝ := (max x 0) ^ n

/-- Powers at least two have the true derivative at their joining point as well. -/
theorem hasDerivAt_positivePartPower {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (positivePartPower n) ((n : ℝ) * (max x 0) ^ (n - 1)) x := by
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n - 1 ≠ 0 := by omega
  by_cases hx : 0 < x
  · have heq : positivePartPower n =ᶠ[𝓝 x] fun t : ℝ ↦ t ^ n := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      simp only [positivePartPower, max_eq_left ht.le]
    simpa only [max_eq_left hx.le] using
      (hasDerivAt_pow n x).congr_of_eventuallyEq heq
  by_cases hx' : x < 0
  · have heq : positivePartPower n =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx'] with t ht
      simp only [positivePartPower, max_eq_right ht.le, zero_pow hn₀]
    simpa only [max_eq_right hx'.le, zero_pow hn₁, mul_zero] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  have hx₀ : x = 0 := by linarith
  subst x
  have ht : Tendsto (fun t : ℝ ↦ (max t 0) ^ (n - 1)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ (max t 0) ^ (n - 1)) := by fun_prop
    simpa only [max_self, zero_pow hn₁] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hzero : HasDerivAt (positivePartPower n) 0 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht₀
    have ht' : t ≠ 0 := ht₀
    simp only [positivePartPower, zero_add, max_self, zero_pow hn₀, sub_zero, smul_eq_mul]
    by_cases htpos : 0 ≤ t
    · rw [max_eq_left htpos, show n = (n - 1) + 1 by omega, pow_succ]
      field_simp
      simp only [Nat.add_sub_cancel]
    · simp only [max_eq_right (le_of_not_ge htpos), zero_pow hn₀, zero_pow hn₁, mul_zero]
  simpa only [max_self, zero_pow hn₁, mul_zero] using hzero

theorem deriv_positivePartPower {n : ℕ} (hn : 2 ≤ n) :
    deriv (positivePartPower n) = fun x : ℝ ↦ (n : ℝ) * (max x 0) ^ (n - 1) :=
  funext (fun x ↦ (hasDerivAt_positivePartPower hn x).deriv)

/-- The actual truncated square is continuously differentiable. -/
theorem contDiff_one_positivePartPower_two : ContDiff ℝ 1 (positivePartPower 2) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (hasDerivAt_positivePartPower (by omega : 2 ≤ 2) x).differentiableAt, ?_⟩
  rw [deriv_positivePartPower (by omega : 2 ≤ 2)]
  exact continuous_const.mul ((continuous_id.max continuous_const).pow _)

/-- The actual truncated cubic is twice continuously differentiable. -/
theorem contDiff_two_positivePartPower_three : ContDiff ℝ 2 (positivePartPower 3) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_positivePartPower (by omega : 2 ≤ 3) x).differentiableAt,
    by norm_num, ?_⟩
  rw [deriv_positivePartPower (by omega : 2 ≤ 3)]
  exact contDiff_const.mul contDiff_one_positivePartPower_two

/-- The true compact cardinal cubic spline is twice continuously differentiable. -/
theorem contDiff_two_cubicSpline : ContDiff ℝ 2 cubicSpline := by
  have h (a : ℝ) : ContDiff ℝ 2 (fun x : ℝ ↦ positivePartPower 3 (x + a)) :=
    contDiff_two_positivePartPower_three.comp (contDiff_id.add contDiff_const)
  have heq : cubicSpline = fun x : ℝ ↦
      (positivePartPower 3 (x + 2) - 4 * positivePartPower 3 (x + 1) +
        6 * positivePartPower 3 x - 4 * positivePartPower 3 (x - 1) +
          positivePartPower 3 (x - 2)) / 6 := by
    funext x
    exact cubicSpline_eq_positivePart_formula x
  rw [heq]
  convert (((((h 2).sub (contDiff_const.mul (h 1))).add
    (contDiff_const.mul contDiff_two_positivePartPower_three)).sub
      (contDiff_const.mul (h (-1)))).add (h (-2))).div_const 6 using 1

/-- The spline's actual first derivative, written as a fourth difference. -/
def cubicSplineFirst (x : ℝ) : ℝ :=
  ((max (x + 2) 0) ^ (2 : ℕ) - 4 * (max (x + 1) 0) ^ (2 : ℕ) +
    6 * (max x 0) ^ (2 : ℕ) - 4 * (max (x - 1) 0) ^ (2 : ℕ) +
      (max (x - 2) 0) ^ (2 : ℕ)) / 2

/-- The spline's actual second derivative has continuous, compactly supported hinges. -/
def cubicSplineSecond (x : ℝ) : ℝ :=
  max (x + 2) 0 - 4 * max (x + 1) 0 + 6 * max x 0 -
    4 * max (x - 1) 0 + max (x - 2) 0

theorem hasDerivAt_cubicSpline (x : ℝ) : HasDerivAt cubicSpline (cubicSplineFirst x) x := by
  have h (a : ℝ) : HasDerivAt (fun t : ℝ ↦ positivePartPower 3 (t + a))
      (3 * (max (x + a) 0) ^ (2 : ℕ)) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using
      (hasDerivAt_positivePartPower (by omega : 2 ≤ 3) (x + a)).comp_add_const x a
  have hd := (((((h 2).sub ((h 1).const_mul 4)).add ((h 0).const_mul 6)).sub
    ((h (-1)).const_mul 4)).add (h (-2))).div_const 6
  have heq : cubicSpline = fun t : ℝ ↦
      (positivePartPower 3 (t + 2) - 4 * positivePartPower 3 (t + 1) +
        6 * positivePartPower 3 (t + 0) - 4 * positivePartPower 3 (t + (-1)) +
          positivePartPower 3 (t + (-2))) / 6 := by
    funext t
    simpa only [positivePartPower, add_zero, ← sub_eq_add_neg] using
      cubicSpline_eq_positivePart_formula t
  rw [heq]
  convert hd using 1
  simp only [cubicSplineFirst, add_zero, ← sub_eq_add_neg]
  ring

theorem deriv_cubicSpline : deriv cubicSpline = cubicSplineFirst :=
  funext (fun x ↦ (hasDerivAt_cubicSpline x).deriv)

theorem hasDerivAt_cubicSplineFirst (x : ℝ) :
    HasDerivAt cubicSplineFirst (cubicSplineSecond x) x := by
  have h (a : ℝ) : HasDerivAt (fun t : ℝ ↦ positivePartPower 2 (t + a))
      (2 * max (x + a) 0) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hasDerivAt_positivePartPower (by omega : 2 ≤ 2) (x + a)).comp_add_const x a
  have hd := (((((h 2).sub ((h 1).const_mul 4)).add ((h 0).const_mul 6)).sub
    ((h (-1)).const_mul 4)).add (h (-2))).div_const 2
  convert hd using 1
  · funext t
    simp only [cubicSplineFirst, positivePartPower, add_zero, ← sub_eq_add_neg,
      Pi.sub_apply, Pi.add_apply]
  · simp only [cubicSplineSecond, add_zero, ← sub_eq_add_neg]
    ring

theorem deriv_cubicSplineFirst : deriv cubicSplineFirst = cubicSplineSecond :=
  funext (fun x ↦ (hasDerivAt_cubicSplineFirst x).deriv)

theorem deriv_deriv_cubicSpline : deriv (deriv cubicSpline) = cubicSplineSecond := by
  rw [deriv_cubicSpline, deriv_cubicSplineFirst]

theorem continuous_cubicSplineSecond : Continuous cubicSplineSecond := by
  unfold cubicSplineSecond
  fun_prop

theorem hasCompactSupport_cubicSplineFirst : HasCompactSupport cubicSplineFirst := by
  rw [← deriv_cubicSpline]
  exact hasCompactSupport_cubicSpline.deriv

theorem hasCompactSupport_cubicSplineSecond : HasCompactSupport cubicSplineSecond := by
  rw [← deriv_deriv_cubicSpline]
  exact hasCompactSupport_cubicSpline.deriv.deriv

/-- A genuine global Lipschitz constant for the derivative, obtained from the actual C² spline. -/
theorem exists_lipschitzWith_deriv_cubicSpline :
    ∃ K : ℝ≥0, LipschitzWith K (deriv cubicSpline) := by
  obtain ⟨C, hC⟩ := hasCompactSupport_cubicSplineSecond.exists_bound_of_continuous
    continuous_cubicSplineSecond
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨⟨C, hC₀⟩, lipschitzWith_of_nnnorm_deriv_le
    contDiff_two_cubicSpline.differentiable_deriv_two ?_⟩
  intro x
  change ‖deriv (deriv cubicSpline) x‖ ≤ C
  rw [deriv_deriv_cubicSpline]
  exact hC x

end PartialBalayage.Maximal.Square
