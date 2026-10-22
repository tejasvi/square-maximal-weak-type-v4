/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic

/-!
# The genuine centered cubic cardinal spline

The piecewise polynomial definition is identified with the supplement's fourth finite
difference of positive cubic powers. This exposes its nonnegativity, symmetry and compact
support as mathematical theorems, independent of any computational certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The actual centered cubic cardinal spline in its equivalent absolute-value form. -/
def cubicSpline (x : ℝ) : ℝ :=
  if |x| ≤ 1 then (4 - 6 * |x| ^ (2 : ℕ) + 3 * |x| ^ (3 : ℕ)) / 6
  else if |x| ≤ 2 then (2 - |x|) ^ (3 : ℕ) / 6 else 0

/-- The spline is even in its actual scalar argument. -/
theorem cubicSpline_neg (x : ℝ) : cubicSpline (-x) = cubicSpline x := by
  simp only [cubicSpline, abs_neg]

/-- The genuine spline vanishes at and beyond its support endpoints. -/
theorem cubicSpline_eq_zero_of_two_le_abs {x : ℝ} (hx : 2 ≤ |x|) : cubicSpline x = 0 := by
  have hnot : ¬ |x| ≤ 1 := by linarith
  rw [cubicSpline, ite_eq_right hnot]
  split_ifs with h
  · have heq : |x| = 2 := le_antisymm h hx
    simp only [heq, sub_self, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_div]
  · rfl

/-- The actual spline is pointwise nonnegative. -/
theorem cubicSpline_nonneg (x : ℝ) : 0 ≤ cubicSpline x := by
  unfold cubicSpline
  split_ifs with h₁ h₂
  · have ha := abs_nonneg x
    have hpos : 0 ≤ 3 * |x| * (1 - |x|) ^ (2 : ℕ) := by positivity
    have hlin : 0 ≤ 3 * (1 - |x|) := by linarith
    nlinarith
  · positivity
  · exact le_rfl

set_option maxHeartbeats 1000000 in
/-- The spline is exactly the fourth difference of truncated cubic powers used by the source. -/
theorem cubicSpline_eq_positivePart_formula (x : ℝ) :
    cubicSpline x = ((max (x + 2) 0) ^ (3 : ℕ) - 4 * (max (x + 1) 0) ^ (3 : ℕ) +
      6 * (max x 0) ^ (3 : ℕ) - 4 * (max (x - 1) 0) ^ (3 : ℕ) +
        (max (x - 2) 0) ^ (3 : ℕ)) / 6 := by
  by_cases hx : 0 ≤ x
  · simp only [cubicSpline, abs_of_nonneg hx, max_eq_left hx,
      max_eq_left (by linarith : 0 ≤ x + 1), max_eq_left (by linarith : 0 ≤ x + 2)]
    by_cases h₁ : x ≤ 1
    · simp only [ite_eq_left h₁, max_eq_right (by linarith : x - 1 ≤ 0),
        max_eq_right (by linarith : x - 2 ≤ 0)]
      ring
    · by_cases h₂ : x ≤ 2
      · simp only [ite_eq_right h₁, ite_eq_left h₂,
          max_eq_left (by linarith : 0 ≤ x - 1), max_eq_right (by linarith : x - 2 ≤ 0)]
        ring
      · simp only [ite_eq_right h₁, ite_eq_right h₂,
          max_eq_left (by linarith : 0 ≤ x - 1), max_eq_left (by linarith : 0 ≤ x - 2)]
        ring
  · have hn : x ≤ 0 := le_of_not_ge hx
    simp only [cubicSpline, abs_of_nonpos hn, max_eq_right hn,
      max_eq_right (by linarith : x - 1 ≤ 0), max_eq_right (by linarith : x - 2 ≤ 0)]
    by_cases h₁ : -x ≤ 1
    · simp only [ite_eq_left h₁, max_eq_left (by linarith : 0 ≤ x + 1),
        max_eq_left (by linarith : 0 ≤ x + 2)]
      ring
    · by_cases h₂ : -x ≤ 2
      · simp only [ite_eq_right h₁, ite_eq_left h₂,
          max_eq_left (by linarith : 0 ≤ x + 2), max_eq_right (by linarith : x + 1 ≤ 0)]
        ring
      · simp only [ite_eq_right h₁, ite_eq_right h₂,
          max_eq_right (by linarith : x + 1 ≤ 0), max_eq_right (by linarith : x + 2 ≤ 0)]
        ring

/-- The actual spline is continuous, directly from its proven positive-part expression. -/
theorem continuous_cubicSpline : Continuous cubicSpline := by
  have hfun : cubicSpline = fun x : ℝ ↦
      ((max (x + 2) 0) ^ (3 : ℕ) - 4 * (max (x + 1) 0) ^ (3 : ℕ) +
        6 * (max x 0) ^ (3 : ℕ) - 4 * (max (x - 1) 0) ^ (3 : ℕ) +
          (max (x - 2) 0) ^ (3 : ℕ)) / 6 := funext cubicSpline_eq_positivePart_formula
  rw [hfun]
  fun_prop

/-- The actual spline has compact support contained in its stated support interval. -/
theorem hasCompactSupport_cubicSpline : HasCompactSupport cubicSpline := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))
  intro x hx
  have hne : cubicSpline x ≠ 0 := hx
  by_contra h
  have htwo : 2 ≤ |x| := by
    simp only [mem_Icc, not_and_or] at h
    rcases h with h | h
    · rw [abs_of_nonpos (by linarith : x ≤ 0)]
      linarith
    · exact (le_abs_self x).trans' (le_of_not_ge h)
  exact hne (cubicSpline_eq_zero_of_two_le_abs htwo)

/-- The actual spline is Lebesgue integrable. -/
theorem integrable_cubicSpline : Integrable cubicSpline :=
  continuous_cubicSpline.integrable_of_hasCompactSupport hasCompactSupport_cubicSpline

/-- The integral over the central positive unit interval is the exact rational `11/24`. -/
theorem integral_cubicSpline_zero_one : (∫ x in (0 : ℝ)..1, cubicSpline x) = 11 / 24 := by
  have hform : (∫ x in (0 : ℝ)..1, cubicSpline x) =
      ∫ x in (0 : ℝ)..1, (4 - 6 * x ^ (2 : ℕ) + 3 * x ^ (3 : ℕ)) / 6 := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc] at hx
    simp only [cubicSpline, abs_of_nonneg hx.1, ite_eq_left hx.2]
  rw [hform]
  have hder (x : ℝ) : HasDerivAt
      (fun x : ℝ ↦ (4 * x - 2 * x ^ (3 : ℕ) + (3 / 4 : ℝ) * x ^ (4 : ℕ)) / 6)
      ((4 - 6 * x ^ (2 : ℕ) + 3 * x ^ (3 : ℕ)) / 6) x := by
    convert! (((hasDerivAt_id x).const_mul 4).sub
      (((hasDerivAt_id x).pow 3).const_mul 2)).add
        (((hasDerivAt_id x).pow 4).const_mul (3 / 4)) |>.div_const 6 using 1
    dsimp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hder x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-- The integral over the positive outer unit interval is the exact rational `1/24`. -/
theorem integral_cubicSpline_one_two : (∫ x in (1 : ℝ)..2, cubicSpline x) = 1 / 24 := by
  have hform : (∫ x in (1 : ℝ)..2, cubicSpline x) =
      ∫ x in (1 : ℝ)..2, (2 - x) ^ (3 : ℕ) / 6 := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), mem_Icc] at hx
    rw [cubicSpline, abs_of_nonneg (by linarith : 0 ≤ x)]
    by_cases h : x ≤ 1
    · have heq : x = 1 := le_antisymm h hx.1
      norm_num [heq]
    · simp only [ite_eq_right h, ite_eq_left hx.2]
  rw [hform]
  have hder (x : ℝ) : HasDerivAt (fun x : ℝ ↦ -(2 - x) ^ (4 : ℕ) / 24)
      ((2 - x) ^ (3 : ℕ) / 6) x := by
    convert! (((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id x)).pow 4).neg.div_const 24
      using 1
    dsimp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hder x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-- The genuine centered cardinal spline has total integral one. -/
theorem integral_cubicSpline : (∫ x, cubicSpline x) = 1 := by
  have hint (a b : ℝ) : IntervalIntegrable cubicSpline volume a b :=
    continuous_cubicSpline.intervalIntegrable a b
  have h02 : (∫ x in (0 : ℝ)..2, cubicSpline x) = 1 / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 2),
      integral_cubicSpline_zero_one, integral_cubicSpline_one_two]
    norm_num
  have hn : (∫ x in (-2 : ℝ)..0, cubicSpline x) = 1 / 2 := by
    have h := intervalIntegral.integral_comp_neg (f := cubicSpline) (a := (0 : ℝ)) (b := 2)
    simpa only [cubicSpline_neg, neg_zero, h02] using h.symm
  have htotal : (∫ x, cubicSpline x) = ∫ x in (-2 : ℝ)..2, cubicSpline x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    apply cubicSpline_eq_zero_of_two_le_abs
    simp only [mem_Ioc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith : x ≤ 0)]
      linarith
    · exact (le_abs_self x).trans' (le_of_not_ge hx)
  rw [htotal, ← intervalIntegral.integral_add_adjacent_intervals (hint (-2) 0) (hint 0 2),
    hn, h02]
  norm_num

end PartialBalayage.Maximal.Square
