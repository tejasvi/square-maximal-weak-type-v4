/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 (weight t^(-87/40); primitive coefficients 40/73, 40/11, -120/7, 40/47; endpoint power 15360000/792561 |z|^(73/40)). -/
module

public import PartialBalayage.Maximal.Square.SplinePotentialEvaluation
public import PartialBalayage.Linear.StableGeneratorScaling
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Actual finite stable integrals of truncated cubics

Each individual truncated cubic has a divergent full generator at infinity. Its genuine
finite-interval integral instead has an explicit primitive and a power correction.
The divergent polynomial terms can subsequently cancel in the actual spline's
fourth difference.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual symmetric second difference of a translated truncated cubic. -/
def truncatedCubicSecondDifference (z t : ℝ) : ℝ :=
  positivePartPower 3 (z + t) + positivePartPower 3 (z - t) -
    2 * positivePartPower 3 z

/-- The true large-argument primitive before the fourth-difference cancellation. -/
def truncatedCubicGeneratorPrimitive (z t : ℝ) : ℝ :=
  (40 / 73 : ℝ) * t ^ (73 / 40 : ℝ) + (40 / 11 : ℝ) * z * t ^ (33 / 40 : ℝ) -
    (120 / 7 : ℝ) * z ^ (2 : ℕ) * t ^ (-7 / 40 : ℝ) +
      (40 / 47 : ℝ) * |z| ^ (3 : ℕ) * t ^ (-47 / 40 : ℝ)

theorem truncatedCubicSecondDifference_near_nonneg {z t : ℝ}
    (hz : 0 ≤ z) (ht₀ : 0 ≤ t) (ht₁ : t ≤ z) :
    truncatedCubicSecondDifference z t = 6 * z * t ^ (2 : ℕ) := by
  simp only [truncatedCubicSecondDifference, positivePartPower,
    max_eq_left hz, max_eq_left (by linarith : 0 ≤ z + t),
    max_eq_left (by linarith : 0 ≤ z - t)]
  ring

theorem truncatedCubicSecondDifference_near_nonpos {z t : ℝ}
    (hz : z ≤ 0) (ht₀ : 0 ≤ t) (ht₁ : t ≤ -z) :
    truncatedCubicSecondDifference z t = 0 := by
  simp only [truncatedCubicSecondDifference, positivePartPower,
    max_eq_right hz, max_eq_right (by linarith : z + t ≤ 0),
    max_eq_right (by linarith : z - t ≤ 0), zero_pow (by omega : (3 : ℕ) ≠ 0)]
  ring

theorem truncatedCubicSecondDifference_far {z t : ℝ} (ht : |z| ≤ t) :
    truncatedCubicSecondDifference z t =
      t ^ (3 : ℕ) + 3 * z * t ^ (2 : ℕ) + 3 * z ^ (2 : ℕ) * t - |z| ^ (3 : ℕ) := by
  have hz₀ : z ≤ t := (le_abs_self z).trans ht
  have hz₁ : -z ≤ t := (neg_le_abs z).trans ht
  simp only [truncatedCubicSecondDifference, positivePartPower,
    max_eq_left (by linarith : 0 ≤ z + t), max_eq_right (by linarith : z - t ≤ 0)]
  rcases le_total 0 z with hz | hz
  · rw [max_eq_left hz, abs_of_nonneg hz]
    ring
  · rw [max_eq_right hz, abs_of_nonpos hz]
    ring

private theorem rpow_weighted_nat {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ (-87 / 40 : ℝ) * t ^ n = t ^ ((n : ℝ) - 87 / 40) := by
  rw [← Real.rpow_natCast t n, ← Real.rpow_add ht]
  congr 1
  ring

theorem weighted_truncatedCubicSecondDifference_far {z t : ℝ}
    (ht₀ : 0 < t) (ht₁ : |z| ≤ t) :
    t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference z t =
      t ^ (33 / 40 : ℝ) + 3 * z * t ^ (-7 / 40 : ℝ) +
        3 * z ^ (2 : ℕ) * t ^ (-47 / 40 : ℝ) - |z| ^ (3 : ℕ) * t ^ (-87 / 40 : ℝ) := by
  rw [truncatedCubicSecondDifference_far ht₁]
  have h₃ := rpow_weighted_nat ht₀ 3
  have h₂ := rpow_weighted_nat ht₀ 2
  have h₁ := rpow_weighted_nat ht₀ 1
  norm_num only [Nat.cast_ofNat, pow_one] at h₃ h₂ h₁
  have h₃' : t ^ (-87 / 40 : ℝ) * t ^ (3 : ℕ) = t ^ (33 / 40 : ℝ) := by
    convert h₃ using 1
    norm_num
  have h₂' : t ^ (-87 / 40 : ℝ) * t ^ (2 : ℕ) = t ^ (-7 / 40 : ℝ) := by
    convert h₂ using 1 <;> norm_num
  have h₁' : t ^ (-87 / 40 : ℝ) * t = t ^ (-47 / 40 : ℝ) := by
    convert h₁ using 1 <;> norm_num
  calc
    _ = (t ^ (-87 / 40 : ℝ) * t ^ (3 : ℕ)) +
        3 * z * (t ^ (-87 / 40 : ℝ) * t ^ (2 : ℕ)) +
        3 * z ^ (2 : ℕ) * (t ^ (-87 / 40 : ℝ) * t) -
        |z| ^ (3 : ℕ) * t ^ (-87 / 40 : ℝ) := by ring
    _ = _ := by rw [h₃', h₂', h₁']

theorem hasDerivAt_truncatedCubicGeneratorPrimitive (z : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (truncatedCubicGeneratorPrimitive z)
      (t ^ (33 / 40 : ℝ) + 3 * z * t ^ (-7 / 40 : ℝ) +
        3 * z ^ (2 : ℕ) * t ^ (-47 / 40 : ℝ) - |z| ^ (3 : ℕ) * t ^ (-87 / 40 : ℝ)) t := by
  have h (p : ℝ) := Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inl ht.ne')
  have hd := (((h (73 / 40)).const_mul (40 / 73)).add
    ((h (33 / 40)).const_mul ((40 / 11) * z))).sub
      ((h (-7 / 40)).const_mul ((120 / 7) * z ^ (2 : ℕ))) |>.add
        ((h (-47 / 40)).const_mul ((40 / 47) * |z| ^ (3 : ℕ)))
  convert hd using 1
  · funext s
    simp only [truncatedCubicGeneratorPrimitive, Pi.add_apply, Pi.sub_apply]
  · norm_num only [show (73 / 40 : ℝ) - 1 = 33 / 40 by norm_num,
      show (33 / 40 : ℝ) - 1 = -7 / 40 by norm_num,
      show (-7 / 40 : ℝ) - 1 = -47 / 40 by norm_num,
      show (-47 / 40 : ℝ) - 1 = -87 / 40 by norm_num]
    ring

/-- The actual far part is exactly the difference of its true primitive values. -/
theorem integral_weighted_truncatedCubic_far {z a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hz : |z| ≤ a) :
    (∫ t in a..b, t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference z t) =
      truncatedCubicGeneratorPrimitive z b - truncatedCubicGeneratorPrimitive z a := by
  have heq : (∫ t in a..b, t ^ (-87 / 40 : ℝ) *
      truncatedCubicSecondDifference z t) = ∫ t in a..b,
      t ^ (33 / 40 : ℝ) + 3 * z * t ^ (-7 / 40 : ℝ) +
        3 * z ^ (2 : ℕ) * t ^ (-47 / 40 : ℝ) - |z| ^ (3 : ℕ) * t ^ (-87 / 40 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact weighted_truncatedCubicSecondDifference_far (ha.trans_le ht.1) (hz.trans ht.1)
  rw [heq]
  have hp (p : ℝ) : ContinuousOn (fun t : ℝ ↦ t ^ p) (Icc a b) :=
    continuousOn_id.rpow_const (fun t ht ↦ Or.inl (ha.trans_le ht.1).ne')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (((hp (73 / 40)).const_mul (40 / 73)).add
      ((hp (33 / 40)).const_mul ((40 / 11) * z))).sub
        ((hp (-7 / 40)).const_mul ((120 / 7) * z ^ (2 : ℕ))) |>.add
          ((hp (-47 / 40)).const_mul ((40 / 47) * |z| ^ (3 : ℕ)))
  · intro t ht
    exact hasDerivAt_truncatedCubicGeneratorPrimitive z (ha.trans ht.1)
  · exact ((((hp (33 / 40)).add ((hp (-7 / 40)).const_mul (3 * z))).add
      ((hp (-47 / 40)).const_mul (3 * z ^ (2 : ℕ)))).sub
        ((hp (-87 / 40)).const_mul (|z| ^ (3 : ℕ)))) |>.intervalIntegrable_of_Icc hab

theorem intervalIntegrable_weighted_truncatedCubic_far {z a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : IntervalIntegrable
      (fun t : ℝ ↦ t ^ (-87 / 40 : ℝ) * truncatedCubicSecondDifference z t) volume a b := by
  have hc : Continuous (truncatedCubicSecondDifference z) := by
    unfold truncatedCubicSecondDifference positivePartPower
    fun_prop
  exact ((continuousOn_id.rpow_const
    (fun t ht ↦ Or.inl (ha.trans_le ht.1).ne')).mul hc.continuousOn)
      |>.intervalIntegrable_of_Icc hab

private theorem rpow_nat_mul {t : ℝ} (ht : 0 < t) (n : ℕ) (p : ℝ) :
    t ^ n * t ^ p = t ^ ((n : ℝ) + p) := by
  rw [← Real.rpow_natCast t n, ← Real.rpow_add ht]

theorem truncatedCubicGeneratorPrimitive_at_abs {z : ℝ} (hz : z ≠ 0) :
    truncatedCubicGeneratorPrimitive z |z| =
      (80 / 11 : ℝ) * max z 0 * |z| ^ (33 / 40 : ℝ) -
        (15360000 / 792561 : ℝ) * |z| ^ (73 / 40 : ℝ) := by
  have ha : 0 < |z| := abs_pos.mpr hz
  have h₁ : |z| * |z| ^ (33 / 40 : ℝ) = |z| ^ (73 / 40 : ℝ) := by
    simpa only [pow_one, Nat.cast_one, show (1 : ℝ) + 33 / 40 = 73 / 40 by norm_num] using
      rpow_nat_mul ha 1 (33 / 40)
  have h₂ : |z| ^ (2 : ℕ) * |z| ^ (-7 / 40 : ℝ) = |z| ^ (73 / 40 : ℝ) := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) + (-7 / 40) = 73 / 40 by norm_num] using
      rpow_nat_mul ha 2 (-7 / 40)
  have h₃ : |z| ^ (3 : ℕ) * |z| ^ (-47 / 40 : ℝ) = |z| ^ (73 / 40 : ℝ) := by
    simpa only [Nat.cast_ofNat, show (3 : ℝ) + (-47 / 40) = 73 / 40 by norm_num] using
      rpow_nat_mul ha 3 (-47 / 40)
  have hz₂ : z ^ (2 : ℕ) = |z| ^ (2 : ℕ) := by rw [sq_abs]
  unfold truncatedCubicGeneratorPrimitive
  rw [hz₂]
  rcases le_total 0 z with h | h
  · rw [max_eq_left h]
    have habs : z = |z| := (abs_of_nonneg h).symm
    rw [habs]
    simp only [abs_abs]
    nlinarith
  · rw [max_eq_right h]
    have habs : z = -|z| := by rw [abs_of_nonpos h, neg_neg]
    rw [habs]
    simp only [abs_neg, abs_abs]
    nlinarith

end PartialBalayage.Maximal.Square
