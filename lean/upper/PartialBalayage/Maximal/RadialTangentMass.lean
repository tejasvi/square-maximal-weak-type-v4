/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PartialBalayage.Constants.Radial

/-!
# Exact mass of a radial harmonic tangent

The radial weight is `z^(β-1)`, with `β=n/2`. At the balanced outer joining radius the tangent's
weighted mass is exactly its height at the inner tangency point times `b^β/β`, independently of
the derivative there. This supplies the inner-mass term in the Poisson and heat table formulas.
It does not assert kernel majorization or a maximal inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage

/-- A radial harmonic tangent in squared-radius coordinates, outside the logarithmic case. -/
def powerHarmonicTangent (β a q d z : ℝ) : ℝ :=
  q + a * d / (1 - β) * ((z / a) ^ (1 - β) - 1)

/-- The logarithmic radial harmonic tangent in dimension two. -/
def logHarmonicTangent (a q d z : ℝ) : ℝ := q + a * d * Real.log (z / a)

private theorem weighted_power_cancel {β a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    (z / a) ^ (1 - β) * z ^ (β - 1) = a ^ (β - 1) := by
  rw [Real.div_rpow hz.le ha.le, div_mul_eq_mul_div,
    ← Real.rpow_add hz, show 1 - β + (β - 1) = 0 by ring, Real.rpow_zero,
    one_div, ← Real.rpow_neg ha.le]
  congr 1
  ring

private theorem weighted_powerHarmonicTangent {β a q d z : ℝ}
    (ha : 0 < a) (hz : 0 < z) :
    powerHarmonicTangent β a q d z * z ^ (β - 1) =
      (q - a * d / (1 - β)) * z ^ (β - 1) + a ^ β * d / (1 - β) := by
  have hcancel := weighted_power_cancel (β := β) ha hz
  have hapow : a * a ^ (β - 1) = a ^ β := by
    nth_rw 1 [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    ring
  unfold powerHarmonicTangent
  calc
    _ = (q - a * d / (1 - β)) * z ^ (β - 1) +
        a * d / (1 - β) * ((z / a) ^ (1 - β) * z ^ (β - 1)) := by ring
    _ = (q - a * d / (1 - β)) * z ^ (β - 1) + a ^ β * d / (1 - β) := by
      rw [hcancel, show a * d / (1 - β) * a ^ (β - 1) =
        (a * a ^ (β - 1)) * d / (1 - β) by ring, hapow]

/-- Exact weighted mass of a power harmonic tangent before imposing the balanced radius. -/
theorem integral_weighted_powerHarmonicTangent {β a b q d : ℝ}
    (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b) :
    (∫ z in 0..b, powerHarmonicTangent β a q d z * z ^ (β - 1)) =
      (q - a * d / (1 - β)) * b ^ β / β + a ^ β * d / (1 - β) * b := by
  have heq : (∫ z in 0..b, powerHarmonicTangent β a q d z * z ^ (β - 1)) =
      ∫ z in 0..b, (q - a * d / (1 - β)) * z ^ (β - 1) +
        a ^ β * d / (1 - β) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro z hz
    exact weighted_powerHarmonicTangent ha hz.1
  rw [heq, intervalIntegral.integral_add
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β - 1)).const_mul _)
    intervalIntegrable_const, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < β - 1)), intervalIntegral.integral_const]
  simp only [sub_add_cancel, Real.zero_rpow hβ.ne', sub_zero, smul_eq_mul]
  ring

/-- The balanced radius cancels the slope's contribution to the weighted tangent mass. -/
theorem integral_weighted_powerHarmonicTangent_of_balance {β a b q d : ℝ}
    (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (hbalance : (b / a) ^ (1 - β) = 1 / β) :
    (∫ z in 0..b, powerHarmonicTangent β a q d z * z ^ (β - 1)) = q * b ^ β / β := by
  have hc := weighted_power_cancel (β := β) ha hb
  rw [hbalance] at hc
  have hapow : a * a ^ (β - 1) = a ^ β := by
    nth_rw 1 [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have hbpow : b * b ^ (β - 1) = b ^ β := by
    nth_rw 1 [← Real.rpow_one b]
    rw [← Real.rpow_add hb]
    congr 1
    ring
  have hprod : a ^ β * b = a * b ^ β / β := by
    rw [← hapow, ← hc]
    calc
      _ = a * (b * b ^ (β - 1)) / β := by ring
      _ = a * b ^ β / β := by rw [hbpow]
  rw [integral_weighted_powerHarmonicTangent hβ ha hb]
  have hterm : a ^ β * d / (1 - β) * b = a * d / (1 - β) * (b ^ β / β) := by
    calc
      _ = (a ^ β * b) * d / (1 - β) := by ring
      _ = _ := by rw [hprod]; ring
  rw [hterm]
  ring

/-- Exact logarithmic tangent mass before imposing the balanced radius. -/
theorem integral_logHarmonicTangent {a b q d : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ z in 0..b, logHarmonicTangent a q d z) =
      b * (q + a * d * (Real.log (b / a) - 1)) := by
  have heq : (∫ z in 0..b, logHarmonicTangent a q d z) =
      ∫ z in 0..b, (q - a * d * Real.log a) + a * d * Real.log z := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro z hz
    unfold logHarmonicTangent
    rw [Real.log_div hz.1.ne' ha.ne']
    ring
  rw [heq, intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_log'.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_from_zero, Real.log_div hb.ne' ha.ne']
  simp only [sub_zero, smul_eq_mul]
  ring

/-- In the logarithmic case the balanced radius cancels the slope contribution. -/
theorem integral_logHarmonicTangent_of_balance {a b q d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hbalance : Real.log (b / a) = 1) :
    (∫ z in 0..b, logHarmonicTangent a q d z) = b * q := by
  rw [integral_logHarmonicTangent ha hb, hbalance]
  ring

/-- The article's radius ratio gives the claimed inner mass outside dimension two. -/
theorem integral_powerHarmonicTangent_rho (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≠ 2)
    {a : ℝ} (ha : 0 < a) (q d : ℝ) :
    (∫ z in 0..Constants.rho n * a,
      powerHarmonicTangent ((n : ℝ) / 2) a q d z * z ^ ((n : ℝ) / 2 - 1)) =
        2 * (Constants.rho n * a) ^ ((n : ℝ) / 2) * q / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : (Constants.rho n * a) / a = Constants.rho n := by
    exact mul_div_cancel_right₀ _ ha.ne'
  have hbalance : ((Constants.rho n * a) / a) ^ (1 - (n : ℝ) / 2) =
      1 / ((n : ℝ) / 2) := by
    rw [hratio, Constants.rho_rpow_one_sub_half n hn hn2]
    field_simp
  rw [integral_weighted_powerHarmonicTangent_of_balance (by positivity) ha
    (mul_pos (Constants.rho_pos n hn) ha) hbalance]
  ring

/-- The logarithmic dimension-two radius ratio gives the same inner-mass identity. -/
theorem integral_logHarmonicTangent_rho {a : ℝ} (ha : 0 < a) (q d : ℝ) :
    (∫ z in 0..Constants.rho 2 * a, logHarmonicTangent a q d z) =
      Constants.rho 2 * a * q := by
  apply integral_logHarmonicTangent_of_balance ha
    (mul_pos (Constants.rho_pos 2 (by norm_num)) ha)
  rw [mul_div_cancel_right₀ _ ha.ne', Constants.rho_two, Real.log_exp]

end PartialBalayage
