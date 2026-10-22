/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.HarmonicCenterLimits
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial integrability of harmonic tangents

After multiplication by the polar Jacobian, the singular harmonic tangent agrees on positive
radii with a continuous function: a polynomial combination in every dimension except two,
and a combination of `r` and `r * log r` in dimension two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Constants

namespace PartialBalayage

/-- The continuous extension of a harmonic tangent multiplied by the polar Jacobian. -/
def harmonicWeightedExtension (n : ℕ) (a q d r : ℝ) : ℝ :=
  if n = 2 then (q - a * d * Real.log a) * r + 2 * a * d * (r * Real.log r)
  else (q - a * d / (1 - (n : ℝ) / 2)) * r ^ (n - 1) +
    a * d * a ^ ((n : ℝ) / 2 - 1) / (1 - (n : ℝ) / 2) * r

/-- The weighted extension is continuous even at the center. -/
theorem continuous_harmonicWeightedExtension (n : ℕ) (a q d : ℝ) :
    Continuous (harmonicWeightedExtension n a q d) := by
  by_cases hn : n = 2
  · unfold harmonicWeightedExtension
    simp only [ite_eq_left hn]
    exact (continuous_id.const_mul _).add (Real.continuous_mul_log.const_mul _)
  · unfold harmonicWeightedExtension
    simp only [ite_eq_right hn]
    fun_prop

/-- The explicit continuous extension agrees with the actual tangent at every positive radius. -/
theorem harmonicRadialTangent_mul_pow_pred (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (q d : ℝ) :
    harmonicRadialTangent n a q d r * r ^ (n - 1) =
      harmonicWeightedExtension n a q d r := by
  by_cases hn2 : n = 2
  · subst n
    have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
    norm_num only [harmonicRadialTangent, harmonicWeightedExtension, harmonicCoordinate,
      Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num, ite_true, Nat.reduceSub, pow_one]
    rw [Real.log_div hr2 ha.ne', Real.log_pow]
    ring
  · have hβ : (n : ℝ) / 2 ≠ 1 := by
      intro h
      apply hn2
      exact_mod_cast (show (n : ℝ) = 2 by linarith)
    have hpow : (r ^ 2) ^ (1 - (n : ℝ) / 2) = r ^ ((2 : ℝ) - n) := by
      rw [← Real.rpow_two r, ← Real.rpow_mul hr.le]
      congr 1
      ring
    have hprod : r ^ ((2 : ℝ) - n) * r ^ (n - 1) = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub hn, Nat.cast_one,
        show (2 : ℝ) - n + (n - 1) = 1 by ring, Real.rpow_one]
    have hc : (r ^ 2 / a) ^ (1 - (n : ℝ) / 2) * r ^ (n - 1) =
        a ^ ((n : ℝ) / 2 - 1) * r := by
      rw [Real.div_rpow (sq_nonneg r) ha.le, hpow, div_mul_eq_mul_div, hprod,
        div_eq_mul_inv, ← Real.rpow_neg ha.le,
        show -(1 - (n : ℝ) / 2) = (n : ℝ) / 2 - 1 by ring]
      ring
    simp only [harmonicRadialTangent, harmonicWeightedExtension, harmonicCoordinate,
      ite_eq_right hn2, ite_eq_right hβ]
    calc
      _ = (q - a * d / (1 - (n : ℝ) / 2)) * r ^ (n - 1) +
          a * d / (1 - (n : ℝ) / 2) *
            ((r ^ 2 / a) ^ (1 - (n : ℝ) / 2) * r ^ (n - 1)) := by ring
      _ = _ := by rw [hc]; ring

/-- A continuous spherical factor preserves integrability of the weighted inner tangent. -/
theorem integrableOn_harmonicRadialTangent_mul_pow_mul (n : ℕ) (hn : 1 ≤ n)
    {a b : ℝ} (ha : 0 < a) (q d : ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) :
    IntegrableOn (fun r ↦ harmonicRadialTangent n a q d r * r ^ (n - 1) * G r)
      (Ioo 0 b) := by
  have hc : IntegrableOn (fun r ↦ harmonicWeightedExtension n a q d r * G r) (Icc 0 b) :=
    ((continuous_harmonicWeightedExtension n a q d).mul hG).continuousOn
      |>.integrableOn_compact isCompact_Icc
  apply (hc.mono_set Ioo_subset_Icc_self).congr_fun
  · intro r hr
    exact (congrArg (fun t : ℝ ↦ t * G r)
      (harmonicRadialTangent_mul_pow_pred n hn ha hr.1 q d)).symm
  · exact measurableSet_Ioo

end PartialBalayage
