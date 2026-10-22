/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RealBetaIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Actual positive beta-prime integrals

The genuine injective substitution t ↦ t/(1+t) transforms the positive
half-line integral into its convergent ordinary beta integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual bijection from the positive half-line to the open unit interval. -/
def betaPrimeChange (t : ℝ) : ℝ := t / (1 + t)

theorem hasDerivAt_betaPrimeChange {t : ℝ} (ht : 0 < t) :
    HasDerivAt betaPrimeChange (1 / (1 + t) ^ 2) t := by
  have hne : 1 + t ≠ 0 := ne_of_gt (by linarith)
  convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) hne using 1
  · rfl
  · simp only [id_eq]
    field_simp [hne]
    ring

theorem injOn_betaPrimeChange : InjOn betaPrimeChange (Ioi 0) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hnx : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hny : 1 + y ≠ 0 := ne_of_gt (by linarith)
  have h := (div_eq_div_iff hnx hny).mp hxy
  nlinarith

theorem image_betaPrimeChange : betaPrimeChange '' Ioi 0 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htpos : 0 < t := ht
    have htp : 0 < 1 + t := by linarith
    exact ⟨div_pos ht htp, (div_lt_one htp).mpr (by linarith)⟩
  · intro hy
    have hd : 0 < 1 - y := by linarith [hy.2]
    refine ⟨y / (1 - y), div_pos hy.1 hd, ?_⟩
    unfold betaPrimeChange
    field_simp
    ring

/-- The true Jacobian gives the actual beta-prime density. -/
theorem betaPrimeChange_density {t : ℝ} (ht : 0 < t) (u v : ℝ) :
    |1 / (1 + t) ^ 2| * realBetaIntegrand u v (betaPrimeChange t) =
      t ^ (u - 1) * (1 + t) ^ (-(u + v)) := by
  have htp : 0 < 1 + t := by linarith
  have he : 1 - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  have hp : (1 + t) ^ (-2 : ℝ) = ((1 + t) ^ 2)⁻¹ := by
    rw [Real.rpow_neg htp.le, Real.rpow_two]
  rw [abs_of_nonneg (by positivity), realBetaIntegrand, betaPrimeChange, he,
    Real.div_rpow ht.le htp.le, Real.div_rpow zero_le_one htp.le, Real.one_rpow]
  simp only [div_eq_mul_inv, one_mul, ← Real.rpow_neg htp.le]
  rw [← hp]
  calc
    _ = t ^ (u - 1) * ((1 + t) ^ (-(u - 1)) *
        (1 + t) ^ (-(v - 1)) * (1 + t) ^ (-2 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add htp, ← Real.rpow_add htp]
      congr 2
      ring

/-- The actual positive beta-prime density is integrable. -/
theorem integrableOn_betaPrime {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t : ℝ ↦ t ^ (u - 1) * (1 + t) ^ (-(u + v))) (Ioi 0) := by
  have hi := (intervalIntegrable_realBetaIntegrand hu hv).1.mono_set Ioo_subset_Ioc_self
  rw [← image_betaPrimeChange] at hi
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t ht ↦ (hasDerivAt_betaPrimeChange ht).hasDerivWithinAt)
      injOn_betaPrimeChange (realBetaIntegrand u v)).mp hi
  apply IntegrableOn.congr_fun hj _ measurableSet_Ioi
  intro t ht
  exact betaPrimeChange_density ht u v

/-- The genuine positive half-line beta-prime integral equals its actual beta integral. -/
theorem integral_betaPrime (u v : ℝ) :
    (∫ t in Ioi (0 : ℝ), t ^ (u - 1) * (1 + t) ^ (-(u + v))) =
      realBetaIntegral u v := by
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht ↦ (hasDerivAt_betaPrimeChange ht).hasDerivWithinAt)
      injOn_betaPrimeChange (realBetaIntegrand u v)
  rw [image_betaPrimeChange] at hj
  rw [realBetaIntegral, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, hj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (betaPrimeChange_density ht u v).symm

end PartialBalayage.Maximal.Square
