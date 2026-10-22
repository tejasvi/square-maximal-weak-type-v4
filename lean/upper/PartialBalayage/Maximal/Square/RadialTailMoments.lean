/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20); the incoming coefficients used by the certificate are dyadic lower bounds (2^-96, rounded recurrence) of the exact integrated coefficients, which keep their own name. -/
module

public import PartialBalayage.Maximal.Square.RadialTailBinomial
public import PartialBalayage.Maximal.Square.RoundedSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact genuine incoming-tail moments

Actual improper power integrals give the rational coefficients of every
incoming-tail monomial. No supplied certificate is used for this analytic
identification.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The genuine incoming-tail monomial is integrable for all positive orders and radii. -/
theorem integrableOn_radial_tail_moment {R α k : ℝ} (hR : 0 < R) (hα : 0 < α)
    (hk : 0 ≤ k) :
    IntegrableOn (fun q : ℝ ↦ (R ^ (-α) - q ^ (-α)) * q ^ (-α - 1 - k)) (Ioi R) := by
  have hi₁ := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -α - 1 - k < -1) hR).const_mul (R ^ (-α))
  have hi₂ := integrableOn_Ioi_rpow_of_lt
    (by linarith : -2 * α - 1 - k < -1) hR
  apply IntegrableOn.congr_fun (hi₁.sub hi₂) _ measurableSet_Ioi
  intro q hq
  change R ^ (-α) * q ^ (-α - 1 - k) - q ^ (-2 * α - 1 - k) =
    (R ^ (-α) - q ^ (-α)) * q ^ (-α - 1 - k)
  symm
  have hqpos : 0 < q := hR.trans hq
  rw [sub_mul, ← Real.rpow_add hqpos]
  congr 2
  ring

/-- Each true improper incoming-tail moment has its exact rational coefficient. -/
theorem integral_radial_tail_moment {R α k : ℝ} (hR : 0 < R) (hα : 0 < α)
    (hk : 0 ≤ k) :
    (∫ q : ℝ in Ioi R, (R ^ (-α) - q ^ (-α)) * q ^ (-α - 1 - k)) =
      α / ((α + k) * (2 * α + k)) * R ^ (-2 * α - k) := by
  have hi₁ := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -α - 1 - k < -1) hR).const_mul (R ^ (-α))
  have hi₂ := integrableOn_Ioi_rpow_of_lt
    (by linarith : -2 * α - 1 - k < -1) hR
  have he : (∫ q : ℝ in Ioi R, (R ^ (-α) - q ^ (-α)) * q ^ (-α - 1 - k)) =
      ∫ q : ℝ in Ioi R, R ^ (-α) * q ^ (-α - 1 - k) - q ^ (-2 * α - 1 - k) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    change (R ^ (-α) - q ^ (-α)) * q ^ (-α - 1 - k) =
      R ^ (-α) * q ^ (-α - 1 - k) - q ^ (-2 * α - 1 - k)
    have hqpos : 0 < q := hR.trans hq
    rw [sub_mul, ← Real.rpow_add hqpos]
    congr 2
    ring
  rw [he, integral_sub hi₁ hi₂, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -α - 1 - k < -1) hR,
    integral_Ioi_rpow_of_lt (by linarith : -2 * α - 1 - k < -1) hR]
  rw [show -α - 1 - k + 1 = -(α + k) by ring,
    show -2 * α - 1 - k + 1 = -(2 * α + k) by ring]
  simp only [div_neg, neg_div, neg_neg]
  rw [← mul_div_assoc]
  have hp : R ^ (-α) * R ^ (-(α + k)) = R ^ (-2 * α - k) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  rw [hp, show -(2 * α + k) = -2 * α - k by ring]
  have h₁ : α + k ≠ 0 := ne_of_gt (by linarith)
  have h₂ : 2 * α + k ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Exact rational coefficients after integrating the actual incoming power series. -/
def radialIncomingExactCoefficient (n : ℕ) : ℚ :=
  radialTailBinomialCoefficient n * (47 / 40) / ((47 / 40 + n) * (47 / 20 + n))

theorem radialIncomingExactCoefficient_nonneg (n : ℕ) : 0 ≤ radialIncomingExactCoefficient n := by
  unfold radialIncomingExactCoefficient
  exact div_nonneg (mul_nonneg (radialTailBinomialCoefficient_nonneg n) (by norm_num))
    (by positivity)

theorem exactRising_eq_radialTailBinomialCoefficient (n : ℕ) :
    exactRising (87 / 40) n = radialTailBinomialCoefficient n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exactRising, radialTailBinomialCoefficient, ih]

/-- The rounded incoming coefficient computed from a rounded binomial factor `b`. -/
def radialIncomingRoundedTerm (n : ℕ) (b : ℚ) : ℚ :=
  roundDown 96 (b * (47 / 40) / ((47 / 40 + n) * (47 / 20 + n)))

/-- Dyadic lower bounds (`2^-96`) of the integrated incoming coefficients. -/
def radialIncomingCoefficient (n : ℕ) : ℚ :=
  radialIncomingRoundedTerm n (roundedRising 96 (87 / 40) n)

theorem radialIncomingCoefficient_nonneg (n : ℕ) : 0 ≤ radialIncomingCoefficient n := by
  unfold radialIncomingCoefficient radialIncomingRoundedTerm
  exact roundDown_nonneg 96 (div_nonneg (mul_nonneg
    (roundedRising_nonneg 96 (by norm_num) n) (by norm_num)) (by positivity))

theorem radialIncomingCoefficient_le_exact (n : ℕ) :
    radialIncomingCoefficient n ≤ radialIncomingExactCoefficient n := by
  unfold radialIncomingCoefficient radialIncomingRoundedTerm radialIncomingExactCoefficient
  refine (roundDown_le 96 _).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  rw [← exactRising_eq_radialTailBinomialCoefficient]
  exact roundedRising_le 96 (by norm_num) n

end PartialBalayage.Maximal.Square
