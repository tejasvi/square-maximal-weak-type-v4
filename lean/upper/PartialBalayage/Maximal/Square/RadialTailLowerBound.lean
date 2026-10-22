/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20); the finite polynomial uses the rounded coefficients and is compared with the exact one. -/
module

public import PartialBalayage.Maximal.Square.RadialTailKernel

/-!
# Genuine finite incoming-tail lower bounds

The actual improper incoming integral dominates every finite rational
polynomial obtained by integrating its genuine binomial truncation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The exact finite rational incoming-tail polynomial used by the arithmetic certificate. -/
def radialIncomingPolynomial (R r d : ℝ) (N : ℕ) : ℝ :=
  R ^ (-47 / 20 : ℝ) * ∑ n ∈ Finset.range N, (radialIncomingCoefficient n : ℝ) *
    (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n)

/-- The same finite polynomial with the exact integrated coefficients. -/
def radialIncomingExactPolynomial (R r d : ℝ) (N : ℕ) : ℝ :=
  R ^ (-47 / 20 : ℝ) * ∑ n ∈ Finset.range N, (radialIncomingExactCoefficient n : ℝ) *
    (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n)

/-- An individual finite lower monomial of the actual incoming integrand. -/
def radialIncomingMonomial (R r d : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  (radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n) *
    ((R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ)) * q ^ (-87 / 40 - (n : ℝ)))

theorem integrableOn_radialIncomingMonomial {R : ℝ} (hR : 0 < R) (r d : ℝ)
    (n : ℕ) : IntegrableOn (radialIncomingMonomial R r d n) (Ioi R) := by
  have hi := (integrableOn_radial_tail_moment hR (by norm_num : (0 : ℝ) < 47 / 40)
    (Nat.cast_nonneg n)).const_mul
      ((radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n))
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro q _
  change (radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n) *
    ((R ^ (-(47 / 40 : ℝ)) - q ^ (-(47 / 40 : ℝ))) *
      q ^ (-(47 / 40 : ℝ) - 1 - (n : ℝ))) = radialIncomingMonomial R r d n q
  simp only [radialIncomingMonomial, show -(47 / 40 : ℝ) = -47 / 40 by ring,
    show (-47 / 40 : ℝ) - 1 - (n : ℝ) = -87 / 40 - (n : ℝ) by ring]

/-- The actual integral of each incoming monomial equals its exact rational coefficient. -/
theorem integral_radialIncomingMonomial {R : ℝ} (hR : 0 < R) (r d : ℝ) (n : ℕ) :
    (∫ q in Ioi R, radialIncomingMonomial R r d n q) =
      R ^ (-47 / 20 : ℝ) * (radialIncomingExactCoefficient n : ℝ) *
        (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n) := by
  unfold radialIncomingMonomial
  rw [integral_const_mul]
  have hm := integral_radial_tail_moment hR (by norm_num : (0 : ℝ) < 47 / 40)
    (Nat.cast_nonneg n)
  have he : (-47 / 40 : ℝ) - 1 - (n : ℝ) = -87 / 40 - (n : ℝ) := by ring
  have he₂ : -2 * (47 / 40 : ℝ) - (n : ℝ) = -47 / 20 - (n : ℝ) := by ring
  simp only [show -(47 / 40 : ℝ) = -47 / 40 by ring, he, he₂,
    show 2 * (47 / 40 : ℝ) = 47 / 20 by ring] at hm
  rw [hm]
  simp only [radialIncomingExactCoefficient, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]
  have hp : R ^ (-47 / 20 : ℝ) *
      (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n) =
      (2 * r ^ n + d ^ n + (-d) ^ n) * R ^ (-47 / 20 - (n : ℝ)) := by
    calc
      _ = 2 * (R ^ (-47 / 20 : ℝ) * (r / R) ^ n) +
          R ^ (-47 / 20 : ℝ) * (d / R) ^ n +
          R ^ (-47 / 20 : ℝ) * (-d / R) ^ n := by ring
      _ = _ := by
        rw [rpow_mul_div_nat hR r, rpow_mul_div_nat hR d, rpow_mul_div_nat hR (-d)]
        ring
  calc
    _ = ((radialTailBinomialCoefficient n : ℝ) * (47 / 40) /
        ((47 / 40 + (n : ℝ)) * (47 / 20 + (n : ℝ)))) *
        ((2 * r ^ n + d ^ n + (-d) ^ n) * R ^ (-47 / 20 - (n : ℝ))) := by ring
    _ = ((radialTailBinomialCoefficient n : ℝ) * (47 / 40) /
        ((47 / 40 + (n : ℝ)) * (47 / 20 + (n : ℝ)))) *
        (R ^ (-47 / 20 : ℝ) *
          (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n)) := by rw [hp]
    _ = _ := by ring

/-- Integrating the genuine kernel lower bound proves the actual finite tail inequality. -/
theorem radialIncomingExactPolynomial_le_tail {R r d : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrR : r < R) (hdR : |d| < R) (N : ℕ) :
    radialIncomingExactPolynomial R r d N ≤ radialIncomingTail (47 / 40) R r d := by
  have hi : IntegrableOn
      (fun q ↦ ∑ n ∈ Finset.range N, radialIncomingMonomial R r d n q) (Ioi R) :=
    integrable_finsetSum _ (fun n _ ↦ integrableOn_radialIncomingMonomial hR r d n)
  have hK := integrableOn_radialIncomingTail_integrand hR hrR hdR
  have hle := integral_mono_ae hi hK (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    have hqpos := hR.trans hq
    have hw : 0 ≤ R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ) :=
      sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR hq.le (by norm_num))
    have hb := mul_le_mul_of_nonneg_left
      (radialIncomingPowerKernel_ge_sum hqpos hr (hrR.trans hq) (hdR.trans hq) N) hw
    convert hb using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    unfold radialIncomingMonomial
    ring)
  rw [integral_finsetSum _ (fun n _ ↦ integrableOn_radialIncomingMonomial hR r d n)] at hle
  simp only [integral_radialIncomingMonomial hR r d] at hle
  simp only [mul_assoc] at hle
  rw [← Finset.mul_sum] at hle
  rw [radialIncomingTail_eq_integral_powerKernel]
  exact hle

/-- The rounded coefficients give a smaller polynomial, since every monomial is nonnegative. -/
theorem radialIncomingPolynomial_le_exact {R r d : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (N : ℕ) :
    radialIncomingPolynomial R r d N ≤ radialIncomingExactPolynomial R r d N := by
  unfold radialIncomingPolynomial radialIncomingExactPolynomial
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hR.le _)
  apply Finset.sum_le_sum
  intro n _
  have hm : 0 ≤ 2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n := by
    have h₁ : 0 ≤ (r / R) ^ n := pow_nonneg (div_nonneg hr hR.le) n
    have h₂ : 0 ≤ (d / R) ^ n + (-d / R) ^ n := by
      simpa only [neg_div] using add_pow_neg_nonneg (d / R) n
    linarith
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast radialIncomingCoefficient_le_exact n) hm

/-- Integrating the genuine kernel lower bound proves the actual finite tail inequality. -/
theorem radialIncomingPolynomial_le_tail {R r d : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hrR : r < R) (hdR : |d| < R) (N : ℕ) :
    radialIncomingPolynomial R r d N ≤ radialIncomingTail (47 / 40) R r d :=
  (radialIncomingPolynomial_le_exact hR hr N).trans
    (radialIncomingExactPolynomial_le_tail hR hr hrR hdR N)

end PartialBalayage.Maximal.Square
