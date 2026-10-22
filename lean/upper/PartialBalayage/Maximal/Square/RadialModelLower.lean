/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20). -/
module

public import PartialBalayage.Maximal.Square.RadialModelTangent
public import PartialBalayage.Maximal.Square.RadialTailLowerBound
public import PartialBalayage.Maximal.Square.GeneratorConstantBound

/-!
# The finite certificate model bounds the genuine incoming-tail expression

Parity identifies the actual integrated polynomial with its positive-radius and
even-difference parts. Downward rational factors preserve its lower bound. The
genuine convex tangent therefore bounds the actual analytic generator expression.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

theorem radialPositivePolynomial_nonneg (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ radialPositivePolynomial N x := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by exact_mod_cast radialIncomingCoefficient_nonneg n) (pow_nonneg hx n)

theorem radialEvenPolynomial_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ radialEvenPolynomial N x := by
  apply Finset.sum_nonneg
  intro n hn
  by_cases he : Even n
  · simp only [radialEvenCoefficient, ite_eq_left he]
    exact mul_nonneg (by exact_mod_cast radialIncomingCoefficient_nonneg n) (he.pow_nonneg x)
  · simp only [radialEvenCoefficient, ite_eq_right he, Rat.cast_zero, zero_mul]
    exact le_rfl

/-- The finite actual tail is exactly the certificate's positive and even polynomials. -/
theorem radialIncomingPolynomial_eq_positive_even (R r d : ℝ) (N : ℕ) :
    radialIncomingPolynomial R r d N = 2 * R ^ (-47 / 20 : ℝ) *
      (radialPositivePolynomial N (r / R) + radialEvenPolynomial N (d / R)) := by
  have ht (n : ℕ) : (radialIncomingCoefficient n : ℝ) *
      (2 * (r / R) ^ n + (d / R) ^ n + (-d / R) ^ n) =
        2 * ((radialIncomingCoefficient n : ℝ) * (r / R) ^ n +
          (radialEvenCoefficient n : ℝ) * (d / R) ^ n) := by
    rw [neg_div]
    by_cases he : Even n
    · rw [he.neg_pow, radialEvenCoefficient, ite_eq_left he]
      ring
    · have ho := Nat.not_even_iff_odd.mp he
      rw [ho.neg_pow, radialEvenCoefficient, ite_eq_right he]
      simp only [Rat.cast_zero, zero_mul]
      ring
  unfold radialIncomingPolynomial
  simp_rw [ht]
  unfold radialPositivePolynomial radialEvenPolynomial
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  ring

/-- Downward factors give a true lower bound for the actual radial analytic expression. -/
theorem radialGeneratorLowerModel_le_analytic {S ρ R r d : ℝ} (N : ℕ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (hdR : |d| < R)
    (hS : S ≤ squareIntrinsicConstant) (hρ : ρ ≤ R ^ (-47 / 20 : ℝ)) :
    radialGeneratorLowerModel S ρ R N r d ≤
      squareIntrinsicConstant * r ^ (-47 / 20 : ℝ) +
        radialIncomingTail (47 / 40 : ℝ) R r d := by
  have hP : 0 ≤ radialPositivePolynomial N (r / R) + radialEvenPolynomial N (d / R) :=
    add_nonneg (radialPositivePolynomial_nonneg N (div_nonneg hr.le hR.le))
      (radialEvenPolynomial_nonneg N _)
  have h₁ := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hr.le (-47 / 20))
  have h₂ := mul_le_mul_of_nonneg_right hρ hP
  have ht := radialIncomingPolynomial_le_tail hR hr.le hrR hdR N
  rw [radialIncomingPolynomial_eq_positive_even] at ht
  unfold radialGeneratorLowerModel
  nlinarith

/-- The actual certificate tangent plane bounds the genuine radial generator expression. -/
theorem radialGeneratorLowerModel_tangent_le_analytic {S ρ R r₀ r d₀ d : ℝ} (N : ℕ)
    (hS₀ : 0 ≤ S) (hρ₀ : 0 ≤ ρ) (hR : 0 < R) (hr₀ : 0 < r₀)
    (hr : 0 < r) (hrR : r < R) (hdR : |d| < R)
    (hS : S ≤ squareIntrinsicConstant) (hρ : ρ ≤ R ^ (-47 / 20 : ℝ)) :
    radialGeneratorLowerModel S ρ R N r₀ d₀ +
      radialGeneratorLowerModelDr S ρ R N r₀ * (r - r₀) +
      radialGeneratorLowerModelDd ρ R N d₀ * (d - d₀) ≤
        squareIntrinsicConstant * r ^ (-47 / 20 : ℝ) +
          radialIncomingTail (47 / 40 : ℝ) R r d :=
  (radialGeneratorLowerModel_tangent N hS₀ hρ₀ hR hr₀ hr).trans
    (radialGeneratorLowerModel_le_analytic N hR hr hrR hdR hS hρ)

end PartialBalayage.Maximal.Square
