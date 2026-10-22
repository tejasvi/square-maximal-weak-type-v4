/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RectanglePolynomialBound
public import PartialBalayage.Maximal.Square.TaylorIntervalEnclosure

/-!
# Genuine finite spline Taylor assembly

Actual finite tensor products expand into the sixteen centered polynomial coefficients.
The total Taylor error follows from the proved error of each absolute power multiplied
by the absolute bound of its genuine spline coefficient polynomial.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Evaluation of an actual centered cubic coefficient vector. -/
def centeredCubic (c : Fin 4 → ℝ) (x : ℝ) : ℝ := ∑ i, c i * x ^ i.val

theorem rectanglePolynomial_add (c d : RectangleIndex → ℝ) (x y : ℝ) :
    rectanglePolynomial (fun p ↦ c p + d p) x y =
      rectanglePolynomial c x y + rectanglePolynomial d x y := by
  simp only [rectanglePolynomial, add_mul, Finset.sum_add_distrib]

theorem rectanglePolynomial_scale (a : ℝ) (c : RectangleIndex → ℝ) (x y : ℝ) :
    rectanglePolynomial (fun p ↦ a * c p) x y = a * rectanglePolynomial c x y := by
  simp only [rectanglePolynomial, mul_assoc, Finset.mul_sum]

theorem rectanglePolynomial_sum {ι : Type*} (s : Finset ι)
    (c : ι → RectangleIndex → ℝ) (x y : ℝ) :
    rectanglePolynomial (fun p ↦ ∑ z ∈ s, c z p) x y =
      ∑ z ∈ s, rectanglePolynomial (c z) x y := by
  simp only [rectanglePolynomial, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Genuine tensor products have the stated sixteen actual centered coefficients. -/
theorem rectanglePolynomial_tensor (c d : Fin 4 → ℝ) (x y : ℝ) :
    rectanglePolynomial (fun p ↦ c p.1 * d p.2) x y =
      centeredCubic c x * centeredCubic d y := by
  simp only [rectanglePolynomial, Fintype.sum_prod_type, centeredCubic]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Each genuine product error is bounded by the coefficient polynomial and Taylor error. -/
theorem abs_product_approximation_error_le {D H T M R : ℝ}
    (hD : |D| ≤ M) (hH : |H - T| ≤ R) : |D * H - D * T| ≤ M * R := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul hD hH (abs_nonneg _) ((abs_nonneg _).trans hD)

/-- The true finite sum error is the sum of the actual individual error bounds. -/
theorem abs_sum_product_approximation_error_le {ι : Type*} (s : Finset ι)
    (D H T M R : ι → ℝ) (hD : ∀ z ∈ s, |D z| ≤ M z)
    (hH : ∀ z ∈ s, |H z - T z| ≤ R z) :
    |(∑ z ∈ s, D z * H z) - ∑ z ∈ s, D z * T z| ≤ ∑ z ∈ s, M z * R z := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun z hz ↦ abs_product_approximation_error_le (hD z hz) (hH z hz)))

/-- Scaling the genuine finite approximation by a nonnegative generator factor. -/
theorem abs_scaled_sum_product_approximation_error_le {ι : Type*} (s : Finset ι)
    (D H T M R : ι → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hD : ∀ z ∈ s, |D z| ≤ M z) (hH : ∀ z ∈ s, |H z - T z| ≤ R z) :
    |σ * (∑ z ∈ s, D z * H z) - σ * ∑ z ∈ s, D z * T z| ≤
      σ * ∑ z ∈ s, M z * R z := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hσ]
  exact mul_le_mul_of_nonneg_left (abs_sum_product_approximation_error_le s D H T M R hD hH)
    hσ

end PartialBalayage.Maximal.Square
