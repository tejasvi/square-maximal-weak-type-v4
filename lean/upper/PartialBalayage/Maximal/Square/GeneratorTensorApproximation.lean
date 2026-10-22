/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 145 signed knots (offset 72) and exponent 73/40 for our kernel. -/
module

public import PartialBalayage.Maximal.Square.GeneratorCubicIntervalData
public import PartialBalayage.Maximal.Square.GeneratorPowerTaylorData
public import PartialBalayage.Maximal.Square.GeneratorFiniteKnots
public import PartialBalayage.Maximal.Square.IntervalFiniteSum

/-!
# Actual finite tensor approximation of the spline generator

Checked cubic interval data and checked Taylor families approximate both genuine
orientations of the signed spline correction. Their exact coefficient intervals
contain the actual centered coefficients, and their finite error sum bounds the
actual correction on the entire closed rectangle.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual centered tensor coefficients of both genuine approximation orientations. -/
def generatorApproximationCoefficients (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (p : RectangleIndex) : ℝ :=
  (∑ k, (H k).coefficients p.1 * (V.centered k p.2 : ℝ)) +
    ∑ k, (U.centered k p.1 : ℝ) * (J k).coefficients p.2

/-- Exact rational coefficient intervals for both actual tensor orientations. -/
def generatorApproximationIntervals (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (p : RectangleIndex) : RationalInterval :=
  (generatorTensorIntervals Finset.univ V.centered (fun k ↦ (H k).intervals) p).add
    (generatorTensorIntervals Finset.univ U.centered (fun k ↦ (J k).intervals) (p.2, p.1))

/-- The exact rational sum of genuine polynomial bounds times genuine Taylor errors. -/
def generatorApproximationError (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) : ℚ :=
  (∑ k, V.bound k * (H k).error) + ∑ k, U.bound k * (J k).error

/-- Checked Taylor data encloses every actual tensor coefficient. -/
theorem generatorApproximationIntervals_contains (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData)
    (hH : ∀ k, (H k).IsValid) (hJ : ∀ k, (J k).IsValid) (p : RectangleIndex) :
    (generatorApproximationIntervals U V H J p).Contains
      (generatorApproximationCoefficients U V H J p) := by
  have h₁ := generatorTensorIntervals_contains Finset.univ V.centered
    (fun k ↦ (H k).intervals) (fun k ↦ (H k).coefficients)
    (fun k _ ↦ (H k).intervals_contains (hH k)) p
  have h₂ := generatorTensorIntervals_contains Finset.univ U.centered
    (fun k ↦ (J k).intervals) (fun k ↦ (J k).coefficients)
    (fun k _ ↦ (J k).intervals_contains (hJ k)) (p.2, p.1)
  simpa [generatorApproximationIntervals, generatorApproximationCoefficients,
    mul_comm] using h₁.add h₂

/-- The actual total error enclosure is nonnegative. -/
theorem generatorApproximationError_nonneg {U V : GeneratorCubicIntervalData}
    (hU : U.IsValid) (hV : V.IsValid) {H J : Fin 145 → GeneratorPowerTaylorData}
    (hH : ∀ k, (H k).IsValid) (hJ : ∀ k, (J k).IsValid) :
    0 ≤ generatorApproximationError U V H J := by
  unfold generatorApproximationError
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro k hk
  · exact mul_nonneg (V.bound_nonneg hV k) ((H k).error_nonneg (hH k))
  · exact mul_nonneg (U.bound_nonneg hU k) ((J k).error_nonneg (hJ k))

private theorem cubic_interval_displacement {D : GeneratorCubicIntervalData} {s : ℝ}
    (hs₀ : (D.lower : ℝ) ≤ s) (hs₁ : s ≤ ((D.lower + D.width : ℚ) : ℝ)) :
    |s - (D.midpoint : ℝ)| ≤ ((D.width / 2 : ℚ) : ℝ) := by
  simp only [GeneratorCubicIntervalData.midpoint, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at *
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem shifted_power_polynomial {D : GeneratorCubicIntervalData}
    {H : Fin 145 → GeneratorPowerTaylorData}
    (hc : ∀ k, (H k).center = (D.cell.val : ℚ) + D.midpoint - (generatorKnot k : ℚ))
    (k : Fin 145) (t : ℝ) :
    (H k).polynomial ((D.cell.val : ℝ) + t - (generatorKnot k : ℝ)) =
      centeredCubic (H k).coefficients (t - (D.midpoint : ℝ)) := by
  unfold GeneratorPowerTaylorData.polynomial
  rw [hc k]
  push_cast
  congr 1
  ring

private theorem shifted_power_error {D : GeneratorCubicIntervalData}
    {H : Fin 145 → GeneratorPowerTaylorData} (hH : ∀ k, (H k).IsValid)
    (hc : ∀ k, (H k).center = (D.cell.val : ℚ) + D.midpoint - (generatorKnot k : ℚ))
    (hr : ∀ k, (H k).radius = D.width / 2) {t : ℝ}
    (ht₀ : (D.lower : ℝ) ≤ t) (ht₁ : t ≤ ((D.lower + D.width : ℚ) : ℝ))
    (k : Fin 145) :
    |(|(D.cell.val : ℝ) + t - (generatorKnot k : ℝ)| ^ (73 / 40 : ℝ) -
      (H k).polynomial ((D.cell.val : ℝ) + t - (generatorKnot k : ℝ)))| ≤
        ((H k).error : ℝ) := by
  apply (H k).error_bound (hH k)
  rw [hc k, hr k]
  push_cast
  have he : (D.cell.val : ℝ) + t - (generatorKnot k : ℝ) -
      ((D.cell.val : ℝ) + (D.midpoint : ℝ) - (generatorKnot k : ℝ)) =
        t - (D.midpoint : ℝ) := by ring
  rw [he]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using cubic_interval_displacement ht₀ ht₁

/-- The actual centered tensor polynomial equals the genuine finite approximation sum. -/
theorem generatorApproximationPolynomial_eq {U V : GeneratorCubicIntervalData}
    (hU : U.IsValid) (hV : V.IsValid) {H J : Fin 145 → GeneratorPowerTaylorData}
    (hcH : ∀ k, (H k).center = (U.cell.val : ℚ) + U.midpoint - (generatorKnot k : ℚ))
    (hcJ : ∀ k, (J k).center = (V.cell.val : ℚ) + V.midpoint - (generatorKnot k : ℚ))
    (t s : ℝ) :
    rectanglePolynomial (generatorApproximationCoefficients U V H J)
      (t - (U.midpoint : ℝ)) (s - (V.midpoint : ℝ)) =
      (∑ k, splineGeneratorCellPolynomial (V.cell.val : ℤ) (generatorKnot k) s *
        (H k).polynomial ((U.cell.val : ℝ) + t - (generatorKnot k : ℝ))) +
      ∑ k, splineGeneratorCellPolynomial (U.cell.val : ℤ) (generatorKnot k) t *
        (J k).polynomial ((V.cell.val : ℝ) + s - (generatorKnot k : ℝ)) := by
  unfold generatorApproximationCoefficients
  rw [rectanglePolynomial_add, rectanglePolynomial_sum, rectanglePolynomial_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [rectanglePolynomial_tensor (H k).coefficients
      (fun b ↦ (V.centered k b : ℝ))]
    rw [shifted_power_polynomial hcH]
    dsimp only [generatorKnot]
    rw [V.polynomial_eq hV k s]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    rw [rectanglePolynomial_tensor (fun b ↦ (U.centered k b : ℝ)) (J k).coefficients]
    rw [shifted_power_polynomial hcJ]
    dsimp only [generatorKnot]
    rw [U.polynomial_eq hU k t]

/-- The checked data bounds the actual full spline correction error on the closed rectangle. -/
theorem abs_generatorCorrectionPower_sub_approximation_le
    {U V : GeneratorCubicIntervalData} (hU : U.IsValid) (hV : V.IsValid)
    {H J : Fin 145 → GeneratorPowerTaylorData}
    (hH : ∀ k, (H k).IsValid) (hJ : ∀ k, (J k).IsValid)
    (hcH : ∀ k, (H k).center = (U.cell.val : ℚ) + U.midpoint - (generatorKnot k : ℚ))
    (hcJ : ∀ k, (J k).center = (V.cell.val : ℚ) + V.midpoint - (generatorKnot k : ℚ))
    (hrH : ∀ k, (H k).radius = U.width / 2)
    (hrJ : ∀ k, (J k).radius = V.width / 2) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (htu₀ : (U.lower : ℝ) ≤ t) (htu₁ : t ≤ ((U.lower + U.width : ℚ) : ℝ))
    (hsv₀ : (V.lower : ℝ) ≤ s) (hsv₁ : s ≤ ((V.lower + V.width : ℚ) : ℝ)) :
    |(splineGeneratorCorrectionPower ((U.cell.val : ℝ) + t) ((V.cell.val : ℝ) + s) -
      rectanglePolynomial (generatorApproximationCoefficients U V H J)
        (t - (U.midpoint : ℝ)) (s - (V.midpoint : ℝ)))| ≤
      (generatorApproximationError U V H J : ℝ) := by
  have h₁ := abs_sum_product_approximation_error_le Finset.univ
    (fun k ↦ splineGeneratorCellPolynomial (V.cell.val : ℤ) (generatorKnot k) s)
    (fun k ↦ |(U.cell.val : ℝ) + t - (generatorKnot k : ℝ)| ^ (73 / 40 : ℝ))
    (fun k ↦ (H k).polynomial ((U.cell.val : ℝ) + t - (generatorKnot k : ℝ)))
    (fun k ↦ (V.bound k : ℝ)) (fun k ↦ ((H k).error : ℝ))
    (fun k _ ↦ V.abs_polynomial_le hV k hsv₀ hsv₁)
    (fun k _ ↦ shifted_power_error hH hcH hrH htu₀ htu₁ k)
  have h₂ := abs_sum_product_approximation_error_le Finset.univ
    (fun k ↦ splineGeneratorCellPolynomial (U.cell.val : ℤ) (generatorKnot k) t)
    (fun k ↦ |(V.cell.val : ℝ) + s - (generatorKnot k : ℝ)| ^ (73 / 40 : ℝ))
    (fun k ↦ (J k).polynomial ((V.cell.val : ℝ) + s - (generatorKnot k : ℝ)))
    (fun k ↦ (U.bound k : ℝ)) (fun k ↦ ((J k).error : ℝ))
    (fun k _ ↦ U.abs_polynomial_le hU k htu₀ htu₁)
    (fun k _ ↦ shifted_power_error hJ hcJ hrJ hsv₀ hsv₁ k)
  rw [splineGeneratorCorrectionPower_eq_finite_knots U.cell V.cell ht₀ ht₁ hs₀ hs₁,
    generatorApproximationPolynomial_eq hU hV hcH hcJ]
  simp only [generatorApproximationError, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  have h := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  convert h using 1
  congr 1
  ring

end PartialBalayage.Maximal.Square
