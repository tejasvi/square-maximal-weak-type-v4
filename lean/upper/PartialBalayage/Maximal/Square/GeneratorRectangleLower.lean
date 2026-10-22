/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 145 signed knots (offset 72) and exponent 73/40 for our kernel; the rectangle
polynomial is bounded below by its Bernstein coefficients (RectangleBernsteinBound). -/
module

public import PartialBalayage.Maximal.Square.GeneratorTensorApproximation
public import PartialBalayage.Maximal.Square.RectangleBernsteinBound

/-!
# Genuine rectangle lower bounds after a positive generator scale

The finite coefficient intervals and true approximation error give a lower bound
for the actual scaled spline generator plus any genuinely enclosed polynomial.
The radial tangent supplies that polynomial in the concrete certificate.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Exact interval coefficients for a scaled actual spline approximation plus a polynomial. -/
def generatorCombinedIntervals (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (S : RationalInterval)
    (R : RectangleIndex → RationalInterval) (p : RectangleIndex) : RationalInterval :=
  (S.nonnegMul (generatorApproximationIntervals U V H J p)).add (R p)

private theorem interval_midpoint_displacement {D : GeneratorCubicIntervalData} {t : ℝ}
    (ht₀ : (D.lower : ℝ) ≤ t) (ht₁ : t ≤ ((D.lower + D.width : ℚ) : ℝ)) :
    |t - (D.midpoint : ℝ)| ≤ ((D.width / 2 : ℚ) : ℝ) := by
  simp only [GeneratorCubicIntervalData.midpoint, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at *
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The checked interval lower bound applies to the actual scaled correction and polynomial. -/
theorem generatorCombinedIntervals_lower
    {U V : GeneratorCubicIntervalData} (hU : U.IsValid) (hV : V.IsValid)
    {H J : Fin 145 → GeneratorPowerTaylorData}
    (hH : ∀ k, (H k).IsValid) (hJ : ∀ k, (J k).IsValid)
    (hcH : ∀ k, (H k).center = (U.cell.val : ℚ) + U.midpoint - (generatorKnot k : ℚ))
    (hcJ : ∀ k, (J k).center = (V.cell.val : ℚ) + V.midpoint - (generatorKnot k : ℚ))
    (hrH : ∀ k, (H k).radius = U.width / 2)
    (hrJ : ∀ k, (J k).radius = V.width / 2)
    {S : RationalInterval} {σ : ℝ} (hS : S.Contains σ) (hS₀ : 0 ≤ S.lower)
    {R : RectangleIndex → RationalInterval} {r : RectangleIndex → ℝ}
    (hR : ∀ p, (R p).Contains (r p)) {δ : ℚ}
    (hδU : U.width / 2 = δ) (hδV : V.width / 2 = δ) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (htu₀ : (U.lower : ℝ) ≤ t) (htu₁ : t ≤ ((U.lower + U.width : ℚ) : ℝ))
    (hsv₀ : (V.lower : ℝ) ≤ s) (hsv₁ : s ≤ ((V.lower + V.width : ℚ) : ℝ)) :
    ((bernsteinIntervalLower (generatorCombinedIntervals U V H J S R) δ -
        S.upper * generatorApproximationError U V H J : ℚ) : ℝ) ≤
      σ * splineGeneratorCorrectionPower ((U.cell.val : ℝ) + t) ((V.cell.val : ℝ) + s) +
        rectanglePolynomial r (t - (U.midpoint : ℝ)) (s - (V.midpoint : ℝ)) := by
  have hσ : 0 ≤ σ := (show (0 : ℝ) ≤ (S.lower : ℝ) by exact_mod_cast hS₀).trans hS.1
  have hE : (0 : ℝ) ≤ (generatorApproximationError U V H J : ℝ) := by
    exact_mod_cast generatorApproximationError_nonneg hU hV hH hJ
  have hC (p : RectangleIndex) :
      (generatorCombinedIntervals U V H J S R p).Contains
        (σ * generatorApproximationCoefficients U V H J p + r p) := by
    exact (hS.nonnegMul (generatorApproximationIntervals_contains U V H J hH hJ p)
      hS₀).add (hR p)
  have ha := abs_generatorCorrectionPower_sub_approximation_le hU hV hH hJ hcH hcJ
    hrH hrJ ht₀ ht₁ hs₀ hs₁ htu₀ htu₁ hsv₀ hsv₁
  have hb := (mul_le_mul_of_nonneg_left ha hσ).trans
    (mul_le_mul_of_nonneg_right hS.2 hE)
  have hz :
      |(σ * splineGeneratorCorrectionPower ((U.cell.val : ℝ) + t) ((V.cell.val : ℝ) + s) +
          rectanglePolynomial r (t - (U.midpoint : ℝ)) (s - (V.midpoint : ℝ)) -
        rectanglePolynomial (fun p ↦ σ * generatorApproximationCoefficients U V H J p + r p)
          (t - (U.midpoint : ℝ)) (s - (V.midpoint : ℝ)))| ≤
      ((S.upper * generatorApproximationError U V H J : ℚ) : ℝ) := by
    rw [rectanglePolynomial_add, rectanglePolynomial_scale]
    have he (a b c : ℝ) : σ * a + c - (σ * b + c) = σ * (a - b) := by ring
    rw [he, abs_mul, abs_of_nonneg hσ]
    simpa only [Rat.cast_mul] using hb
  have hδ₀ : 0 ≤ δ := by
    rw [← hδU]
    exact div_nonneg hU.1.le (by norm_num)
  have hx := interval_midpoint_displacement htu₀ htu₁
  have hy := interval_midpoint_displacement hsv₀ hsv₁
  rw [hδU] at hx
  rw [hδV] at hy
  exact bernsteinIntervalLower_sub_error_le hC hδ₀ hx hy hz

end PartialBalayage.Maximal.Square
