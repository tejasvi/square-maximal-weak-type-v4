/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: constants of our kernel: S = 2119593029/10^9 (lower bound of the intrinsic constant), c = 1977601376167/2^40, R = 33/20, grid spacing 1/32, interior bound u + v < 264/5; Bernstein rectangle lower bound. -/
module

public import PartialBalayage.Maximal.Square.FirstGeneratorLeaf
public import PartialBalayage.Maximal.Square.GeneratorCoordinateData
public import PartialBalayage.Maximal.Square.RadialRectangleTangent

/-!
# Sound checked generator rectangles

This connects genuine coordinate data, radial root data, and an exact positive
rational rectangle bound to the actual strict-interior source expression. The
concrete finite partition discharges each rational check separately.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The proved rational lower constant for the actual intrinsic radial source. -/
def generatorIntrinsicLower : ℚ := 2119593029 / 1000000000

/-- The exact coefficient of the actual truncated homogeneous radial kernel. -/
def generatorRadialCoefficient : ℚ := 1977601376167 / 1099511627776

/-- Radial tangent intervals at the midpoint of two actual coordinate intervals. -/
def generatorCheckedRadialIntervals (U V : GeneratorCoordinateData)
    (D : RadialGeneratorPlaneData) (bu bv : ℚ) : RectangleIndex → RationalInterval :=
  radialRectangleIntervals D generatorIntrinsicLower generatorRadiusInterval.lower
    (33 / 20) generatorRadialCoefficient
    ((U.cubic.cell.val : ℚ) + U.cubic.midpoint)
    ((V.cubic.cell.val : ℚ) + V.cubic.midpoint) bu bv

/-- Exact lower bound obtained from the actual finite approximations on this rectangle. -/
def generatorCheckedRectangleLower (U V : GeneratorCoordinateData)
    (D : RadialGeneratorPlaneData) (bu bv δ : ℚ) : ℚ :=
  bernsteinIntervalLower
      (generatorCombinedIntervals U.cubic V.cubic U.powers V.powers
        splineGeneratorFactorInterval (generatorCheckedRadialIntervals U V D bu bv)) δ -
    splineGeneratorFactorInterval.upper *
      generatorApproximationError U.cubic V.cubic U.powers V.powers

/-- A genuine checked rectangle is pointwise positive on its strict-support interior. -/
theorem generatorInteriorDensity_pos_of_checked_rectangle
    {U V : GeneratorCoordinateData} (hU : U.IsValid) (hV : V.IsValid)
    {D : RadialGeneratorPlaneData} (hD : D.IsValid) {bu bv δ : ℚ}
    (hDr : D.radius = (bu + bv) / 32) (hDd : D.difference = (bu - bv) / 32)
    (hδU : U.cubic.width / 2 = δ) (hδV : V.cubic.width / 2 = δ)
    (hLower : 0 < generatorCheckedRectangleLower U V D bu bv δ)
    {t s : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (htu₀ : (U.cubic.lower : ℝ) ≤ t)
    (htu₁ : t ≤ ((U.cubic.lower + U.cubic.width : ℚ) : ℝ))
    (hsv₀ : (V.cubic.lower : ℝ) ≤ s)
    (hsv₁ : s ≤ ((V.cubic.lower + V.cubic.width : ℚ) : ℝ))
    (hu : 0 < (U.cubic.cell.val : ℝ) + t)
    (hv : 0 < (V.cubic.cell.val : ℝ) + s)
    (hr : (U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s) < 264 / 5) :
    0 < generatorInteriorDensity
      ((U.cubic.cell.val : ℝ) + t) ((V.cubic.cell.val : ℝ) + s) := by
  let a := generatorRadialCoefficient
  let S := generatorIntrinsicLower
  let ρ := generatorRadiusInterval.lower
  let uc : ℚ := (U.cubic.cell.val : ℚ) + U.cubic.midpoint
  let vc : ℚ := (V.cubic.cell.val : ℚ) + V.cubic.midpoint
  let rI := generatorCheckedRadialIntervals U V D bu bv
  let rc := radialRectangleCoefficients D S ρ (33 / 20) a uc vc bu bv
  have hRI (p : RectangleIndex) : (rI p).Contains (rc p) :=
    radialRectangleIntervals_contains hD S ρ (33 / 20) a uc vc bu bv p
  have hLow := generatorCombinedIntervals_lower hU.1 hV.1 U.powers_valid V.powers_valid
    hU.2.1 hV.2.1 hU.2.2 hV.2.2 splineGeneratorFactorInterval_contains
    splineGeneratorFactorInterval_lower_nonneg hRI hδU hδV
    ht₀ ht₁ hs₀ hs₁ htu₀ htu₁ hsv₀ hsv₁
  have hLow' : (generatorCheckedRectangleLower U V D bu bv δ : ℝ) ≤
      splineGeneratorFactor * splineGeneratorCorrectionPower
        ((U.cubic.cell.val : ℝ) + t) ((V.cubic.cell.val : ℝ) + s) +
      rectanglePolynomial rc
        (t - (U.cubic.midpoint : ℝ)) (s - (V.cubic.midpoint : ℝ)) := hLow
  have hpoly := radialRectanglePolynomial_eq D S ρ (33 / 20) a uc vc bu bv hDr hDd
    ((U.cubic.cell.val : ℝ) + t) ((V.cubic.cell.val : ℝ) + s)
  have hx : (U.cubic.cell.val : ℝ) + t - (uc : ℝ) = t - (U.cubic.midpoint : ℝ) := by
    simp only [uc, Rat.cast_add, Rat.cast_natCast]
    ring
  have hy : (V.cubic.cell.val : ℝ) + s - (vc : ℝ) = s - (V.cubic.midpoint : ℝ) := by
    simp only [vc, Rat.cast_add, Rat.cast_natCast]
    ring
  rw [hx, hy] at hpoly
  have hS₀ : (0 : ℝ) ≤ (S : ℝ) := by norm_num [S, generatorIntrinsicLower]
  have hρ₀ : (0 : ℝ) ≤ (ρ : ℝ) := by norm_num [ρ, generatorRadiusInterval]
  have hSu : (S : ℝ) ≤ squareIntrinsicConstant := by
    simpa only [S, generatorIntrinsicLower, Rat.cast_div, Rat.cast_ofNat] using
      squareIntrinsicConstant_ge
  have hρu : (ρ : ℝ) ≤ (33 / 20 : ℝ) ^ (-47 / 20 : ℝ) := by
    simpa only [ρ, supportRadius] using generatorRadiusInterval_contains.1
  have hrad : 0 < ((U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s)) / 32 := by
    linarith
  have hradR : ((U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s)) / 32 < 33 / 20 := by
    linarith
  have hdiff : |((U.cubic.cell.val : ℝ) + t - ((V.cubic.cell.val : ℝ) + s)) / 32| < 33 / 20 := by
    apply abs_lt.mpr
    constructor <;> linarith
  have htangent := radialGeneratorLowerModel_tangent_le_analytic
    (S := (S : ℝ)) (ρ := (ρ : ℝ)) (R := (33 / 20 : ℝ))
    (r₀ := (D.radius : ℝ)) (d₀ := (D.difference : ℝ))
    (r := ((U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s)) / 32)
    (d := ((U.cubic.cell.val : ℝ) + t - ((V.cubic.cell.val : ℝ) + s)) / 32)
    D.terms hS₀ hρ₀ (by norm_num : (0 : ℝ) < 33 / 20)
    (by exact_mod_cast hD.1) hrad hradR hdiff hSu hρu
  have ha : (0 : ℝ) ≤ (a : ℝ) := by norm_num [a, generatorRadialCoefficient]
  have hplane : rectanglePolynomial rc
      (t - (U.cubic.midpoint : ℝ)) (s - (V.cubic.midpoint : ℝ)) ≤
      radialCoefficient *
        (squareIntrinsicConstant *
            (((U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s)) / 32) ^
              (-47 / 20 : ℝ) +
          radialIncomingTail (47 / 40) supportRadius
            (((U.cubic.cell.val : ℝ) + t + ((V.cubic.cell.val : ℝ) + s)) / 32)
            (((U.cubic.cell.val : ℝ) + t - ((V.cubic.cell.val : ℝ) + s)) / 32)) := by
    rw [hpoly]
    simpa only [a, generatorRadialCoefficient, S, radialCoefficient, supportRadius,
      Rat.cast_div, Rat.cast_ofNat] using mul_le_mul_of_nonneg_left htangent ha
  have hLB : (0 : ℝ) < (generatorCheckedRectangleLower U V D bu bv δ : ℝ) := by
    exact_mod_cast hLower
  have h := hLB.trans_le (hLow'.trans (add_le_add le_rfl hplane))
  simpa only [generatorInteriorDensity, add_comm] using h

end PartialBalayage.Maximal.Square
