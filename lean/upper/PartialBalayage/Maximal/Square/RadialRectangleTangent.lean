/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid spacing 1/32 (physical coordinates are the unit-grid coordinates divided by 32). -/
module

public import PartialBalayage.Maximal.Square.RadialPlaneInterval
public import PartialBalayage.Maximal.Square.RectanglePolynomialBound

/-!
# Genuine radial tangent coefficients in the rectangle coordinates

The physical coordinates are the unit-grid coordinates divided by thirty-two. The
actual tangent plane is expressed at any rational rectangle midpoint; signed
interval operations enclose its three nonzero coefficients exactly.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual three coefficients of the finite model's scaled unit-grid tangent plane. -/
def radialRectangleCoefficients (D : RadialGeneratorPlaneData) (S ρ R a : ℚ)
    (uc vc bu bv : ℚ) (p : RectangleIndex) : ℝ :=
  let F := radialGeneratorLowerModel S ρ R D.terms D.radius D.difference
  let Dr := radialGeneratorLowerModelDr S ρ R D.terms D.radius
  let Dd := radialGeneratorLowerModelDd ρ R D.terms D.difference
  let gu := (a : ℝ) / 32 * (Dr + Dd)
  let gv := (a : ℝ) / 32 * (Dr - Dd)
  if p = (0, 0) then (a : ℝ) * F + gu * (uc - bu : ℚ) + gv * (vc - bv : ℚ)
  else if p = (1, 0) then gu
  else if p = (0, 1) then gv
  else 0

/-- Exact rational intervals for the three actual coefficients of the same plane. -/
def radialRectangleIntervals (D : RadialGeneratorPlaneData) (S ρ R a : ℚ)
    (uc vc bu bv : ℚ) (p : RectangleIndex) : RationalInterval :=
  let Dr := D.radiusDerivativeInterval S ρ R
  let Dd := D.differenceDerivativeInterval ρ R
  let gu := (Dr.add Dd).scale (a / 32)
  let gv := (Dr.add (Dd.scale (-1))).scale (a / 32)
  if p = (0, 0) then
    ((D.valueInterval S ρ R).scale a).add
      ((gu.scale (uc - bu)).add (gv.scale (vc - bv)))
  else if p = (1, 0) then gu
  else if p = (0, 1) then gv
  else RationalInterval.point 0

/-- Exact root checks and signed interval operations enclose every actual tangent coefficient. -/
theorem radialRectangleIntervals_contains {D : RadialGeneratorPlaneData} (hD : D.IsValid)
    (S ρ R a uc vc bu bv : ℚ) (p : RectangleIndex) :
    (radialRectangleIntervals D S ρ R a uc vc bu bv p).Contains
      (radialRectangleCoefficients D S ρ R a uc vc bu bv p) := by
  have hF := D.valueInterval_contains hD S ρ R
  have hDr := D.radiusDerivativeInterval_contains hD S ρ R
  have hDd := D.differenceDerivativeInterval_contains ρ R
  have hgu := (hDr.add hDd).scale (a / 32)
  have hgv := (hDr.add (hDd.scale (-1))).scale (a / 32)
  have hC := (hF.scale a).add ((hgu.scale (uc - bu)).add (hgv.scale (vc - bv)))
  unfold radialRectangleIntervals radialRectangleCoefficients
  split_ifs
  · convert hC using 1
    push_cast
    ring
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using hgu
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one,
      neg_one_mul, ← sub_eq_add_neg] using hgv
  · simpa only [Rat.cast_zero] using RationalInterval.point_contains 0

/-- The actual three-coefficient polynomial is the true physical-coordinate tangent plane. -/
theorem radialRectanglePolynomial_eq (D : RadialGeneratorPlaneData)
    (S ρ R a uc vc bu bv : ℚ)
    (hr : D.radius = (bu + bv) / 32) (hd : D.difference = (bu - bv) / 32)
    (u v : ℝ) :
    rectanglePolynomial (radialRectangleCoefficients D S ρ R a uc vc bu bv)
      (u - (uc : ℝ)) (v - (vc : ℝ)) =
      (a : ℝ) *
        (radialGeneratorLowerModel S ρ R D.terms D.radius D.difference +
          radialGeneratorLowerModelDr S ρ R D.terms D.radius *
            ((u + v) / 32 - (D.radius : ℝ)) +
          radialGeneratorLowerModelDd ρ R D.terms D.difference *
            ((u - v) / 32 - (D.difference : ℝ))) := by
  norm_num [rectanglePolynomial, radialRectangleCoefficients,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  rw [hr, hd]
  push_cast
  ring

end PartialBalayage.Maximal.Square
