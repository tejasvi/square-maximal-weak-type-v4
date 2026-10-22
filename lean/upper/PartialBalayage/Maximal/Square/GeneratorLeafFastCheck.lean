/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: R = 33/20, grid spacing 1/32, exponent -47/20; Bernstein rectangle lower bound. -/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafData
public import PartialBalayage.Maximal.Square.IncomingTailEvaluator

/-!
# Exact cached finite-tail arithmetic for actual generator leaves

The Horner evaluator is proved equal to the genuine finite incoming-tail sums.
Consequently these faster rational calculations give exactly the same real
generator rectangle bound; no numerical value or analytic assumption is added.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square.GeneratorLeafData

/-- Exact Horner-based value interval for the actual finite radial model. -/
def fastValueInterval (D : GeneratorLeafData) : RationalInterval :=
  (D.radialRoot.radiusPower.scale generatorIntrinsicLower).add
    (RationalInterval.point (2 * generatorRadiusInterval.lower *
      (incomingTailValue D.terms (D.radialRoot.radius / (33 / 20)) +
        incomingEvenTailValue D.terms (((D.baseU - D.baseV) / 32) / (33 / 20)))))

/-- Exact Horner-based radius derivative interval. -/
def fastRadiusDerivativeInterval (D : GeneratorLeafData) : RationalInterval :=
  (D.radialRoot.derivativePower.scale ((-47 / 20) * generatorIntrinsicLower)).add
    (RationalInterval.point (2 * generatorRadiusInterval.lower / (33 / 20) *
      incomingTailDerivative D.terms (D.radialRoot.radius / (33 / 20))))

/-- Exact Horner-based signed-difference derivative interval. -/
def fastDifferenceDerivativeInterval (D : GeneratorLeafData) : RationalInterval :=
  RationalInterval.point (2 * generatorRadiusInterval.lower / (33 / 20) *
    incomingEvenTailDerivative D.terms (((D.baseU - D.baseV) / 32) / (33 / 20)))

/-- Horner evaluation preserves the actual finite-model value interval exactly. -/
theorem fastValueInterval_eq (D : GeneratorLeafData) :
    D.fastValueInterval =
      D.plane.valueInterval generatorIntrinsicLower generatorRadiusInterval.lower (33 / 20) := by
  simp only [fastValueInterval, RadialGeneratorPlaneData.valueInterval, plane,
    GeneratorRadialRootData.plane, incomingTailValue_eq, incomingEvenTailValue_eq]

/-- Horner evaluation preserves the actual finite-model radius derivative exactly. -/
theorem fastRadiusDerivativeInterval_eq (D : GeneratorLeafData) :
    D.fastRadiusDerivativeInterval =
      D.plane.radiusDerivativeInterval generatorIntrinsicLower generatorRadiusInterval.lower
        (33 / 20) := by
  simp only [fastRadiusDerivativeInterval, RadialGeneratorPlaneData.radiusDerivativeInterval,
    plane, GeneratorRadialRootData.plane, incomingTailDerivative_eq]

/-- Horner evaluation preserves the actual signed-difference derivative exactly. -/
theorem fastDifferenceDerivativeInterval_eq (D : GeneratorLeafData) :
    D.fastDifferenceDerivativeInterval =
      D.plane.differenceDerivativeInterval generatorRadiusInterval.lower (33 / 20) := by
  simp only [fastDifferenceDerivativeInterval,
    RadialGeneratorPlaneData.differenceDerivativeInterval, plane,
    GeneratorRadialRootData.plane, incomingEvenTailDerivative_eq]

/-- Exact three-coefficient tangent intervals using the proved cached finite sums. -/
def fastRadialIntervals (D : GeneratorLeafData) (p : RectangleIndex) : RationalInterval :=
  let gu := (D.fastRadiusDerivativeInterval.add D.fastDifferenceDerivativeInterval).scale
    (generatorRadialCoefficient / 32)
  let gv := (D.fastRadiusDerivativeInterval.add
    (D.fastDifferenceDerivativeInterval.scale (-1))).scale (generatorRadialCoefficient / 32)
  if p = (0, 0) then
    (D.fastValueInterval.scale generatorRadialCoefficient).add
      ((gu.scale ((D.coordinateU.cubic.cell.val : ℚ) + D.coordinateU.cubic.midpoint -
        D.baseU)).add
        (gv.scale ((D.coordinateV.cubic.cell.val : ℚ) + D.coordinateV.cubic.midpoint -
          D.baseV)))
  else if p = (1, 0) then gu
  else if p = (0, 1) then gv
  else RationalInterval.point 0

/-- The actual tangent coefficients agree exactly with their fast computations. -/
theorem fastRadialIntervals_eq (D : GeneratorLeafData) :
    D.fastRadialIntervals =
      generatorCheckedRadialIntervals D.coordinateU D.coordinateV D.plane D.baseU D.baseV := by
  funext p
  simp only [fastRadialIntervals, generatorCheckedRadialIntervals, radialRectangleIntervals,
    fastValueInterval_eq, fastRadiusDerivativeInterval_eq, fastDifferenceDerivativeInterval_eq]

/-- Exact fast evaluation of the same genuine generator rectangle lower bound. -/
def fastLowerBound (D : GeneratorLeafData) : ℚ :=
  bernsteinIntervalLower
      (generatorCombinedIntervals D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers splineGeneratorFactorInterval
        D.fastRadialIntervals) D.rectangle.radius -
    splineGeneratorFactorInterval.upper *
      generatorApproximationError D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers

/-- The faster computation is precisely the actual source lower bound. -/
theorem fastLowerBound_eq (D : GeneratorLeafData) : D.fastLowerBound = D.lowerBound := by
  simp only [fastLowerBound, lowerBound, generatorCheckedRectangleLower, fastRadialIntervals_eq]

/-- Ordinary exact metadata and fast arithmetic suffice for actual leaf validity. -/
theorem numericalValid_of_fast {D : GeneratorLeafData} (hD : D.MetadataValid)
    (hL : 0 < D.fastLowerBound) : D.NumericalValid := by
  exact ⟨hD, by simpa only [fastLowerBound_eq] using hL⟩

end PartialBalayage.Maximal.Square.GeneratorLeafData
