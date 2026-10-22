/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 145 signed knots (offset 72) and exponent 73/40 for our kernel; Bernstein
rectangle lower bound. -/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafFastCheck

/-!
# Exact sparse evaluation of genuine generator leaf bounds

Zero cubic coefficients and zero polynomial bounds are tested before looking up
their power intervals. The resulting sparse evaluation equals the existing
exact rational lower bound for every datum, without an additional certificate.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- A zero scalar is recognized before its power interval needs to be evaluated. -/
def sparseScaleInterval (q : ℚ) (I : RationalInterval) : RationalInterval :=
  if q = 0 then RationalInterval.point 0 else I.scale q

/-- Skipping a zero scalar preserves the exact signed interval operation. -/
theorem sparseScaleInterval_eq (q : ℚ) (I : RationalInterval) :
    sparseScaleInterval q I = I.scale q := by
  by_cases hq : q = 0
  · subst q
    simp [sparseScaleInterval, RationalInterval.scale, RationalInterval.point]
  · simp [sparseScaleInterval, hq]

/-- A zero coefficient is recognized before its Taylor error needs to be evaluated. -/
def sparseProduct (q r : ℚ) : ℚ := if q = 0 then 0 else q * r

/-- Skipping a zero coefficient preserves the exact rational product. -/
theorem sparseProduct_eq (q r : ℚ) : sparseProduct q r = q * r := by
  by_cases hq : q = 0 <;> simp [sparseProduct, hq]

/-- Exact tensor interval summation with zero coefficients skipped first. -/
def sparseGeneratorTensorIntervals {ι : Type*} (s : Finset ι)
    (D : ι → Fin 4 → ℚ) (H : ι → Fin 4 → RationalInterval)
    (p : RectangleIndex) : RationalInterval :=
  RationalInterval.sum s (fun z ↦ sparseScaleInterval (D z p.2) (H z p.1))

/-- The sparse tensor evaluator equals the actual finite tensor interval. -/
theorem sparseGeneratorTensorIntervals_eq {ι : Type*} (s : Finset ι)
    (D : ι → Fin 4 → ℚ) (H : ι → Fin 4 → RationalInterval)
    (p : RectangleIndex) :
    sparseGeneratorTensorIntervals s D H p = generatorTensorIntervals s D H p := by
  unfold sparseGeneratorTensorIntervals generatorTensorIntervals
  apply congrArg (RationalInterval.sum s)
  funext z
  exact sparseScaleInterval_eq _ _

/-- Both genuine tensor orientations with their zero coefficients skipped first. -/
def sparseGeneratorApproximationIntervals (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (p : RectangleIndex) : RationalInterval :=
  (sparseGeneratorTensorIntervals Finset.univ V.centered (fun k ↦ (H k).intervals) p).add
    (sparseGeneratorTensorIntervals Finset.univ U.centered
      (fun k ↦ (J k).intervals) (p.2, p.1))

/-- The sparse approximation intervals equal the actual approximation intervals. -/
theorem sparseGeneratorApproximationIntervals_eq (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (p : RectangleIndex) :
    sparseGeneratorApproximationIntervals U V H J p =
      generatorApproximationIntervals U V H J p := by
  simp only [sparseGeneratorApproximationIntervals, generatorApproximationIntervals,
    sparseGeneratorTensorIntervals_eq]

/-- The genuine error sum with zero polynomial bounds skipped first. -/
def sparseGeneratorApproximationError (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) : ℚ :=
  (∑ k, sparseProduct (V.bound k) (H k).error) +
    ∑ k, sparseProduct (U.bound k) (J k).error

/-- The sparse error sum equals the actual error sum. -/
theorem sparseGeneratorApproximationError_eq (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) :
    sparseGeneratorApproximationError U V H J = generatorApproximationError U V H J := by
  simp only [sparseGeneratorApproximationError, generatorApproximationError, sparseProduct_eq]

/-- The exact combined coefficient interval using sparse tensor summation. -/
def sparseGeneratorCombinedIntervals (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (S : RationalInterval)
    (R : RectangleIndex → RationalInterval) (p : RectangleIndex) : RationalInterval :=
  (S.nonnegMul (sparseGeneratorApproximationIntervals U V H J p)).add (R p)

/-- The sparse combined evaluator equals the actual coefficient intervals. -/
theorem sparseGeneratorCombinedIntervals_eq (U V : GeneratorCubicIntervalData)
    (H J : Fin 145 → GeneratorPowerTaylorData) (S : RationalInterval)
    (R : RectangleIndex → RationalInterval) :
    sparseGeneratorCombinedIntervals U V H J S R = generatorCombinedIntervals U V H J S R := by
  funext p
  simp only [sparseGeneratorCombinedIntervals, generatorCombinedIntervals,
    sparseGeneratorApproximationIntervals_eq]

namespace GeneratorLeafData

/-- Exact sparse computation of the same genuine source rectangle lower bound. -/
def sparseLowerBound (D : GeneratorLeafData) : ℚ :=
  bernsteinIntervalLower
      (sparseGeneratorCombinedIntervals D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers splineGeneratorFactorInterval
        D.fastRadialIntervals) D.rectangle.radius -
    splineGeneratorFactorInterval.upper *
      sparseGeneratorApproximationError D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers

/-- Sparse evaluation is exactly the frozen Horner-based rational bound. -/
theorem sparseLowerBound_eq_fastLowerBound (D : GeneratorLeafData) :
    D.sparseLowerBound = D.fastLowerBound := by
  simp only [sparseLowerBound, fastLowerBound, sparseGeneratorCombinedIntervals_eq,
    sparseGeneratorApproximationError_eq]

/-- Sparse evaluation is exactly the actual source rectangle lower bound. -/
theorem sparseLowerBound_eq_lowerBound (D : GeneratorLeafData) :
    D.sparseLowerBound = D.lowerBound :=
  (sparseLowerBound_eq_fastLowerBound D).trans (fastLowerBound_eq D)

/-- Exact metadata and the sparse rational check prove the actual leaf validity. -/
theorem numericalValid_of_sparse {D : GeneratorLeafData} (hD : D.MetadataValid)
    (hL : 0 < D.sparseLowerBound) : D.NumericalValid := by
  apply numericalValid_of_fast hD
  simpa only [sparseLowerBound_eq_fastLowerBound] using hL

end GeneratorLeafData

end PartialBalayage.Maximal.Square
