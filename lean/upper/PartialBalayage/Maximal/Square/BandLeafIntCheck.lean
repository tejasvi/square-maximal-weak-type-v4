/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandLeaf
public import PartialBalayage.Maximal.Square.GeneratorLeafIntCheck

/-!
# The band leaf check with integer tensor sums

The rectangle lower bound of a band leaf uses the same spline approximation as an interior leaf;
its tensor intervals and error come from the integer sums of `GeneratorLeafIntCheck`, and the
result equals `BandLeafData.lowerBound` exactly.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

namespace BandLeafData

variable (C : BandConstants)

/-- The band leaf lower bound computed with integer tensor sums. -/
def intLowerBound (D : BandLeafData) : ℚ :=
  bernsteinIntervalLower
      (fun p ↦ (splineGeneratorFactorInterval.nonnegMul (intApproxOf D.coordinateU D.coordinateV p)).add
        (RationalInterval.point (radialCoefficients C D p))) D.rectangle.radius -
    splineGeneratorFactorInterval.upper * intErrorOf D.coordinateU D.coordinateV

theorem intLowerBound_eq (D : BandLeafData) : intLowerBound C D = lowerBound C D := by
  unfold intLowerBound lowerBound
  rw [← sparseGeneratorCombinedIntervals_eq, ← sparseGeneratorApproximationError_eq, intErrorOf_eq]
  unfold sparseGeneratorCombinedIntervals
  congr 2
  funext p
  rw [intApproxOf_eq]

theorem isValid_of_int {D : BandLeafData} (hM : D.MetadataValid) (hL : 0 < intLowerBound C D) :
    IsValid C D :=
  ⟨hM, intLowerBound_eq C D ▸ hL⟩

end BandLeafData

end PartialBalayage.Maximal.Square
