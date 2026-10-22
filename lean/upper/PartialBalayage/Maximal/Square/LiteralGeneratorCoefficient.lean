/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCoefficientRange
public import PartialBalayage.Maximal.Square.Data.RepresentativeCoefficientMatrix

/-!
# Actual generator coefficients from the proved finite lookup

The finite lookup is already proved equal to the original orbit coefficient
function. Substitution gives a computable rational expression for every actual
generator cubic coefficient, with no additional numerical hypothesis.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The actual twenty-term expression using the proved finite coefficient lookup. -/
def literalGeneratorCellCoefficient (cell k : ℤ) (b : ℕ) : ℚ :=
  ∑ q : Fin 5, splineFourthDifferenceCoefficient q * ∑ j ∈ Finset.range 4,
    literalRepresentativeCoefficient
      (max (k + 2 - (q.val : ℤ)).natAbs (cell - 1 + j).natAbs)
      (min (k + 2 - (q.val : ℤ)).natAbs (cell - 1 + j).natAbs) *
        cubicSplineCellCoefficient (1 - j) b

/-- Every cached expression is the genuine signed generator cubic coefficient. -/
theorem splineGeneratorCellCoefficient_eq_literal (cell k : ℤ) (b : ℕ) :
    splineGeneratorCellCoefficient cell k b = literalGeneratorCellCoefficient cell k b := by
  rw [splineGeneratorCellCoefficient_eq_local_range]
  unfold localGeneratorCellCoefficient literalGeneratorCellCoefficient
  simp_rw [representativeCoefficient_eq_literal]

end PartialBalayage.Maximal.Square
