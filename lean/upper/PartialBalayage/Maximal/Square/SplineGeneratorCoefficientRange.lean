/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCoefficients
public import PartialBalayage.Maximal.Square.LocalCoefficientRange

/-!
# Transparent actual generator-cell coefficient arithmetic

The exact integer support interval contains four translated splines. Rewriting
it as a range of length four gives the literal twenty-term rational expression
for each actual generator cubic coefficient.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The actual generator coefficient as a transparent twenty-term rational expression. -/
def localGeneratorCellCoefficient (cell k : ℤ) (b : ℕ) : ℚ :=
  ∑ q : Fin 5, splineFourthDifferenceCoefficient q * ∑ j ∈ Finset.range 4,
    representativeCoefficient
      (max (k + 2 - (q.val : ℤ)).natAbs (cell - 1 + j).natAbs)
      (min (k + 2 - (q.val : ℤ)).natAbs (cell - 1 + j).natAbs) *
        cubicSplineCellCoefficient (1 - j) b

/-- The transparent twenty-term rational expression is the genuine generator coefficient. -/
theorem splineGeneratorCellCoefficient_eq_local_range (cell k : ℤ) (b : ℕ) :
    splineGeneratorCellCoefficient cell k b = localGeneratorCellCoefficient cell k b := by
  unfold splineGeneratorCellCoefficient
  simp_rw [splineCoefficient_eq_representative]
  have hc : cell + 2 + 1 - (cell - 1) = 4 := by ring
  simp only [Int.Icc_eq_finset_map, hc, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  unfold localGeneratorCellCoefficient
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  ring

end PartialBalayage.Maximal.Square
