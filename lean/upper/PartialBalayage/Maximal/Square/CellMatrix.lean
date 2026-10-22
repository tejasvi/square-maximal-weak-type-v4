/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.LocalCoefficientRange

/-!
# Actual bicubic coefficients from finite rational matrices

Checking the sixteen entries of a finite matrix identifies every actual cell coefficient:
all coefficients outside the matrix vanish by the genuine spline's degree bound.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- A finite rational bicubic matrix extended by zero to all natural degrees. -/
def cellMatrixExtension (c : Fin 4 → Fin 4 → ℚ) (a b : ℕ) : ℚ :=
  if ha : a < 4 then if hb : b < 4 then c ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

/-- The sixteen ordinary checks identify every genuine bicubic cell coefficient. -/
theorem correctionCellCoefficient_eq_matrix (k l : ℤ) (c : Fin 4 → Fin 4 → ℚ)
    (hc : ∀ a b : Fin 4, correctionCellCoefficient k l a b = c a b) (a b : ℕ) :
    correctionCellCoefficient k l a b = cellMatrixExtension c a b := by
  unfold cellMatrixExtension
  split_ifs with ha hb
  · exact hc ⟨a, ha⟩ ⟨b, hb⟩
  · exact correctionCellCoefficient_eq_zero_of_four_le_right k l a (by omega)
  · exact correctionCellCoefficient_eq_zero_of_four_le_left k l (by omega) b

end PartialBalayage.Maximal.Square
