/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the strict bound 359123/100000 of our kernel instead of 452/125. -/
module

public import PartialBalayage.Maximal.Square.SquarePositiveSource
public import PartialBalayage.Maximal.Square.SquareWeakBoundOfSourcePositivity

/-!
# The strict square maximal bound

The actual comparison kernel, positive generator source, stable obstacle,
and all-input transfer give the table's exact strict bound for centered squares.
-/

@[expose] public section

namespace PartialBalayage.Maximal

/-- The centered square maximal operator has weak-type constant strictly below 3.59123. -/
theorem square_weakTypeConstant_lt_3_59123 :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (359123 / 100000 : ℝ) :=
  Square.cubeWeakTypeConstant_lt_of_square_source_nonneg
    Square.ae_squareGeneratorDensity_nonneg

end PartialBalayage.Maximal
