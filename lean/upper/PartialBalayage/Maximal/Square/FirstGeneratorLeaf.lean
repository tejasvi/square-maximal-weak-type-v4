/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: only the density definition is kept (grid spacing 1/32, alpha = 47/40); the single first-rectangle check and its data module are not used. -/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleLower
public import PartialBalayage.Maximal.Square.RadialModelLower
public import PartialBalayage.Maximal.Square.Data.GeneratorScaleData

/-!
# The explicit strict-interior source density

The normalized strict-interior source density in the unit-grid coordinates.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The explicit normalized strict-interior source density in the unit-grid coordinates. -/
def generatorInteriorDensity (u v : ℝ) : ℝ :=
  radialCoefficient *
    (squareIntrinsicConstant * ((u + v) / 32) ^ (-47 / 20 : ℝ) +
      radialIncomingTail (47 / 40) supportRadius ((u + v) / 32) ((u - v) / 32)) +
    splineGeneratorFactor * splineGeneratorCorrectionPower u v

end PartialBalayage.Maximal.Square
