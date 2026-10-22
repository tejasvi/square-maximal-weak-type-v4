/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorDensity
public import PartialBalayage.Maximal.Square.DiamondBoundaryNull

/-!
# The actual generator and density agree almost everywhere

The original coordinate generator equals the genuine distributional density outside
the two null axes and the null diamond boundary. No generator certificate is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

/-- The actual full kernel generator is the density in the proved punctured source identity. -/
theorem ae_coordinateStableGenerator_euclideanKernel_eq_density :
    coordinateStableGenerator (47 / 40) euclideanKernel =ᵐ[volume] squareGeneratorDensity := by
  filter_upwards [ae_euclidean_coordinate_ne_zero 0, ae_euclidean_coordinate_ne_zero 1,
    ae_diamondRadius_ne supportRadius] with x hx₀ hx₁ hr
  exact coordinateStableGenerator_euclideanKernel_eq_density hx₀ hx₁ hr

end PartialBalayage.Maximal.Square
