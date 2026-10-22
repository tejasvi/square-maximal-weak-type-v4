/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: our kernel's mass formula and target 359123/100000. -/
module

public import PartialBalayage.Maximal.Square.RadialMass
public import PartialBalayage.Maximal.Square.SplineMass
public import PartialBalayage.Maximal.Square.MassCoefficientBound

/-!
# Exact mass and strict numerical bound for the actual square kernel

These conclusions concern the original integrable kernel with all 9,045
signed tensor coefficients (1,181 coefficient classes). The separate generator and majorization proofs
are still needed to turn its mass into the square maximal-operator bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PartialBalayage.Maximal.Square

/-- The exact Lebesgue mass of the actual article kernel. -/
theorem integral_euclideanKernel :
    (∫ x, euclideanKernel x) = 94 / 33 * radialCoefficient * supportRadius ^ (33 / 40 : ℝ) +
      (coefficientSum : ℝ) / 1024 := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin 2), radialBase (x 0) (x 1) +
        splineCorrection (x 0) (x 1) := integral_congr_ae euclideanKernel_ae_eq
    _ = _ := by rw [integral_add integrable_radialBase integrable_splineCorrection,
      integral_radialBase, integral_splineCorrection]

/-- Half the actual kernel mass is strictly less than our certificate's bound. -/
theorem half_integral_euclideanKernel_lt :
    (∫ x, euclideanKernel x) / 2 < 359123 / 100000 := by
  rw [integral_euclideanKernel]
  exact half_mass_coefficient_lt

end PartialBalayage.Maximal.Square
