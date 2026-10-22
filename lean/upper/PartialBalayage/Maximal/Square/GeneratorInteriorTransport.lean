/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40, grid spacing 1/32, interior bound 264/5. -/
module

public import PartialBalayage.Maximal.Square.KernelSourceInteriorFormula
public import PartialBalayage.Maximal.Square.FirstGeneratorLeaf

/-!
# The certificate's interior expression is the actual source density

The original physical generator, its sixteen-fold spatial scale, and the named actual
interior density agree exactly. The original sign symmetry retains both absolute spatial
coordinates, so the genuine rectangle positivity can apply to the full source density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The named literal interior expression has the actual original generator normalization. -/
theorem kernelGeneratorAt_scaled_eq_generatorInteriorDensity {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 264 / 5) :
    kernelGeneratorAt (47 / 40) (u / 32) (v / 32) =
      stableNormalization (47 / 40) * generatorInteriorDensity u v :=
  kernelGeneratorAt_scaled_eq_interior hu hv hr

/-- The actual punctured source equals the certificate's full density on its exact spatial scale. -/
theorem squareGeneratorDensity_eq_generatorInteriorDensity {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) < supportRadius) :
    squareGeneratorDensity x = stableNormalization (47 / 40) *
      generatorInteriorDensity (32 * |x 0|) (32 * |x 1|) := by
  have hu : 0 < |x 0| := abs_pos.mpr hx₀
  have hv : 0 < |x 1| := abs_pos.mpr hx₁
  have hrscaled : 32 * |x 0| + 32 * |x 1| < 264 / 5 := by
    norm_num only [supportRadius, diamondRadius] at hr
    linarith
  have he := kernelGeneratorAt_scaled_eq_generatorInteriorDensity
    (mul_pos (by norm_num) hu) (mul_pos (by norm_num) hv) hrscaled
  rw [show 32 * |x 0| / 32 = |x 0| by ring,
    show 32 * |x 1| / 32 = |x 1| by ring] at he
  rw [squareGeneratorDensity_eq_kernelGeneratorAt_abs hx₀ hx₁ (ne_of_lt hr)]
  exact he

end PartialBalayage.Maximal.Square
