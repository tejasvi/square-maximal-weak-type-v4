/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40; the exterior positivity statement becomes nonnegativity wherever the kernel vanishes. -/
module

public import PartialBalayage.Maximal.Square.KernelPuncturedSource
public import PartialBalayage.Maximal.Square.DiamondGeneratorExterior
public import PartialBalayage.Maximal.Square.ExteriorGeneratorPositivity

/-!
# The full source density is the actual original generator

At points off the axes and support boundary, genuine coordinate integrability permits
adding the radial and spline integrals. The true exterior kernel positivity therefore
applies to exactly the density appearing in the punctured distributional identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem coordinateLine_kernel_add {x : E} (hx₀ : x 0 ≠ 0) (hx₁ : x 1 ≠ 0)
    (i : Fin 2) : coordinateLine euclideanKernel x i =
      fun t ↦ coordinateLine (fun y : E ↦ radialBase (y 0) (y 1)) x i t +
        coordinateLine (fun y : E ↦ splineCorrection (y 0) (y 1)) x i t := by
  funext t
  unfold coordinateLine euclideanKernel
  have hother : (x + t • EuclideanSpace.basisFun (Fin 2) ℝ i) (1 - i) ≠ 0 := by
    fin_cases i
    · change (x + t • EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 ≠ 0
      simpa [EuclideanSpace.basisFun_apply] using hx₁
    · change (x + t • EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 ≠ 0
      simpa [EuclideanSpace.basisFun_apply] using hx₀
  have he : ¬ ((x + t • EuclideanSpace.basisFun (Fin 2) ℝ i) 0 = 0 ∧
      (x + t • EuclideanSpace.basisFun (Fin 2) ℝ i) 1 = 0) := by
    rintro ⟨h₀, h₁⟩
    fin_cases i <;> simp_all
  simp only [kernel, ite_eq_right he]

private theorem integrableOn_radialCoordinateSecondDifference {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius) (i : Fin 2) :
    IntegrableOn (fun t ↦ t ^ (-1 - (47 / 40 : ℝ)) • stableSecondDifference
      (coordinateLine (fun y : E ↦ radialBase (y 0) (y 1)) x i) t) (Ioi 0) := by
  have hi := (integrableOn_coordinateDiamondSecondDifference hx₀ hx₁ hr i).const_mul
    radialCoefficient
  apply hi.congr
  filter_upwards with t
  simp only [stableSecondDifference, coordinateLine,
    radialBase_eq_coefficient_diamondTruncatedPower, smul_eq_mul]
  ring

private theorem stableGeneratorIntegral_kernel_add {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius) (i : Fin 2) :
    stableGeneratorIntegral (47 / 40) (coordinateLine euclideanKernel x i) =
      stableGeneratorIntegral (47 / 40)
        (coordinateLine (fun y : E ↦ radialBase (y 0) (y 1)) x i) +
      stableGeneratorIntegral (47 / 40)
        (coordinateLine (fun y : E ↦ splineCorrection (y 0) (y 1)) x i) := by
  have hrint := integrableOn_radialCoordinateSecondDifference hx₀ hx₁ hr i
  have hsint := integrableOn_coordinateStableSecondDifference
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num) contDiff_splineCorrection
    hasCompactSupport_splineCorrection x i
  rw [coordinateLine_kernel_add hx₀ hx₁ i]
  unfold stableGeneratorIntegral
  calc
    _ = ∫ t in Ioi 0,
        t ^ (-1 - (47 / 40 : ℝ)) • stableSecondDifference
          (coordinateLine (fun y : E ↦ radialBase (y 0) (y 1)) x i) t +
        t ^ (-1 - (47 / 40 : ℝ)) • stableSecondDifference
          (coordinateLine (fun y : E ↦ splineCorrection (y 0) (y 1)) x i) t := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [stableSecondDifference, smul_eq_mul]
      ring
    _ = _ := integral_add hrint hsint

/-- The punctured density is the original normalized generator off exceptional lines. -/
theorem coordinateStableGenerator_euclideanKernel_eq_density {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius) :
    coordinateStableGenerator (47 / 40) euclideanKernel x = squareGeneratorDensity x := by
  have he : coordinateStableGenerator (47 / 40) euclideanKernel x =
      coordinateStableGenerator (47 / 40) (fun y : E ↦ radialBase (y 0) (y 1)) x +
        coordinateStableGenerator (47 / 40) (fun y : E ↦ splineCorrection (y 0) (y 1)) x := by
    unfold coordinateStableGenerator
    simp_rw [stableGeneratorIntegral_kernel_add hx₀ hx₁ hr]
    rw [Finset.sum_add_distrib, mul_add]
  rw [he, coordinateStableGenerator_radialBase]
  rfl

/-- The actual source density is nonnegative wherever the kernel vanishes. -/
theorem squareGeneratorDensity_nonneg_of_kernel_zero [KernelMajorizationFacts] {x : E}
    (hx₀ : x 0 ≠ 0) (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius)
    (hK : euclideanKernel x = 0) : 0 ≤ squareGeneratorDensity x := by
  rw [← coordinateStableGenerator_euclideanKernel_eq_density hx₀ hx₁ hr]
  exact coordinateStableGenerator_euclideanKernel_nonneg_of_zero x hK

end PartialBalayage.Maximal.Square
