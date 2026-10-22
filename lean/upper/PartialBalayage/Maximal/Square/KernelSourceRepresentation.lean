/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorSymmetry

/-!
# Genuine source representation from product integrability

The actual two-coordinate generator pairs with compact C² tests whenever its original
source-side jump product is integrable. Both integrability and equality are retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem mul_coordinateStableGenerator_split (α : ℝ) (K φ : E → ℝ) :
    (fun x : E ↦ K x * coordinateStableGenerator α φ x) =
      fun x ↦ stableNormalization α *
        (K x * stableGeneratorIntegral α (coordinateLine φ x 0)) +
      stableNormalization α * (K x * stableGeneratorIntegral α (coordinateLine φ x 1)) := by
  funext x
  simp only [coordinateStableGenerator, Fin.sum_univ_two]
  ring

theorem integrable_mul_coordinateStableGenerator_of_products {α : ℝ} {K φ : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hi : ∀ i : Fin 2, Integrable (fun p : E × ℝ ↦
      K p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α)) :
    Integrable (fun x : E ↦ K x * coordinateStableGenerator α φ x) := by
  rw [mul_coordinateStableGenerator_split]
  exact ((integrable_mul_coordinateGenerator_of_product hα0 hα2 0 (hi 0)).const_mul _).add
    ((integrable_mul_coordinateGenerator_of_product hα0 hα2 1 (hi 1)).const_mul _)

private theorem integral_mul_coordinateStableGenerator_split {α : ℝ} {K φ : E → ℝ}
    (hi : ∀ i : Fin 2, Integrable
      (fun x : E ↦ K x * stableGeneratorIntegral α (coordinateLine φ x i))) :
    (∫ x : E, K x * coordinateStableGenerator α φ x) =
      stableNormalization α * (∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x 0)) +
        stableNormalization α * ∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x 1)
        := by
  have h := integral_add ((hi 0).const_mul (stableNormalization α))
    ((hi 1).const_mul (stableNormalization α))
  rw [mul_coordinateStableGenerator_split]
  simpa only [Pi.add_apply, integral_const_mul] using h

/-- Genuine source-side Fubini gives the full two-coordinate distributional identity. -/
theorem integral_coordinateStableGenerator_source_representation {α : ℝ} {K φ : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hK : Integrable K volume)
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hi : ∀ i : Fin 2, Integrable (fun p : E × ℝ ↦
      φ p.1 * stableSecondDifference (coordinateLine K p.1 i) p.2)
        (spatialJumpMeasure α)) :
    (∫ x : E, K x * coordinateStableGenerator α φ x) =
      ∫ x : E, φ x * coordinateStableGenerator α K x := by
  have hp (i : Fin 2) := integrable_kernel_mul_coordinateSecondDifference
    hα0 hα2 hK φ hφ hs i
  rw [integral_mul_coordinateStableGenerator_split
    (fun i ↦ integrable_mul_coordinateGenerator_of_product hα0 hα2 i (hp i)),
    integral_mul_coordinateStableGenerator_split
      (fun i ↦ integrable_mul_coordinateGenerator_of_product hα0 hα2 i (hi i))]
  rw [integral_kernel_mul_coordinateGenerator_symmetry hα0 hα2 hK hφ hs 0 (hi 0),
    integral_kernel_mul_coordinateGenerator_symmetry hα0 hα2 hK hφ hs 1 (hi 1)]

end PartialBalayage.Maximal.Square
