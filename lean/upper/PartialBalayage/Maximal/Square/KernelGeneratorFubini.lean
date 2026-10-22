/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpGeneratorPairing
public import PartialBalayage.Maximal.Square.GeneratorMeasurability

/-!
# Actual singular-generator Fubini for integrable kernels

The compact test's uniform quadratic cancellation suffices for genuine product integrability
against every actual L¹ kernel. Square integrability of the kernel is unnecessary.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open PartialBalayage.Linear
open scoped NNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem coordinateSecondDifference_integrable_uniform {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (i : Fin 2) :
    ∃ C : ℝ, ∀ x : E,
      Integrable (stableSecondDifference (coordinateLine φ x i)) (stableJumpMeasure α) ∧
      (∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖ ∂stableJumpMeasure α) ≤ C := by
  obtain ⟨M, K, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds φ hφ hs
  refine ⟨stableNormalization α * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α), fun x ↦ ?_⟩
  have hm : AEStronglyMeasurable (stableSecondDifference (coordinateLine φ x i))
      (volume.restrict (Ioi 0)) :=
    (continuous_stableSecondDifference (hd x i).continuous).aestronglyMeasurable
  have hn : ∀ t ∈ Ioc 0 1,
      ‖stableSecondDifference (coordinateLine φ x i) t‖ ≤ 2 * (K : ℝ) * t ^ 2 :=
    fun t ht ↦ norm_stableSecondDifference_le_quadratic (hd x i) (hLip x i) ht.1.le
  have hf : ∀ t ∈ Ioi 1, ‖stableSecondDifference (coordinateLine φ x i) t‖ ≤ 4 * M :=
    fun t _ ↦ norm_stableSecondDifference_le_four (fun _ ↦ hM _) t
  refine ⟨integrable_stableJumpMeasure_of_bounds hα0 hα2 (by norm_num : (0 : ℝ) < 1)
    _ hm hn hf, ?_⟩
  simpa only [Real.one_rpow, mul_one] using integral_norm_stableJumpMeasure_le hα0 hα2
    (by norm_num : (0 : ℝ) < 1) _ hm hn hf

/-- Genuine product integrability uses only the kernel's actual L¹ integrability. -/
theorem integrable_kernel_mul_coordinateSecondDifference {α : ℝ} {K : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hK : Integrable K volume)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    Integrable (fun p : E × ℝ ↦
      K p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α) := by
  obtain ⟨C, hC⟩ := coordinateSecondDifference_integrable_uniform hα0 hα2 φ hφ hs i
  have hc : Continuous (fun p : E × ℝ ↦
      stableSecondDifference (coordinateLine φ p.1 i) p.2) := by
    unfold stableSecondDifference coordinateLine
    have hcφ := hφ.continuous
    fun_prop
  have hm : AEStronglyMeasurable (fun p : E × ℝ ↦
      K p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α) :=
    (hK.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α))).mul hc.aestronglyMeasurable
  change Integrable _ (volume.prod (stableJumpMeasure α))
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards with x
    exact (hC x).1.const_mul (K x)
  · apply (hK.norm.mul_const C).mono' hm.norm.integral_prod_right'
    filter_upwards with x
    simp only [norm_mul, integral_const_mul, norm_norm]
    rw [show ‖∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖
      ∂stableJumpMeasure α‖ =
      ∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖ ∂stableJumpMeasure α by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]]
    exact mul_le_mul_of_nonneg_left (hC x).2 (norm_nonneg _)

/-- Actual Fubini recovers the original normalized coordinate generator against any L¹ kernel. -/
theorem integral_kernel_mul_coordinateSecondDifference {α : ℝ} {K : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hK : Integrable K volume)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    (∫ p, K p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2
      ∂spatialJumpMeasure α) = stableNormalization α *
        ∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x i) := by
  have hi := integrable_kernel_mul_coordinateSecondDifference hα0 hα2 hK φ hφ hs i
  rw [spatialJumpMeasure, integral_prod _ hi, ← integral_const_mul]
  congr 1
  funext x
  dsimp only
  rw [integral_const_mul, integral_stableJumpMeasure hα0 hα2]
  unfold stableGeneratorIntegral
  simp only [smul_eq_mul]
  ring

end PartialBalayage.Maximal.Square
