/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorSymmetry

/-!
# Genuine source-side product integrability from spatial cancellation

Actual spatial translation bounds the large jumps by the kernel's L¹ mass. An actual
integrated quadratic small-jump estimate then suffices for complete product integrability.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem integrable_translate_kernel {K : E → ℝ} (hK : Integrable K volume) (a : E) :
    Integrable (fun x ↦ K (x + a)) volume :=
  ((measurePreserving_add_right volume a).integrable_comp_emb
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).mpr hK

theorem coordinateSecondDifference_eq_spatial (K : E → ℝ) (x : E) (i : Fin 2) (t : ℝ) :
    stableSecondDifference (coordinateLine K x i) t =
      K (x + t • EuclideanSpace.basisFun (Fin 2) ℝ i) +
        K (x - t • EuclideanSpace.basisFun (Fin 2) ℝ i) - 2 * K x := by
  simp only [stableSecondDifference, coordinateLine, neg_smul, zero_smul, add_zero,
    smul_eq_mul, sub_eq_add_neg]

theorem integrable_coordinateSecondDifference_kernel {K : E → ℝ}
    (hK : Integrable K volume) (i : Fin 2) (t : ℝ) :
    Integrable (fun x ↦ stableSecondDifference (coordinateLine K x i) t) volume := by
  have hp := integrable_translate_kernel hK (t • EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hn := integrable_translate_kernel hK (-t • EuclideanSpace.basisFun (Fin 2) ℝ i)
  have h := (hp.add hn).sub (hK.const_mul (2 : ℝ))
  apply h.congr
  filter_upwards with x
  simp only [stableSecondDifference, coordinateLine, Pi.add_apply, Pi.sub_apply,
    zero_smul, add_zero, smul_eq_mul]

/-- The true spatial L¹ second difference has the exact translation mass bound. -/
theorem integral_norm_coordinateSecondDifference_kernel_le {K : E → ℝ}
    (hK : Integrable K volume) (i : Fin 2) (t : ℝ) :
    (∫ x : E, ‖stableSecondDifference (coordinateLine K x i) t‖) ≤ 4 * ∫ x : E, ‖K x‖ := by
  let a := t • EuclideanSpace.basisFun (Fin 2) ℝ i
  have hp := (integrable_translate_kernel hK a).norm
  have hn := (integrable_translate_kernel hK (-a)).norm
  have hh : Integrable (fun x ↦ ‖K (x + a)‖ + ‖K (x + -a)‖ + 2 * ‖K x‖) :=
    (hp.add hn).add (hK.norm.const_mul 2)
  have hb (x : E) : ‖stableSecondDifference (coordinateLine K x i) t‖ ≤
      ‖K (x + a)‖ + ‖K (x + -a)‖ + 2 * ‖K x‖ := by
    rw [coordinateSecondDifference_eq_spatial, sub_eq_add_neg]
    change ‖K (x + a) + K (x + -a) - 2 * K x‖ ≤ _
    exact (norm_sub_le _ _).trans (by
      rw [norm_mul, show ‖(2 : ℝ)‖ = 2 by norm_num]
      linarith [norm_add_le (K (x + a)) (K (x + -a))])
  have he₁ := integral_add (hp.add hn) (hK.norm.const_mul 2)
  have he₂ := integral_add hp hn
  simp only [Pi.add_apply] at he₁ he₂
  have he (b : E) : (∫ x : E, ‖K (x + b)‖) = ∫ x : E, ‖K x‖ :=
    (measurePreserving_add_right volume b).integral_comp
      (Homeomorph.addRight b).isClosedEmbedding.measurableEmbedding (fun x ↦ ‖K x‖)
  have hmono := integral_mono (integrable_coordinateSecondDifference_kernel hK i t).norm hh hb
  apply hmono.trans_eq
  rw [he₁, he₂, integral_const_mul, he a, he (-a)]
  ring

private theorem integrable_test_mul_kernelSecondDifference {K φ : E → ℝ} {M : ℝ}
    (hK : Integrable K volume) (hφ : Continuous φ) (hb : ∀ x, ‖φ x‖ ≤ M)
    (i : Fin 2) (t : ℝ) :
    Integrable (fun x ↦ φ x * stableSecondDifference (coordinateLine K x i) t) volume :=
  (integrable_coordinateSecondDifference_kernel hK i t).bdd_mul hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

private theorem integral_norm_test_mul_kernelSecondDifference_le {K φ : E → ℝ} {M : ℝ}
    (hK : Integrable K volume) (hφ : Continuous φ) (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M)
    (i : Fin 2) (t : ℝ) :
    (∫ x : E, ‖φ x * stableSecondDifference (coordinateLine K x i) t‖) ≤
      4 * (M * ∫ x : E, ‖K x‖) := by
  have hi := integrable_test_mul_kernelSecondDifference hK hφ hb i t
  have hm := (integrable_coordinateSecondDifference_kernel hK i t).norm.const_mul M
  have hbound (x : E) : ‖φ x * stableSecondDifference (coordinateLine K x i) t‖ ≤
      M * ‖stableSecondDifference (coordinateLine K x i) t‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  apply (integral_mono hi.norm hm hbound).trans
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (integral_norm_coordinateSecondDifference_kernel_le hK i t)
    hM).trans_eq (by ring)

/-- An actual spatial quadratic estimate gives full source-side stable product integrability. -/
theorem integrable_source_product_of_spatial_secondDifference_bound
    {α ρ C M : ℝ} {K φ : E → ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hρ : 0 < ρ)
    (hK : Integrable K volume) (hKm : Measurable K) (hφ : Continuous φ)
    (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M) (i : Fin 2)
    (hnear : ∀ t ∈ Ioc 0 ρ,
      (∫ x : E, ‖φ x * stableSecondDifference (coordinateLine K x i) t‖) ≤ C * t ^ 2) :
    Integrable (fun p : E × ℝ ↦ φ p.1 *
      stableSecondDifference (coordinateLine K p.1 i) p.2) (spatialJumpMeasure α) := by
  have hm : Measurable (fun p : E × ℝ ↦ φ p.1 *
      stableSecondDifference (coordinateLine K p.1 i) p.2) := by
    unfold stableSecondDifference coordinateLine
    fun_prop
  have hi : AEStronglyMeasurable (fun t : ℝ ↦
      ∫ x : E, ‖φ x * stableSecondDifference (coordinateLine K x i) t‖)
        (volume.restrict (Ioi 0)) :=
    (hm.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
  have hg := integrable_stableJumpMeasure_of_bounds hα0 hα2 hρ _ hi
    (fun t ht ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
      exact hnear t ht)
    (fun t _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
      exact integral_norm_test_mul_kernelSecondDifference_le hK hφ hM hb i t)
  change Integrable _ (volume.prod (stableJumpMeasure α))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  exact ⟨Filter.Eventually.of_forall
    (fun t ↦ integrable_test_mul_kernelSecondDifference hK hφ hb i t), hg⟩

end PartialBalayage.Maximal.Square
