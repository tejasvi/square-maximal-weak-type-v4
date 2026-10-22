/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorFubini

/-!
# Genuine physical generator self-adjointness

Translation invariance first identifies the actual fixed-jump pairings. Actual product
integrability then allows Fubini across every jump. Smooth compact kernels satisfy both
product integrability conditions automatically.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem integrable_translate_mul_bounded {K φ : E → ℝ} {M : ℝ}
    (hK : Integrable K volume) (hφ : Continuous φ) (hb : ∀ x, ‖φ x‖ ≤ M) (a : E) :
    Integrable (fun x ↦ K (x + a) * φ x) volume := by
  have hi : Integrable (fun x ↦ K (x + a)) volume :=
    ((measurePreserving_add_right volume a).integrable_comp_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).mpr hK
  exact hi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)

private theorem integral_translate_mul_bounded {K φ : E → ℝ} (a : E) :
    (∫ x : E, K x * φ (x + a)) = ∫ x : E, K (x + -a) * φ x := by
  have h := (measurePreserving_add_right volume (-a)).integral_comp
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
    (fun x ↦ K x * φ (x + a))
  simpa only [add_assoc, neg_add_cancel, add_zero] using h.symm

/-- Genuine L¹ kernels and bounded continuous tests have the actual fixed-jump symmetry. -/
theorem integral_kernel_mul_secondDifference_symmetry {K φ : E → ℝ} {M : ℝ}
    (hK : Integrable K volume) (hφ : Continuous φ) (hb : ∀ x, ‖φ x‖ ≤ M) (a : E) :
    (∫ x : E, K x * (φ (x + a) + φ (x - a) - 2 * φ x)) =
      ∫ x : E, φ x * (K (x + a) + K (x - a) - 2 * K x) := by
  have h₀ := hK.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hp : Integrable (fun x ↦ K x * φ (x + a)) volume :=
    hK.mul_bdd (hφ.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ hb (x + a)))
  have hn : Integrable (fun x ↦ K x * φ (x + -a)) volume :=
    hK.mul_bdd (hφ.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ hb (x + -a)))
  have hpa := integrable_translate_mul_bounded hK hφ hb a
  have hna := integrable_translate_mul_bounded hK hφ hb (-a)
  have he₁ : (fun x ↦ K x * (φ (x + a) + φ (x - a) - 2 * φ x)) =
      fun x ↦ (K x * φ (x + a) + K x * φ (x + -a)) - 2 * (K x * φ x) := by
    funext x
    simp only [sub_eq_add_neg]
    ring
  have he₂ : (fun x ↦ φ x * (K (x + a) + K (x - a) - 2 * K x)) =
      fun x ↦ (K (x + a) * φ x + K (x + -a) * φ x) - 2 * (K x * φ x) := by
    funext x
    simp only [sub_eq_add_neg]
    ring
  have e₁ := integral_sub (hp.add hn) (h₀.const_mul 2)
  have e₂ := integral_sub (hpa.add hna) (h₀.const_mul 2)
  have e₃ := integral_add hp hn
  have e₄ := integral_add hpa hna
  simp only [Pi.add_apply] at e₁ e₂ e₃ e₄
  rw [he₁, he₂, e₁, e₂, e₃, e₄, integral_const_mul,
    integral_translate_mul_bounded a, integral_translate_mul_bounded (-a)]
  simp only [neg_neg]
  ring

/-- Actual product integrability permits the true coordinate-generator symmetry. -/
theorem integral_kernel_mul_coordinateGenerator_symmetry {α : ℝ} {K φ : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hK : Integrable K volume)
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (i : Fin 2)
    (hi : Integrable (fun p : E × ℝ ↦
      φ p.1 * stableSecondDifference (coordinateLine K p.1 i) p.2)
        (spatialJumpMeasure α)) :
    stableNormalization α * (∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x i)) =
      stableNormalization α * ∫ x : E, φ x *
        stableGeneratorIntegral α (coordinateLine K x i) := by
  obtain ⟨M, _, hb, _, _⟩ := compactC2_coordinateLine_bounds φ hφ hs
  have ht := integrable_kernel_mul_coordinateSecondDifference hα0 hα2 hK φ hφ hs i
  rw [← integral_kernel_mul_coordinateSecondDifference hα0 hα2 hK φ hφ hs i]
  calc
    _ = ∫ t, (∫ x : E, K x * stableSecondDifference (coordinateLine φ x i) t)
        ∂stableJumpMeasure α := by rw [spatialJumpMeasure, integral_prod_symm _ ht]
    _ = ∫ t, (∫ x : E, φ x * stableSecondDifference (coordinateLine K x i) t)
        ∂stableJumpMeasure α := by
      congr 1
      funext t
      simpa only [stableSecondDifference, coordinateLine, neg_smul, sub_eq_add_neg,
        smul_eq_mul, zero_smul, add_zero] using
          integral_kernel_mul_secondDifference_symmetry hK hφ.continuous hb
          (t • EuclideanSpace.basisFun (Fin 2) ℝ i)
    _ = ∫ p, φ p.1 * stableSecondDifference (coordinateLine K p.1 i) p.2
        ∂spatialJumpMeasure α := by rw [spatialJumpMeasure, integral_prod_symm _ hi]
    _ = _ := by
      rw [spatialJumpMeasure, integral_prod _ hi, ← integral_const_mul]
      congr 1
      funext x
      dsimp only
      rw [integral_const_mul, integral_stableJumpMeasure hα0 hα2]
      unfold stableGeneratorIntegral
      simp only [smul_eq_mul]
      ring

/-- Actual product integrability implies integrability of the genuine generator pairing. -/
theorem integrable_mul_coordinateGenerator_of_product {α : ℝ} {K φ : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (i : Fin 2)
    (hi : Integrable (fun p : E × ℝ ↦
      K p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α)) :
    Integrable (fun x : E ↦ K x * stableGeneratorIntegral α (coordinateLine φ x i)) := by
  have he : (fun x : E ↦ ∫ t, K x * stableSecondDifference (coordinateLine φ x i) t
      ∂stableJumpMeasure α) = fun x ↦ stableNormalization α *
        (K x * stableGeneratorIntegral α (coordinateLine φ x i)) := by
    funext x
    rw [integral_const_mul, integral_stableJumpMeasure hα0 hα2]
    unfold stableGeneratorIntegral
    simp only [smul_eq_mul]
    ring
  have ht : Integrable (fun x : E ↦ stableNormalization α *
      (K x * stableGeneratorIntegral α (coordinateLine φ x i))) := by
    rw [← he]
    exact hi.integral_prod_left
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (stableNormalization_pos hα0 hα2).ne') _).mp ht

private theorem integral_kernel_mul_generator_split {α : ℝ} {K φ : E → ℝ}
    (hi : ∀ i : Fin 2, Integrable
      (fun x : E ↦ K x * stableGeneratorIntegral α (coordinateLine φ x i))) :
    (∫ x : E, K x * coordinateStableGenerator α φ x) =
      stableNormalization α * (∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x 0)) +
        stableNormalization α * ∫ x : E, K x * stableGeneratorIntegral α (coordinateLine φ x 1)
        := by
  have he : (fun x : E ↦ K x * coordinateStableGenerator α φ x) =
      fun x ↦ stableNormalization α * (K x * stableGeneratorIntegral α (coordinateLine φ x 0)) +
        stableNormalization α * (K x * stableGeneratorIntegral α (coordinateLine φ x 1)) := by
    funext x
    simp only [coordinateStableGenerator, Fin.sum_univ_two]
    ring
  have h := integral_add ((hi 0).const_mul (stableNormalization α))
    ((hi 1).const_mul (stableNormalization α))
  rw [he]
  simpa only [Pi.add_apply, integral_const_mul] using h

/-- The actual normalized generator is self-adjoint on genuine compact C² functions. -/
theorem integral_coordinateStableGenerator_compactC2_symmetry {α : ℝ} {K φ : E → ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hK : ContDiff ℝ 2 K) (hsK : HasCompactSupport K)
    (hφ : ContDiff ℝ 2 φ) (hsφ : HasCompactSupport φ) :
    (∫ x : E, K x * coordinateStableGenerator α φ x) =
      ∫ x : E, φ x * coordinateStableGenerator α K x := by
  have hKi : Integrable K volume := hK.continuous.integrable_of_hasCompactSupport hsK
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hsφ
  have hp (i : Fin 2) := integrable_kernel_mul_coordinateSecondDifference
    hα0 hα2 hKi φ hφ hsφ i
  have hq (i : Fin 2) := integrable_kernel_mul_coordinateSecondDifference
    hα0 hα2 hφi K hK hsK i
  rw [integral_kernel_mul_generator_split
    (fun i ↦ integrable_mul_coordinateGenerator_of_product hα0 hα2 i (hp i)),
    integral_kernel_mul_generator_split
      (fun i ↦ integrable_mul_coordinateGenerator_of_product hα0 hα2 i (hq i))]
  rw [integral_kernel_mul_coordinateGenerator_symmetry hα0 hα2 hKi hφ hsφ 0 (hq 0),
    integral_kernel_mul_coordinateGenerator_symmetry hα0 hα2 hKi hφ hsφ 1 (hq 1)]

end PartialBalayage.Maximal.Square
