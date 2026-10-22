/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SourceGeneratorConvolution
public import PartialBalayage.Maximal.Square.GeneratorMeasurability

/-!
# Actual mollification of the stable equation and its kernel source

Bounded middle kernels give genuine associative convolution of L¹ inputs.
The actual distributional stable equation identifies each smooth source image
with convolution of its genuine forcing by the original comparison kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure ContinuousLinearMap Filter Set
open scoped Convolution ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Genuine L¹ outer factors and a bounded measurable middle factor give associativity. -/
theorem convolution_assoc_of_integrable_bounded_middle
    {K a u : E → ℝ} (hK : Integrable K volume) (hu : Integrable u volume)
    (ha : AEStronglyMeasurable a volume) {M : ℝ} (hb : ∀ x, ‖a x‖ ≤ M) (x : E) :
    ((K ⋆[lsmul ℝ ℝ, volume] a) ⋆[lsmul ℝ ℝ, volume] u) x =
      (K ⋆[lsmul ℝ ℝ, volume] (a ⋆[lsmul ℝ ℝ, volume] u)) x := by
  have hKa (y : E) : ConvolutionExistsAt K a y (lsmul ℝ ℝ) volume := by
    exact hK.mul_bdd (ha.comp_measurePreserving (volume.measurePreserving_sub_left y))
      (Eventually.of_forall fun z ↦ hb (y - z))
  have hau (y : E) : ConvolutionExistsAt a u y (lsmul ℝ ℝ) volume := by
    apply ((hu.comp_sub_left y).mul_bdd ha (Eventually.of_forall hb)).congr
    filter_upwards with z
    change u (y - z) * a z = a z * u (y - z)
    ring
  have hq : QuasiMeasurePreserving (fun p : E × E ↦ p.1 - p.2)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    filter_upwards with y
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right volume (-y)).quasiMeasurePreserving
  have hi0 := (hu.comp_sub_left x).mul_prod hK
  have hi : Integrable (fun p : E × E ↦ K p.2 * (a (p.1 - p.2) * u (x - p.1)))
      (volume.prod volume) := by
    apply (hi0.mul_bdd (ha.comp_quasiMeasurePreserving hq)
      (Eventually.of_forall fun p ↦ hb (p.1 - p.2))).congr
    filter_upwards with p
    simp only [Function.comp_def]
    ring
  exact convolution_assoc' (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ)
    (fun _ _ _ ↦ by simp only [lsmul_apply, smul_eq_mul, mul_assoc])
    (Eventually.of_forall hKa) (Eventually.of_forall hau) hi

/-- The true stable generator commutes with translation followed by reflection. -/
theorem coordinateStableGenerator_const_sub (α : ℝ) (φ : E → ℝ) (x y : E) :
    coordinateStableGenerator α (fun z ↦ φ (x - z)) y =
      coordinateStableGenerator α φ (x - y) := by
  have he : (fun z : E ↦ φ (x - z)) = fun z ↦ (fun a : E ↦ φ (x + a)) (-z) := by
    funext z
    simp only [sub_eq_add_neg]
  rw [he]
  calc
    _ = coordinateStableGenerator α (fun a : E ↦ φ (x + a)) (-y) :=
      coordinateStableGenerator_reflect α (fun a : E ↦ φ (x + a)) y
    _ = coordinateStableGenerator α φ (x + -y) :=
      coordinateStableGenerator_translate α φ x (-y)
    _ = _ := by rw [sub_eq_add_neg]

/-- The actual compact mollifier turns the genuine weak stable PDE into a pointwise equation. -/
theorem stableGenerator_mollification_eq_of_distribution
    (α : ℝ) (u g : E → ℝ)
    (hpde : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ y, u y * coordinateStableGenerator α ψ y) = ∫ y, g y * ψ y)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    ((coordinateStableGenerator α φ) ⋆[lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
  have hψ : ContDiff ℝ 2 (fun y : E ↦ φ (x - y)) := by fun_prop
  have hsψ : HasCompactSupport (fun y : E ↦ φ (x - y)) :=
    hs.comp_homeomorph (Homeomorph.subLeft x)
  have he := hpde _ hψ hsψ
  simp only [coordinateStableGenerator_const_sub] at he
  simpa only [convolution_lsmul_swap, smul_eq_mul, mul_comm] using he

/-- The full compensated source of the actual smooth state is the true forcing convolution. -/
theorem compensatedSourceGenerator_mollification_eq_kernel_forcing
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (hKeven : ∀ y, K (-y) = K y)
    (μ : Measure E) [SigmaFinite μ]
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ y, K y * coordinateStableGenerator α ψ y) = ∫ y, ψ y ∂μ)
    {u g : E → ℝ} (hu : Integrable u volume)
    (hpde : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ y, u y * coordinateStableGenerator α ψ y) = ∫ y, g y * ψ y)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    compensatedSourceGenerator μ (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      (K ⋆[lsmul ℝ ℝ, volume] (φ ⋆[lsmul ℝ ℝ, volume] g)) x := by
  have hm := integrable_compensatedJumpMoment_of_punctured_source
    hα0 hα2 hK μ hlocal haway
  rw [compensatedSourceGenerator_convolution_compactC2 μ hm hu hφ hs]
  have hsource : compensatedSourceGenerator μ φ = K ⋆[lsmul ℝ ℝ, volume]
      coordinateStableGenerator α φ := funext
    (compensatedSourceGenerator_eq_kernel_convolution hα0 hα2 hK hKeven μ hlocal haway hφ hs)
  rw [hsource]
  obtain ⟨M, L, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds φ hφ hs
  rw [convolution_assoc_of_integrable_bounded_middle hK hu
    (stronglyMeasurable_coordinateStableGenerator α hφ.continuous).aestronglyMeasurable
      (norm_coordinateStableGenerator_le hα0 hα2 φ hM hd hLip)]
  have hdist := funext (stableGenerator_mollification_eq_of_distribution α u g hpde hφ hs)
  rw [hdist]

end PartialBalayage.Maximal.Square
