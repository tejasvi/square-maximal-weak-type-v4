/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SourceMomentIntegrability
public import Mathlib.Analysis.Convolution

/-!
# The compensated source is the true kernel-convolved generator

Translating the actual compact-test source identity gives a pointwise identity
for the full compensated jump generator. Its second differences remain truly
source-integrable, including the infinite small-jump mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped Convolution

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The full actual symmetric second-difference generator of the punctured source measure. -/
def compensatedSourceGenerator (μ : Measure E) (φ : E → ℝ) (x : E) : ℝ :=
  (1 / 2 : ℝ) * ∫ z, φ (x + z) + φ (x - z) - 2 * φ x ∂μ

/-- Physical translation commutes with the actual coordinate generator. -/
theorem coordinateStableGenerator_translate (α : ℝ) (φ : E → ℝ) (x y : E) :
    coordinateStableGenerator α (fun z ↦ φ (x + z)) y =
      coordinateStableGenerator α φ (x + y) := by
  unfold coordinateStableGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext t
  simp only [coordinateLine, add_assoc]

/-- Genuine compact C² second differences are integrable against the entire source measure. -/
theorem integrable_compactC2_sourceSecondDifference (μ : Measure E)
    (hm : Integrable compensatedJumpMoment μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    Integrable (fun z ↦ φ (x + z) + φ (x - z) - 2 * φ x) μ := by
  let ψ (z : E) := φ (x + z)
  have hc : ContDiff ℝ 2 ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.addLeft x)
  obtain ⟨C, hb, _⟩ := exists_compensated_test_moment_bound
    (sourceEvenPart_contDiff hc) (sourceEvenPart_hasCompactSupport hcs)
    (sourceEvenPart_fderiv_zero ψ)
  have hφc := hφ.continuous
  have hδ : Continuous (fun z ↦ φ (x + z) + φ (x - z) - 2 * φ x) := by fun_prop
  apply (hm.const_mul (2 * C)).mono' hδ.aestronglyMeasurable
  filter_upwards with z
  have he : φ (x + z) + φ (x - z) - 2 * φ x =
      2 * (sourceEvenPart ψ z - sourceEvenPart ψ 0) := by
    simp only [sourceEvenPart, ψ, neg_zero, add_zero, sub_eq_add_neg]
    ring
  rw [he, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (C * compensatedJumpMoment z) :=
      mul_le_mul_of_nonneg_left (hb z) (by norm_num)
    _ = _ := by ring

/-- The actual source generator is the true kernel convolution
of the original coordinate generator. -/
theorem compensatedSourceGenerator_eq_kernel_convolution
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (hKeven : ∀ x, K (-x) = K x) (μ : Measure E)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ y, K y * coordinateStableGenerator α ψ y) = ∫ y, ψ y ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    compensatedSourceGenerator μ φ x =
      (K ⋆ coordinateStableGenerator α φ) x := by
  let ψ (z : E) := φ (x + z)
  have hc : ContDiff ℝ 2 ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.addLeft x)
  have he := integral_kernel_generator_eq_compensatedSymmetricSource_of_punctured_source
    hα0 hα2 hK hKeven μ hlocal haway hc hcs
  have hr : compensatedSymmetricSource μ ψ = compensatedSourceGenerator μ φ x := by
    unfold compensatedSymmetricSource compensatedSourceGenerator
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [ψ, add_zero, sub_eq_add_neg]
  rw [hr] at he
  rw [← he]
  have hneg := integral_neg_eq_self
    (fun y : E ↦ K y * coordinateStableGenerator α φ (x - y)) volume
  simp only [sub_neg_eq_add, hKeven] at hneg
  rw [convolution_def]
  calc
    _ = ∫ y, K y * coordinateStableGenerator α φ (x + y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [coordinateStableGenerator_translate]
    _ = _ := hneg

end PartialBalayage.Maximal.Square
