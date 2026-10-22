/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SourceMomentIntegrability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Actual positive dilation of kernels and punctured source measures

Physical dilation preserves the genuine local source identity. Its Jacobian
and stable-generator powers give the actual positive pushed-forward measure.
Every positive averaging radius consequently has the same proved source data.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine unnormalized physical kernel dilation. -/
def dilatedComparisonKernel (r : ℝ) (K : E → ℝ) (x : E) : ℝ := K (r⁻¹ • x)

/-- The genuine positive push-forward of the original punctured source. -/
def dilatedSourceMeasure (α r : ℝ) (μ : Measure E) : Measure E :=
  ENNReal.ofReal (r ^ 2 * r ^ (-α)) • Measure.map (fun x : E ↦ r • x) μ

theorem integrable_dilatedComparisonKernel {K : E → ℝ} (hK : Integrable K volume)
    {r : ℝ} (hr : 0 < r) : Integrable (dilatedComparisonKernel r K) volume :=
  hK.comp_smul (inv_ne_zero hr.ne')

/-- The actual kernel mass scales by the genuine planar Jacobian. -/
theorem integral_dilatedComparisonKernel (K : E → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x, dilatedComparisonKernel r K x) = r ^ 2 * ∫ x, K x := by
  simpa only [dilatedComparisonKernel, finrank_euclideanSpace_fin, smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg (μ := volume) K hr.le

theorem dilatedComparisonKernel_even {K : E → ℝ} (hK : ∀ x, K (-x) = K x)
    (r : ℝ) (x : E) : dilatedComparisonKernel r K (-x) = dilatedComparisonKernel r K x := by
  simp only [dilatedComparisonKernel, smul_neg, hK]

private theorem contDiff_comp_positive_dilation {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (r : ℝ) : ContDiff ℝ 2 (fun x : E ↦ φ (r • x)) := by
  fun_prop

private theorem hasCompactSupport_comp_positive_dilation {φ : E → ℝ}
    (hs : HasCompactSupport φ) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun x : E ↦ φ (r • x)) :=
  hs.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')

private theorem zero_not_tsupport_comp_positive_dilation {φ : E → ℝ}
    (hs : 0 ∉ tsupport φ) {r : ℝ} (hr : 0 < r) :
    0 ∉ tsupport (fun x : E ↦ φ (r • x)) := by
  have ht := tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero r hr.ne')
  change 0 ∉ tsupport (φ ∘ Homeomorph.smulOfNeZero r hr.ne')
  rw [ht]
  simpa only [mem_preimage, Homeomorph.smulOfNeZero_apply, smul_zero] using hs

/-- The original coordinate generator acquires its exact direct-dilation power. -/
theorem coordinateStableGenerator_comp_positive_dilation (α : ℝ) (φ : E → ℝ)
    {r : ℝ} (hr : 0 < r) (x : E) :
    coordinateStableGenerator α (fun y ↦ φ (r • y)) x =
      r ^ α * coordinateStableGenerator α φ (r • x) := by
  have he := coordinateStableGenerator_dilate α φ x (inv_pos.mpr hr)
  simpa only [inv_inv, ← Real.rpow_neg_eq_inv_rpow, neg_neg] using he

/-- The actual scaled kernel/test pairing has the Jacobian minus generator power. -/
theorem integral_dilatedComparisonKernel_mul_generator (α : ℝ) (K φ : E → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ x, dilatedComparisonKernel r K x * coordinateStableGenerator α φ x) =
      (r ^ 2 * r ^ (-α)) *
        ∫ x, K x * coordinateStableGenerator α (fun y ↦ φ (r • y)) x := by
  let H : E → ℝ := fun x ↦ K x * coordinateStableGenerator α φ (r • x)
  have hc : (∫ x, H (r⁻¹ • x)) = r ^ 2 * ∫ x, H x := by
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
      Measure.integral_comp_inv_smul_of_nonneg (μ := volume) H hr.le
  have hp : r ^ (-α) * r ^ α = 1 := by
    rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
  calc
    _ = ∫ x, H (r⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [H, dilatedComparisonKernel, smul_inv_smul₀ hr.ne']
    _ = r ^ 2 * ∫ x, H x := hc
    _ = _ := by
      rw [← integral_const_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [coordinateStableGenerator_comp_positive_dilation α φ hr x]
      dsimp only [H]
      calc
        _ = r ^ 2 * (r ^ (-α) * r ^ α) *
            (K x * coordinateStableGenerator α φ (r • x)) := by rw [hp, mul_one]
        _ = _ := by ring

/-- Actual integration against the scaled measure is integration against the true dilation. -/
theorem integral_dilatedSourceMeasure (α : ℝ) {r : ℝ} (hr : 0 < r)
    (μ : Measure E) (φ : E → ℝ) :
    (∫ x, φ x ∂dilatedSourceMeasure α r μ) =
      (r ^ 2 * r ^ (-α)) * ∫ x, φ (r • x) ∂μ := by
  have he : MeasurableEmbedding (fun x : E ↦ r • x) :=
    (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv.measurableEmbedding
  rw [dilatedSourceMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), he.integral_map]
  rfl

/-- Every genuine compact test away from the origin remains source-integrable after dilation. -/
theorem integrable_dilatedSourceMeasure_test {μ : Measure E}
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (α : ℝ) {r : ℝ} (hr : 0 < r) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (hs₀ : 0 ∉ tsupport φ) :
    Integrable φ (dilatedSourceMeasure α r μ) := by
  have he : MeasurableEmbedding (fun x : E ↦ r • x) :=
    (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv.measurableEmbedding
  have hi := hlocal (fun x ↦ φ (r • x)) (contDiff_comp_positive_dilation hφ r)
    (hasCompactSupport_comp_positive_dilation hs hr)
    (zero_not_tsupport_comp_positive_dilation hs₀ hr)
  exact (he.integrable_map_iff.mpr hi).smul_measure (by simp)

/-- The true punctured distributional source identity is preserved at every positive radius. -/
theorem integral_dilatedComparisonKernel_generator_eq_source {α : ℝ} {K : E → ℝ}
    {μ : Measure E}
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {r : ℝ} (hr : 0 < r) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (hs₀ : 0 ∉ tsupport φ) :
    (∫ x, dilatedComparisonKernel r K x * coordinateStableGenerator α φ x) =
      ∫ x, φ x ∂dilatedSourceMeasure α r μ := by
  rw [integral_dilatedComparisonKernel_mul_generator α K φ hr,
    integral_dilatedSourceMeasure α hr μ φ,
    haway (fun x ↦ φ (r • x)) (contDiff_comp_positive_dilation hφ r)
      (hasCompactSupport_comp_positive_dilation hs hr)
      (zero_not_tsupport_comp_positive_dilation hs₀ hr)]

end PartialBalayage.Maximal.Square
