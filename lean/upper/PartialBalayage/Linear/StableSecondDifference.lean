/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FractionalCutoffBound
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Genuine stable second differences of differentiable functions

The actual second difference has a quadratic bound from a Lipschitz derivative
and a uniform bound from the function's amplitude. These imply integrability
and the exact estimate for its full singular stable-generator integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace PartialBalayage.Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The genuine symmetric second difference at the origin. -/
def stableSecondDifference (φ : ℝ → F) (t : ℝ) : F :=
  φ t + φ (-t) - (2 : ℝ) • φ 0

theorem stableSecondDifference_zero (φ : ℝ → F) : stableSecondDifference φ 0 = 0 := by
  simp [stableSecondDifference, two_smul]

/-- An actual bounded function has the uniform second-difference estimate. -/
theorem norm_stableSecondDifference_le_four {φ : ℝ → F} {M : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ M) (t : ℝ) : ‖stableSecondDifference φ t‖ ≤ 4 * M := by
  unfold stableSecondDifference
  calc
    _ ≤ ‖φ t + φ (-t)‖ + ‖(2 : ℝ) • φ 0‖ := norm_sub_le _ _
    _ ≤ (‖φ t‖ + ‖φ (-t)‖) + 2 * ‖φ 0‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact add_le_add (norm_add_le (φ t) (φ (-t))) le_rfl
    _ ≤ 4 * M := by linarith [hφ t, hφ (-t), hφ 0]

/-- A Lipschitz first derivative gives a genuine quadratic second-difference bound. -/
theorem norm_stableSecondDifference_le_quadratic {φ : ℝ → F} {K : ℝ≥0}
    (hφ : Differentiable ℝ φ) (hφ' : LipschitzWith K (deriv φ)) {t : ℝ} (ht : 0 ≤ t) :
    ‖stableSecondDifference φ t‖ ≤ 2 * (K : ℝ) * t ^ 2 := by
  have hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt (stableSecondDifference φ)
      (deriv φ s - deriv φ (-s)) (Icc 0 t) s := by
    intro s hs
    have hneg := (hφ (-s)).hasDerivAt.scomp s (hasDerivAt_id s).neg
    have hadd := ((hφ s).hasDerivAt.add hneg).sub_const ((2 : ℝ) • φ 0)
    change HasDerivWithinAt (fun s ↦ φ s + φ (-s) - (2 : ℝ) • φ 0)
      (deriv φ s - deriv φ (-s)) (Icc 0 t) s
    simpa only [Pi.add_apply, Function.comp_apply, neg_smul, one_smul, sub_eq_add_neg] using
      hadd.hasDerivWithinAt
  have hb : ∀ s ∈ Ico 0 t, ‖deriv φ s - deriv φ (-s)‖ ≤ 2 * (K : ℝ) * t := by
    intro s hs
    calc
      _ ≤ (K : ℝ) * ‖s - (-s)‖ := hφ'.norm_sub_le s (-s)
      _ = (K : ℝ) * (2 * s) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
        ring
      _ ≤ 2 * (K : ℝ) * t := by nlinarith [K.coe_nonneg, hs.2]
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa only [stableSecondDifference_zero, sub_zero, pow_two, mul_assoc] using hbound

/-- The original second difference is strongly measurable whenever its source is continuous. -/
theorem continuous_stableSecondDifference {φ : ℝ → F} (hφ : Continuous φ) :
    Continuous (stableSecondDifference φ) := by
  unfold stableSecondDifference
  exact (hφ.add (hφ.comp continuous_neg)).sub continuous_const

/-- The actual full stable-generator integral of a bounded smooth function is integrable. -/
theorem integrable_stable_secondDifference {α r M : ℝ} {K : ℝ≥0} {φ : ℝ → F}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (hφ : Differentiable ℝ φ)
    (hφ' : LipschitzWith K (deriv φ)) (hM : ∀ t, ‖φ t‖ ≤ M) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) • stableSecondDifference φ t) (Ioi 0) := by
  apply integrable_stable_weighted_difference hα0 hα2 hr (stableSecondDifference φ)
    (continuous_stableSecondDifference hφ.continuous).aestronglyMeasurable
  · intro t ht
    exact norm_stableSecondDifference_le_quadratic hφ hφ' ht.1.le
  · intro t ht
    exact norm_stableSecondDifference_le_four hM t

/-- The actual full stable-generator integral has the exact amplitude/derivative estimate. -/
theorem norm_integral_stable_secondDifference_le [CompleteSpace F]
    {α r M : ℝ} {K : ℝ≥0} {φ : ℝ → F}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (hφ : Differentiable ℝ φ)
    (hφ' : LipschitzWith K (deriv φ)) (hM : ∀ t, ‖φ t‖ ≤ M) :
    ‖∫ t in Ioi 0, t ^ (-1 - α) • stableSecondDifference φ t‖ ≤
      (2 * (K : ℝ)) * r ^ (2 - α) / (2 - α) + 4 * M * r ^ (-α) / α := by
  apply norm_integral_stable_weighted_difference_le hα0 hα2 hr (stableSecondDifference φ)
    (continuous_stableSecondDifference hφ.continuous).aestronglyMeasurable
  · intro t ht
    exact norm_stableSecondDifference_le_quadratic hφ hφ' ht.1.le
  · intro t ht
    exact norm_stableSecondDifference_le_four hM t

/-- A genuinely small bounded smooth function has the vanishing-order cutoff estimate. -/
theorem norm_integral_stable_secondDifference_small_le [CompleteSpace F]
    {α ε : ℝ} {K : ℝ≥0} {φ : ℝ → F}
    (hα0 : 0 < α) (hα2 : α < 2) (hε : 0 < ε) (hφ : Differentiable ℝ φ)
    (hφ' : LipschitzWith K (deriv φ)) (hM : ∀ t, ‖φ t‖ ≤ (K : ℝ) * ε ^ 2) :
    ‖∫ t in Ioi 0, t ^ (-1 - α) • stableSecondDifference φ t‖ ≤
      (2 * (K : ℝ)) * (1 / (2 - α) + 4 / α) * ε ^ (2 - α) := by
  apply norm_integral_stable_small_cutoff_le hα0 hα2 hε (stableSecondDifference φ)
    (continuous_stableSecondDifference hφ.continuous).aestronglyMeasurable
  · intro t ht
    exact norm_stableSecondDifference_le_quadratic hφ hφ' ht.1.le
  · intro t ht
    apply (norm_stableSecondDifference_le_four hM t).trans
    nlinarith [K.coe_nonneg, sq_nonneg ε]

/-- The genuine full singular integral tends to zero through positive cutoff radii. -/
theorem tendsto_integral_stable_secondDifference_small_zero [CompleteSpace F]
    {α : ℝ} {K : ℝ≥0} (hα0 : 0 < α) (hα2 : α < 2) (φ : ℝ → ℝ → F)
    (hφ : ∀ ε > 0, Differentiable ℝ (φ ε))
    (hφ' : ∀ ε > 0, LipschitzWith K (deriv (φ ε)))
    (hM : ∀ ε > 0, ∀ t, ‖φ ε t‖ ≤ (K : ℝ) * ε ^ 2) :
    Tendsto (fun ε ↦ ∫ t in Ioi 0,
      t ^ (-1 - α) • stableSecondDifference (φ ε) t) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun ε ↦ (2 * (K : ℝ)) * (1 / (2 - α) + 4 / α) * ε ^ (2 - α))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_integral_stable_secondDifference_small_le hα0 hα2 hε
      (hφ ε hε) (hφ' ε hε) (hM ε hε)
  · have hp : Tendsto (fun ε : ℝ ↦ ε ^ (2 - α)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (2 - α))) :=
      (Real.continuousAt_rpow_const 0 (2 - α)
      (Or.inr (by linarith : 0 ≤ 2 - α))).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow (by linarith : 2 - α ≠ 0), mul_zero] using
      hp.const_mul ((2 * (K : ℝ)) * (1 / (2 - α) + 4 / α))

end PartialBalayage.Linear
