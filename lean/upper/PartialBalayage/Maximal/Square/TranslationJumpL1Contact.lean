/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TranslationJumpContact

/-!
# Contact positivity using actual integrable source-form tests

The true negative-part contact tests are bounded by compact tests and thus belong
to L¹. Genuine weak equations on this actual integrable energy class suffice,
without requiring density of compact smooth functions in the full jump graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- Actual weak generator pairings imply the vanishing-error normalized contact estimate. -/
theorem integral_normalizedContactTest_lower_bound_of_L1_jump_form
    (μ : Measure E) [SigmaFinite μ] (u g φ b : L²)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x) (hφ0 : ∀ᵐ x ∂volume, 0 ≤ φ x)
    (hφ1 : Integrable (φ : E → ℝ) volume)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hφ : MemLp (translationJump (φ : E → ℝ)) 2 (volume.prod μ))
    (hequ : ∀ v : L², Integrable (v : E → ℝ) volume →
      MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
      translationJumpForm μ u v = -(∫ x, g x * v x))
    (heqφ : ∀ v : L², Integrable (v : E → ℝ) volume →
      MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
      translationJumpForm μ φ v = -(∫ x, b x * v x)) (k : ℕ) :
    -((∫ x, ‖b x * φ x‖) / ((k : ℝ) + 1)) ≤
      ∫ x, g x * normalizedContactTest u φ k x := by
  let c := (k : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let W := c • u - φ
  let H := translationJumpNegativePart W
  have hW := memLp_translationJump_smul_sub μ u φ hu hφ c
  have hH := memLp_translationJump_negativePart μ W hW
  have hHAE : (H : E → ℝ) =ᵐ[volume] normalizedContactTest u φ k := by
    filter_upwards [translationJumpNegativePart_ae W, Lp.coeFn_sub (c • u) φ,
      Lp.coeFn_smul c u] with x hx hw hs
    rw [hx, hw]
    simp only [Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul, normalizedContactTest]
    congr 1
    dsimp [c]
    ring
  have hH1 : Integrable (H : E → ℝ) volume := by
    apply hφ1.norm.mono' (Lp.aestronglyMeasurable H)
    filter_upwards [hHAE, hu0, hφ0] with x hx hux hφx
    rw [hx, Real.norm_of_nonneg (normalizedContactTest_nonneg _ _ _ _)]
    exact (normalizedContactTest_le hux hφx k).trans (le_abs_self (φ x))
  have hform : c * (-(∫ x, g x * H x)) + (∫ x, b x * H x) ≤ 0 := by
    have hm := translationJumpForm_negativePart_nonpos μ W
    rw [translationJumpForm_smul_sub_left μ u φ H hu hφ hH c,
      hequ H hH1 hH, heqφ H hH1 hH] at hm
    simpa only [sub_neg_eq_add] using hm
  have hi : Integrable (fun x ↦ b x * φ x) volume :=
    (Lp.memLp b).integrable_mul (Lp.memLp φ)
  have hb : -(∫ x, ‖b x * φ x‖) ≤ ∫ x, b x * H x := by
    rw [← integral_neg]
    apply integral_mono_ae hi.norm.neg ((Lp.memLp b).integrable_mul (Lp.memLp H))
    filter_upwards [hHAE, hu0, hφ0] with x hx hux hφx
    change -‖b x * φ x‖ ≤ b x * H x
    rw [hx]
    have hab : ‖b x * normalizedContactTest u φ k x‖ ≤ ‖b x * φ x‖ := by
      rw [norm_mul, norm_mul,
        Real.norm_of_nonneg (normalizedContactTest_nonneg _ _ _ _),
        Real.norm_of_nonneg hφx]
      exact mul_le_mul_of_nonneg_left (normalizedContactTest_le hux hφx k) (norm_nonneg _)
    exact (neg_le_neg hab).trans (by
      simpa only [Real.norm_eq_abs] using neg_abs_le (b x * normalizedContactTest u φ k x))
  have heI : (∫ x, g x * H x) = ∫ x, g x * normalizedContactTest u φ k x := by
    apply integral_congr_ae
    filter_upwards [hHAE] with x hx
    rw [hx]
  rw [heI] at hform
  change -((∫ x, ‖b x * φ x‖) / c) ≤ _
  rw [← neg_div, div_le_iff₀ hc]
  nlinarith

/-- An actual nonnegative jump form gives AE contact positivity for its genuine weak generator.

All hypotheses concern the actual increment integrals and their weak generator equations.
They allow an infinite jump measure, and impose no pointwise regularity on the state.
-/
theorem ae_nonneg_on_contact_of_L1_translationJumpForm
    (μ : Measure E) [SigmaFinite μ] (u g : L²)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hequ : ∀ v : L², Integrable (v : E → ℝ) volume →
      MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
      translationJumpForm μ u v = -(∫ x, g x * v x))
    (htest : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∃ (hφ : MemLp φ 2 volume) (b : L²),
        MemLp (translationJump (hφ.toLp φ : E → ℝ)) 2 (volume.prod μ) ∧
        ∀ v : L², Integrable (v : E → ℝ) volume →
          MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
          translationJumpForm μ (hφ.toLp φ) v = -(∫ x, b x * v x)) :
    ∀ᵐ x ∂volume, u x = 0 → 0 ≤ g x := by
  apply ae_nonneg_on_contact_of_normalized_tests u g hu0
  intro φ hφ hs hφ0
  obtain ⟨hφm, b, hφJ, hφeq⟩ := htest φ hφ hs
  let Φ := hφm.toLp φ
  have hΦ0 : ∀ᵐ x ∂volume, 0 ≤ Φ x := by
    filter_upwards [hφm.coeFn_toLp] with x hx
    rw [hx]
    exact hφ0 x
  have hΦ1 : Integrable (Φ : E → ℝ) volume := by
    apply (hφ.continuous.integrable_of_hasCompactSupport hs).congr
    exact Filter.EventuallyEq.symm hφm.coeFn_toLp
  refine ⟨∫ x, ‖b x * Φ x‖, fun k ↦ ?_⟩
  have hbound := integral_normalizedContactTest_lower_bound_of_L1_jump_form μ u g Φ b
    hu0 hΦ0 hΦ1 hu hφJ hequ hφeq k
  have he : (∫ x, g x * normalizedContactTest u Φ k x) =
      ∫ x, g x * normalizedContactTest u φ k x := by
    apply integral_congr_ae
    filter_upwards [hφm.coeFn_toLp] with x hx
    simp only [normalizedContactTest, Φ, hx]
  rwa [he] at hbound

end PartialBalayage.Maximal.Square
