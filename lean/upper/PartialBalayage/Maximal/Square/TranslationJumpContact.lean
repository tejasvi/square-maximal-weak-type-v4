/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpContactLimit
public import PartialBalayage.Maximal.Square.JumpEnergy

/-!
# Contact positivity for actual translation jump forms

The jump measure may have infinite mass at the origin. Square-integrable physical
increments suffice for the mixed-sign inequality and the normalized obstacle tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- Actual increments for a spatial point and a full vector jump. -/
def translationJump (u : E → ℝ) (p : E × E) : ℝ := u (p.1 + p.2) - u p.1

theorem quasiMeasurePreserving_translationJumpPoint (μ : Measure E) [SigmaFinite μ] :
    QuasiMeasurePreserving (fun p : E × E ↦ p.1 + p.2) (volume.prod μ) volume := by
  apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
  filter_upwards with z
  exact (measurePreserving_add_right volume z).quasiMeasurePreserving

theorem aestronglyMeasurable_translationJump (μ : Measure E) [SigmaFinite μ] (u : L²) :
    AEStronglyMeasurable (translationJump (u : E → ℝ)) (volume.prod μ) :=
  ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_translationJumpPoint μ)).sub
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)))

/-- The genuine symmetric bilinear form, with all jump mass retained. -/
def translationJumpForm (μ : Measure E) (u v : L²) : ℝ :=
  (1 / 2 : ℝ) * ∫ p, translationJump (u : E → ℝ) p *
    translationJump (v : E → ℝ) p ∂volume.prod μ

theorem memLp_translationJump_smul_sub (μ : Measure E) [SigmaFinite μ]
    (u v : L²) (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hv : MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ)) (c : ℝ) :
    MemLp (translationJump ((c • u - v : L²) : E → ℝ)) 2 (volume.prod μ) := by
  apply (hu.const_mul c |>.sub hv).ae_eq
  have he := Lp.coeFn_sub (c • u) v
  have hs := Lp.coeFn_smul c u
  filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae he,
    (quasiMeasurePreserving_translationJumpPoint μ).ae hs,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hs]
      with p hx hy hsx hsy
  simp only [translationJump, hx, hy, Pi.sub_apply, hsx, hsy, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The negative part is an actual `L²` class, with the same singular jump measure. -/
def translationJumpNegativePart (u : L²) : L² :=
  lipschitzWith_negative_part.compLp (by simp) u

theorem translationJumpNegativePart_ae (u : L²) :
    (translationJumpNegativePart u : E → ℝ) =ᵐ[volume] fun x ↦ max (-u x) 0 :=
  lipschitzWith_negative_part.coeFn_compLp (by simp) u

theorem memLp_translationJump_negativePart (μ : Measure E) [SigmaFinite μ]
    (u : L²) (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ)) :
    MemLp (translationJump (translationJumpNegativePart u : E → ℝ)) 2 (volume.prod μ) := by
  apply hu.norm.mono' (aestronglyMeasurable_translationJump μ _)
  have he := translationJumpNegativePart_ae u
  filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae he] with p hx hy
  simp only [translationJump, hx, hy]
  simpa only [NNReal.coe_one, one_mul] using lipschitzWith_negative_part.norm_sub_le
    (u (p.1 + p.2)) (u p.1)

private theorem negativePart_increment_mul_nonpos (a b : ℝ) :
    (a - b) * (max (-a) 0 - max (-b) 0) ≤ 0 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb)]
    nlinarith [sq_nonneg (a - b)]
  · rw [max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
    nlinarith
  · rw [max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb)]
    nlinarith
  · rw [max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
    simp

/-- The mixed-sign inequality follows pointwise for the actual full vector increments. -/
theorem translationJumpForm_negativePart_nonpos (μ : Measure E) [SigmaFinite μ]
    (u : L²) : translationJumpForm μ u (translationJumpNegativePart u) ≤ 0 := by
  unfold translationJumpForm
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply integral_nonpos_of_ae
  have he := translationJumpNegativePart_ae u
  filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae he] with p hx hy
  simp only [translationJump, hx, hy]
  exact negativePart_increment_mul_nonpos _ _

/-- Bilinearity in the first argument uses true integrability of the increment products. -/
theorem translationJumpForm_smul_sub_left (μ : Measure E) [SigmaFinite μ]
    (u v w : L²) (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hv : MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ))
    (hw : MemLp (translationJump (w : E → ℝ)) 2 (volume.prod μ)) (c : ℝ) :
    translationJumpForm μ (c • u - v) w =
      c * translationJumpForm μ u w - translationJumpForm μ v w := by
  have he : translationJump ((c • u - v : L²) : E → ℝ) =ᵐ[volume.prod μ]
      fun p ↦ c * translationJump (u : E → ℝ) p - translationJump (v : E → ℝ) p := by
    have hsub := Lp.coeFn_sub (c • u) v
    have hs := Lp.coeFn_smul c u
    filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae hsub,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hsub,
      (quasiMeasurePreserving_translationJumpPoint μ).ae hs,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hs]
        with p hx hy hsx hsy
    simp only [translationJump, hx, hy, Pi.sub_apply, hsx, hsy, Pi.smul_apply,
      smul_eq_mul]
    ring
  unfold translationJumpForm
  have hI : (∫ p, translationJump ((c • u - v : L²) : E → ℝ) p *
      translationJump (w : E → ℝ) p ∂volume.prod μ) =
        c * (∫ p, translationJump (u : E → ℝ) p *
          translationJump (w : E → ℝ) p ∂volume.prod μ) -
        ∫ p, translationJump (v : E → ℝ) p *
          translationJump (w : E → ℝ) p ∂volume.prod μ := by
    calc
      _ = ∫ p, c * (translationJump (u : E → ℝ) p *
          translationJump (w : E → ℝ) p) -
          translationJump (v : E → ℝ) p * translationJump (w : E → ℝ) p
          ∂volume.prod μ := by
        apply integral_congr_ae
        filter_upwards [he] with p hp
        rw [hp]
        ring
      _ = _ := by
        simpa only [Pi.mul_apply, Pi.sub_apply, integral_const_mul] using
          integral_sub ((hu.integrable_mul hw).const_mul c) (hv.integrable_mul hw)
  rw [hI]
  ring

/-- Actual weak generator pairings imply the vanishing-error normalized contact estimate. -/
theorem integral_normalizedContactTest_lower_bound_of_jump_form
    (μ : Measure E) [SigmaFinite μ] (u g φ b : L²)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x) (hφ0 : ∀ᵐ x ∂volume, 0 ≤ φ x)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hφ : MemLp (translationJump (φ : E → ℝ)) 2 (volume.prod μ))
    (hequ : ∀ v : L², MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
      translationJumpForm μ u v = -(∫ x, g x * v x))
    (heqφ : ∀ v : L², MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
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
  have hform : c * (-(∫ x, g x * H x)) + (∫ x, b x * H x) ≤ 0 := by
    have hm := translationJumpForm_negativePart_nonpos μ W
    rw [translationJumpForm_smul_sub_left μ u φ H hu hφ hH c,
      hequ H hH, heqφ H hH] at hm
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
theorem ae_nonneg_on_contact_of_translationJumpForm
    (μ : Measure E) [SigmaFinite μ] (u g : L²)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hequ : ∀ v : L², MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
      translationJumpForm μ u v = -(∫ x, g x * v x))
    (htest : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∃ (hφ : MemLp φ 2 volume) (b : L²),
        MemLp (translationJump (hφ.toLp φ : E → ℝ)) 2 (volume.prod μ) ∧
        ∀ v : L², MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
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
  refine ⟨∫ x, ‖b x * Φ x‖, fun k ↦ ?_⟩
  have hbound := integral_normalizedContactTest_lower_bound_of_jump_form μ u g Φ b
    hu0 hΦ0 hu hφJ hequ hφeq k
  have he : (∫ x, g x * normalizedContactTest u Φ k x) =
      ∫ x, g x * normalizedContactTest u φ k x := by
    apply integral_congr_ae
    filter_upwards [hφm.coeFn_toLp] with x hx
    simp only [normalizedContactTest, Φ, hx]
  rwa [he] at hbound

end PartialBalayage.Maximal.Square
