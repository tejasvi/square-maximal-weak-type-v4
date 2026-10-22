/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourceTests

/-!
# Genuine full-source graph states and their energy bound

Actual bounded quadratic differences place an integrable L² state in the
source graph. A genuine L² source image gives its weak equation and the true
energy bound needed for strong mollification limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- A genuine smooth value and actual L² source image yield the complete integrable weak form. -/
theorem compensatedSource_state_weak_equation
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {w : E → ℝ} (hw : Continuous w) (hw1 : Integrable w volume)
    (hw2 : MemLp w 2 volume) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z)
    (g : L²) (hg : g =ᵐ[volume] compensatedSourceGenerator μ w) :
    ∃ hJ : MemLp (translationJump (hw2.toLp w : E → ℝ)) 2 (volume.prod μ),
      (∀ v : L², Integrable (v : E → ℝ) volume →
        MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
          translationJumpForm μ (hw2.toLp w) v = -(∫ x, g x * v x)) ∧
      ‖hJ.toLp (translationJump (hw2.toLp w : E → ℝ))‖ ^ 2 ≤
        2 * ‖g‖ * ‖hw2.toLp w‖ := by
  have hrawJ := memLp_translationJump_of_integrable_moment_bound μ hm hw hw1 hw2 hb
  have hJ := hrawJ.ae_eq (translationJump_congr_ae μ hw2.coeFn_toLp).symm
  have heq (v : L²) (hv1 : Integrable (v : E → ℝ) volume)
      (hvJ : MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ)) :
      translationJumpForm μ (hw2.toLp w) v = -(∫ x, g x * v x) := by
    have he := integral_translationJump_mul_eq_neg_source μ hm hw hw2
      hv1 (Lp.memLp v) hrawJ hvJ hb
    unfold translationJumpForm
    calc
      _ = (1 / 2 : ℝ) * ∫ p, translationJump w p *
          translationJump (v : E → ℝ) p ∂volume.prod μ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [translationJump_congr_ae μ hw2.coeFn_toLp] with p hp
        rw [hp]
      _ = -(∫ x, v x * compensatedSourceGenerator μ w x) := he
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        rw [hx, mul_comm]
  refine ⟨hJ, heq, ?_⟩
  have hiW : Integrable (hw2.toLp w : E → ℝ) volume := hw1.congr hw2.coeFn_toLp.symm
  have hs := heq (hw2.toLp w) hiW hJ
  rw [translationJumpForm_self_eq_norm_sq μ _ hJ] at hs
  have hin : (∫ x, g x * hw2.toLp w x) = ⟪g, hw2.toLp w⟫ := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  rw [hin] at hs
  have hnorm : ‖inner ℝ g (hw2.toLp w)‖ ≤ ‖g‖ * ‖hw2.toLp w‖ :=
    norm_inner_le_norm g (hw2.toLp w)
  have hneg : -⟪g, hw2.toLp w⟫ ≤ ‖⟪g, hw2.toLp w⟫‖ := by
    simpa only [Real.norm_eq_abs] using neg_le_abs ⟪g, hw2.toLp w⟫
  nlinarith

end PartialBalayage.Maximal.Square
