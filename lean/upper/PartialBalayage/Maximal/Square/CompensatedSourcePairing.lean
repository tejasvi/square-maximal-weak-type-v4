/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourceBounds
public import PartialBalayage.Maximal.Square.JumpGeneratorPairing
public import PartialBalayage.Maximal.Square.TranslationJumpEnergyLimit

/-!
# Actual full-source energy of bounded smooth integrable states

A genuine quadratic second-difference bound permits Fubini against any actual
L¹ value test. Translation integration by parts then establishes the true
source energy and its generator equation, including for noncompact states.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Bounded differentiable states with Lipschitz derivative have the actual jump moment bound. -/
theorem exists_bounded_symmetricSecondDifference_bound {w : E → ℝ} {L : ℝ≥0}
    (hw : Differentiable ℝ w) (hL : LipschitzWith L (fderiv ℝ w))
    {M : ℝ} (hM : ∀ x, ‖w x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : E,
      ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z := by
  let C := max (2 * (L : ℝ)) (4 * M)
  refine ⟨C, (mul_nonneg (by norm_num) L.coe_nonneg).trans (le_max_left _ _), ?_⟩
  intro x z
  by_cases hz : ‖z‖ ^ 2 ≤ 1
  · rw [compensatedJumpMoment, min_eq_left hz]
    exact (norm_symmetricSecondDifference_le_quadratic hw hL x z).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hz), mul_one]
    have hb : ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ 4 * M := by
      calc
        _ ≤ (‖w (x + z)‖ + ‖w (x - z)‖) + ‖2 * w x‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ 4 * M := by
          rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          linarith [hM (x + z), hM (x - z), hM x]
    exact hb.trans (le_max_right _ _)

/-- Actual bounded quadratic differences are integrable against the full infinite source. -/
theorem integrable_sourceSecondDifference_of_moment_bound
    (μ : Measure E) (hm : Integrable compensatedJumpMoment μ)
    {w : E → ℝ} (hw : Continuous w) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z)
    (x : E) : Integrable (fun z ↦ w (x + z) + w (x - z) - 2 * w x) μ := by
  apply (hm.const_mul C).mono' (by fun_prop : Continuous
    (fun z ↦ w (x + z) + w (x - z) - 2 * w x)).aestronglyMeasurable
  exact Eventually.of_forall (hb x)

/-- True Fubini integrability holds against every actual L¹ value test. -/
theorem integrable_value_mul_sourceSecondDifference
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {w v : E → ℝ} (hw : Continuous w) (hv : Integrable v volume) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z) :
    Integrable (fun p : E × E ↦
      v p.1 * (w (p.1 + p.2) + w (p.1 - p.2) - 2 * w p.1)) (volume.prod μ) := by
  have hd : Continuous
      (fun p : E × E ↦ w (p.1 + p.2) + w (p.1 - p.2) - 2 * w p.1) := by fun_prop
  have ha := (hv.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ))).mul
      hd.aestronglyMeasurable
  apply (integrable_prod_iff ha).mpr
  constructor
  · filter_upwards with x
    exact (integrable_sourceSecondDifference_of_moment_bound μ hm hw hb x).const_mul (v x)
  · apply (hv.norm.mul_const (C * ∫ z, compensatedJumpMoment z ∂μ)).mono'
      ha.norm.integral_prod_right'
    filter_upwards with x
    simp only [Pi.mul_apply, Function.comp_def, norm_mul, integral_const_mul, norm_norm]
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ∫ z, C * compensatedJumpMoment z ∂μ :=
        integral_mono (integrable_sourceSecondDifference_of_moment_bound μ hm hw hb x).norm
          (hm.const_mul C) (hb x)
      _ = _ := integral_const_mul _ _

/-- The true full source generator has an integrable product with every actual L¹ test. -/
theorem integrable_value_mul_compensatedSourceGenerator
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {w v : E → ℝ} (hw : Continuous w) (hv : Integrable v volume) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z) :
    Integrable (fun x ↦ v x * compensatedSourceGenerator μ w x) volume := by
  have hi := (integrable_value_mul_sourceSecondDifference μ hm hw hv hb).integral_prod_left
  have he : (fun x : E ↦ v x * compensatedSourceGenerator μ w x) =
      fun x ↦ (1 / 2 : ℝ) * ∫ z, v x * (w (x + z) + w (x - z) - 2 * w x) ∂μ := by
    funext x
    rw [integral_const_mul]
    dsimp [compensatedSourceGenerator]
    ring
  rw [he]
  exact hi.const_mul _

/-- Translation integration by parts gives the actual full-source equation. -/
theorem integral_translationJump_mul_eq_neg_source
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {w v : E → ℝ} (hw : Continuous w) (hw2 : MemLp w 2 volume)
    (hv1 : Integrable v volume) (hv2 : MemLp v 2 volume)
    (hwJ : MemLp (translationJump w) 2 (volume.prod μ))
    (hvJ : MemLp (translationJump v) 2 (volume.prod μ)) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z) :
    (1 / 2 : ℝ) * (∫ p, translationJump w p * translationJump v p ∂volume.prod μ) =
      -(∫ x, v x * compensatedSourceGenerator μ w x) := by
  have hiJ := hwJ.integrable_mul hvJ
  have hiS := integrable_value_mul_sourceSecondDifference μ hm hw hv1 hb
  have he (z : E) : (∫ x, translationJump w (x, z) * translationJump v (x, z)) =
      -(∫ x, v x * (w (x + z) + w (x - z) - 2 * w x)) := by
    have h := integral_translationDifference_mul hv2 hw2 z
    simpa only [translationJump, translationDifference, mul_comm] using h
  calc
    _ = (1 / 2 : ℝ) * ∫ z, (∫ x, translationJump w (x, z) *
        translationJump v (x, z)) ∂μ := by
      have heJ := integral_prod_symm _ hiJ
      simp only [Pi.mul_apply] at heJ
      rw [heJ]
    _ = -((1 / 2 : ℝ) * ∫ z, (∫ x,
        v x * (w (x + z) + w (x - z) - 2 * w x)) ∂μ) := by
      simp only [he, integral_neg, mul_neg]
    _ = -(∫ x, v x * compensatedSourceGenerator μ w x) := by
      rw [← integral_integral_swap hiS, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_const_mul]
      dsimp [compensatedSourceGenerator]
      ring

/-- The genuine bounded smooth L¹ and L² state belongs to the full source energy domain. -/
theorem memLp_translationJump_of_integrable_moment_bound
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {w : E → ℝ} (hw : Continuous w) (hw1 : Integrable w volume)
    (hw2 : MemLp w 2 volume) {C : ℝ}
    (hb : ∀ x z, ‖w (x + z) + w (x - z) - 2 * w x‖ ≤ C * compensatedJumpMoment z) :
    MemLp (translationJump w) 2 (volume.prod μ) := by
  have hc : Continuous (translationJump w) := by unfold translationJump; fun_prop
  have hi := integrable_value_mul_sourceSecondDifference μ hm hw hw1 hb
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' (hc.pow 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with z
    exact (memLp_translationDifference hw2 z).integrable_sq
  · apply hi.integral_prod_right.neg.congr
    filter_upwards with z
    have he := integral_translationDifference_mul hw2 hw2 z
    simp only [translationDifference, ← pow_two] at he
    simp only [Pi.neg_apply]
    rw [← he]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.pow_apply, translationJump, Real.norm_eq_abs]
    exact (abs_of_nonneg (sq_nonneg (w (x + z) - w x))).symm

end PartialBalayage.Maximal.Square
