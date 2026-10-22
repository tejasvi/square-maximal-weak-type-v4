/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SourceMomentIntegrability
public import PartialBalayage.Maximal.Square.TranslationJumpContact
public import PartialBalayage.Maximal.Square.JumpCompactTests

/-!
# Actual compact tests in the full source jump form

The true truncated second moment makes every compact Lipschitz function an
admissible test for the source's full vector increments, even when its jump
measure has infinite mass near zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal NNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The integrated quadratic bound holds for every actual vector displacement. -/
theorem integral_translationDifference_sq_le_quadratic {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) (a : E) :
    (∫ x : E, translationDifference φ a x ^ 2) ≤
      (2 * (volume (tsupport φ)).toReal * (K : ℝ) ^ 2) * ‖a‖ ^ 2 := by
  let C := (K : ℝ) ^ 2 * ‖a‖ ^ 2
  let g := (tsupport φ).indicator (fun _ : E ↦ C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgc : Integrable g volume :=
    (integrable_indicator_iff hs.isCompact.measurableSet).mpr
      (integrableOn_const hs.isCompact.measure_lt_top.ne)
  have hgt : Integrable (fun x ↦ g (x + a)) volume :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable hgc
  have hm := hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)
  have hi := (memLp_translationDifference hm a).integrable_sq
  have hb (x : E) : translationDifference φ a x ^ 2 ≤ C := by
    have h := hφ.norm_sub_le (x + a) x
    rw [add_sub_cancel_left, Real.norm_eq_abs] at h
    have hp := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (K : ℝ) * ‖a‖) |>.mpr h
    simpa only [translationDifference, C, mul_pow, sq_abs] using hp
  have hb2 (x : E) : translationDifference φ a x ^ 2 ≤ g x + g (x + a) := by
    by_cases hx : x ∈ tsupport φ
    · rw [show g x = C by exact indicator_of_mem hx _]
      exact (hb x).trans (le_add_of_nonneg_right (indicator_nonneg (fun _ _ ↦ hC) _))
    · by_cases hy : x + a ∈ tsupport φ
      · rw [show g x = 0 by exact indicator_of_notMem hx _,
          show g (x + a) = C by exact indicator_of_mem hy _, zero_add]
        exact hb x
      · rw [show g x = 0 by exact indicator_of_notMem hx _,
          show g (x + a) = 0 by exact indicator_of_notMem hy _, zero_add]
        rw [translationDifference, image_eq_zero_of_notMem_tsupport hy,
          image_eq_zero_of_notMem_tsupport hx, sub_self, zero_pow two_ne_zero]
  calc
    _ ≤ ∫ x : E, g x + g (x + a) := integral_mono hi (hgc.add hgt) hb2
    _ = _ := by
      rw [integral_add hgc hgt,
        (measurePreserving_add_right volume a).integral_comp
          (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding,
        show (∫ x : E, g x) = (volume (tsupport φ)).toReal * C by
          dsimp [g]
          rw [integral_indicator hs.isCompact.measurableSet, integral_const]
          simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]]
      dsimp [C]
      ring

/-- The true integrated increment square is controlled by the truncated second moment. -/
theorem integral_translationDifference_sq_le_compensatedJumpMoment
    {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) :
    ∃ C : ℝ, ∀ a : E, (∫ x : E, translationDifference φ a x ^ 2) ≤
      C * compensatedJumpMoment a := by
  let A := 2 * (volume (tsupport φ)).toReal * (K : ℝ) ^ 2
  let B := 4 * ∫ x : E, φ x ^ 2
  refine ⟨max A B, fun a ↦ ?_⟩
  by_cases ha : ‖a‖ ^ 2 ≤ 1
  · rw [compensatedJumpMoment, min_eq_left ha]
    exact (integral_translationDifference_sq_le_quadratic hφ hs a).trans
      (mul_le_mul_of_nonneg_right (le_max_left A B) (sq_nonneg _))
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge ha), mul_one]
    exact (integral_translationDifference_sq_le_four
      (hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)) a).trans
        (le_max_right A B)

/-- Every true compact Lipschitz test has square-integrable full vector source increments. -/
theorem memLp_translationJump_of_compact_lipschitz
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) :
    MemLp (translationJump φ) 2 (volume.prod μ) := by
  have hφc := hφ.continuous
  have hc : Continuous (translationJump φ) := by unfold translationJump; fun_prop
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' (hc.pow 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with a
    exact (memLp_translationDifference
      (hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)) a).integrable_sq
  · obtain ⟨C, hC⟩ := integral_translationDifference_sq_le_compensatedJumpMoment hφ hs
    have hg : StronglyMeasurable (fun a : E ↦ ∫ x : E, translationJump φ (x, a) ^ 2) :=
      (by unfold translationJump; fun_prop : Continuous
        (fun p : E × E ↦ translationJump φ (p.2, p.1) ^ 2)).stronglyMeasurable.integral_prod_right'
    have hgi : Integrable (fun a : E ↦ ∫ x : E, translationJump φ (x, a) ^ 2) μ := by
      apply (hm.const_mul C).mono' hg.aestronglyMeasurable
      filter_upwards with a
      have hn : 0 ≤ ∫ x : E, translationJump φ (x, a) ^ 2 :=
        integral_nonneg (fun x ↦ sq_nonneg _)
      change ‖∫ x : E, translationJump φ (x, a) ^ 2‖ ≤ C * compensatedJumpMoment a
      rw [Real.norm_of_nonneg hn]
      simpa only [translationJump,
        translationDifference] using hC a
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hgi

/-- Genuine compact C² functions supply actual L² source-form test classes. -/
theorem exists_translationJump_compactC2Test
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ hφm : MemLp φ 2 volume,
      MemLp (translationJump (hφm.toLp φ : E → ℝ)) 2 (volume.prod μ) := by
  obtain ⟨K, hLip⟩ := hφ.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  let hv := hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)
  refine ⟨hv, (memLp_translationJump_of_compact_lipschitz μ hm hLip hs).ae_eq ?_⟩
  filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae hv.coeFn_toLp,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hv.coeFn_toLp]
      with p hx hy
  simp only [translationJump, hx, hy]

end PartialBalayage.Maximal.Square
