/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedGeneratorConvolution
public import PartialBalayage.Maximal.Square.TranslationJumpTests

/-!
# Genuine compact-test bounds for the full source generator

Actual compact C² tests have uniformly quadratic symmetric differences.
Their spatially integrated differences obey the same finite jump moment bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual full-vector symmetric difference has its quadratic bound. -/
theorem norm_symmetricSecondDifference_le_quadratic {φ : E → ℝ} {K : ℝ≥0}
    (hφ : Differentiable ℝ φ) (hK : LipschitzWith K (fderiv ℝ φ)) (x z : E) :
    ‖φ (x + z) + φ (x - z) - 2 * φ x‖ ≤ 2 * (K : ℝ) * ‖z‖ ^ 2 := by
  let ψ (a : E) := φ (x + a) - φ x - (fderiv ℝ φ x) a
  have ht : Differentiable ℝ (fun a : E ↦ φ (x + a)) :=
    hφ.comp (by fun_prop)
  have hd : Differentiable ℝ ψ := (ht.sub_const (φ x)).sub (fderiv ℝ φ x).differentiable
  have he (a : E) : fderiv ℝ ψ a = fderiv ℝ φ (x + a) - fderiv ℝ φ x := by
    change fderiv ℝ ((fun b : E ↦ φ (x + b) - φ x) - (fderiv ℝ φ x : E → ℝ)) a = _
    rw [fderiv_sub ((ht a).sub_const (φ x)) (fderiv ℝ φ x).differentiableAt,
      fderiv_sub_const, fderiv_comp_add_left, ContinuousLinearMap.fderiv]
  have hL : LipschitzWith K (fderiv ℝ ψ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm, he a, he b]
    calc
      _ = ‖fderiv ℝ φ (x + a) - fderiv ℝ φ (x + b)‖ := by congr 1; abel
      _ ≤ (K : ℝ) * ‖(x + a) - (x + b)‖ := hK.norm_sub_le _ _
      _ = _ := by rw [add_sub_add_left_eq_sub, dist_eq_norm]
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψ'0 : fderiv ℝ ψ 0 = 0 := by rw [he]; simp
  have hb (a : E) : ‖ψ a‖ ≤ (K : ℝ) * ‖a‖ ^ 2 :=
    norm_le_quadratic_of_lipschitz_fderiv hd hL hψ0 hψ'0 a
  have hδ : φ (x + z) + φ (x - z) - 2 * φ x = ψ z + ψ (-z) := by
    dsimp [ψ]
    rw [map_neg]
    simp only [sub_eq_add_neg]
    ring
  rw [hδ]
  exact (norm_add_le _ _).trans (by
    have hn := hb (-z)
    rw [norm_neg] at hn
    nlinarith [hb z])

/-- Every actual compact C² test has a uniform true second-difference moment bound. -/
theorem exists_compactC2_symmetricSecondDifference_bound {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : E,
      ‖φ (x + z) + φ (x - z) - 2 * φ x‖ ≤ C * compensatedJumpMoment z := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hφ.fderiv_right (by norm_num)) one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  let C := max (2 * (K : ℝ)) (4 * M)
  refine ⟨C, (mul_nonneg (by norm_num) K.coe_nonneg).trans (le_max_left _ _), ?_⟩
  intro x z
  by_cases hz : ‖z‖ ^ 2 ≤ 1
  · rw [compensatedJumpMoment, min_eq_left hz]
    exact (norm_symmetricSecondDifference_le_quadratic
      (hφ.differentiable (by norm_num)) hK x z).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hz), mul_one]
    have hδ : ‖φ (x + z) + φ (x - z) - 2 * φ x‖ ≤ 4 * M := by
      calc
        _ ≤ (‖φ (x + z)‖ + ‖φ (x - z)‖) + ‖2 * φ x‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ 4 * M := by
          rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          linarith [hM (x + z), hM (x - z), hM x]
    exact hδ.trans (le_max_right _ _)

/-- Spatial integration of actual compact-test differences retains the true jump moment. -/
theorem integral_norm_symmetricSecondDifference_le_compensatedJumpMoment {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ C : ℝ, ∀ z : E, (∫ x, ‖φ (x + z) + φ (x - z) - 2 * φ x‖) ≤
      C * compensatedJumpMoment z := by
  obtain ⟨C, hC0, hC⟩ := exists_compactC2_symmetricSecondDifference_bound hφ hs
  refine ⟨3 * (volume (tsupport φ)).toReal * C, fun z ↦ ?_⟩
  let D := C * compensatedJumpMoment z
  let g := (tsupport φ).indicator (fun _ : E ↦ D)
  have hD : 0 ≤ D := mul_nonneg hC0 (compensatedJumpMoment_nonneg z)
  have hgc : Integrable g volume :=
    (integrable_indicator_iff hs.isCompact.measurableSet).mpr
      (integrableOn_const hs.isCompact.measure_lt_top.ne)
  have hgp : Integrable (fun x ↦ g (x + z)) volume :=
    (measurePreserving_add_right volume z).integrable_comp_of_integrable hgc
  have hgn : Integrable (fun x ↦ g (x + -z)) volume :=
    (measurePreserving_add_right volume (-z)).integrable_comp_of_integrable hgc
  have hiφ : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hs
  have hi : Integrable (fun x ↦ φ (x + z) + φ (x - z) - 2 * φ x) volume := by
    apply (
      (((measurePreserving_add_right volume z).integrable_comp_of_integrable hiφ).add
        ((measurePreserving_add_right volume (-z)).integrable_comp_of_integrable hiφ)).sub
          (hiφ.const_mul 2)).congr
    filter_upwards with x
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_def, sub_eq_add_neg]
  have hbound (x : E) : ‖φ (x + z) + φ (x - z) - 2 * φ x‖ ≤
      g (x + z) + g (x + -z) + g x := by
    have hg0 (a : E) : 0 ≤ g a := indicator_nonneg (fun _ _ ↦ hD) a
    by_cases hx : x ∈ tsupport φ
    · rw [show g x = D by exact indicator_of_mem hx _]
      exact (hC x z).trans (by dsimp [D]; linarith [hg0 (x + z), hg0 (x + -z)])
    by_cases hp : x + z ∈ tsupport φ
    · rw [show g (x + z) = D by exact indicator_of_mem hp _]
      exact (hC x z).trans (by dsimp [D]; linarith [hg0 x, hg0 (x + -z)])
    by_cases hn : x + -z ∈ tsupport φ
    · rw [show g (x + -z) = D by exact indicator_of_mem hn _]
      exact (hC x z).trans (by dsimp [D]; linarith [hg0 x, hg0 (x + z)])
    · simp only [sub_eq_add_neg]
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hp,
        image_eq_zero_of_notMem_tsupport hn]
      simpa only [zero_add, mul_zero, sub_zero, neg_zero, norm_zero] using
        add_nonneg (add_nonneg (hg0 (x + z)) (hg0 (x + -z))) (hg0 x)
  calc
    _ ≤ ∫ x, g (x + z) + g (x + -z) + g x :=
      integral_mono hi.norm ((hgp.add hgn).add hgc) hbound
    _ = _ := by
      have ha := integral_add (hgp.add hgn) hgc
      simp only [Pi.add_apply] at ha
      rw [ha, integral_add hgp hgn,
        (measurePreserving_add_right volume z).integral_comp
          (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding,
        (measurePreserving_add_right volume (-z)).integral_comp
          (Homeomorph.addRight (-z)).isClosedEmbedding.measurableEmbedding,
        show (∫ x : E, g x) = (volume (tsupport φ)).toReal * D by
          dsimp [g]
          rw [integral_indicator hs.isCompact.measurableSet, integral_const]
          simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]]
      dsimp [D]
      ring

/-- The full actual compact-test second difference is jointly integrable in space and source. -/
theorem integrable_prod_compactC2_sourceSecondDifference
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    Integrable (fun p : E × E ↦ φ (p.1 + p.2) + φ (p.1 - p.2) - 2 * φ p.1)
      (volume.prod μ) := by
  have hc := hφ.continuous
  have hδ : Continuous (fun p : E × E ↦ φ (p.1 + p.2) + φ (p.1 - p.2) - 2 * φ p.1) :=
    by fun_prop
  apply (integrable_prod_iff' hδ.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with z
    have hi : Integrable φ volume := hc.integrable_of_hasCompactSupport hs
    apply (
      (((measurePreserving_add_right volume z).integrable_comp_of_integrable hi).add
        ((measurePreserving_add_right volume (-z)).integrable_comp_of_integrable hi)).sub
          (hi.const_mul 2)).congr
    filter_upwards with x
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_def, sub_eq_add_neg]
  · obtain ⟨C, hC⟩ := integral_norm_symmetricSecondDifference_le_compensatedJumpMoment hφ hs
    have hg0 : Continuous
        (fun p : E × E ↦ ‖φ (p.2 + p.1) + φ (p.2 - p.1) - 2 * φ p.2‖) := by fun_prop
    have hg : StronglyMeasurable
        (fun z : E ↦ ∫ x, ‖φ (x + z) + φ (x - z) - 2 * φ x‖) :=
      hg0.stronglyMeasurable.integral_prod_right'
    apply (hm.const_mul C).mono' hg.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    exact hC z

/-- The genuine full source generator maps actual compact C² tests into ordinary L¹. -/
theorem integrable_compensatedSourceGenerator_compactC2
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    Integrable (compensatedSourceGenerator μ φ) volume :=
  (integrable_prod_compactC2_sourceSecondDifference μ hm hφ hs).integral_prod_left.const_mul _

/-- The true compact-test source generator has a genuine global bound. -/
theorem exists_bound_compensatedSourceGenerator_compactC2
    (μ : Measure E) (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖compensatedSourceGenerator μ φ x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_compactC2_symmetricSecondDifference_bound hφ hs
  refine ⟨(1 / 2 : ℝ) * (C * ∫ z, compensatedJumpMoment z ∂μ),
    mul_nonneg (by norm_num) (mul_nonneg hC0
      (integral_nonneg compensatedJumpMoment_nonneg)), fun x ↦ ?_⟩
  unfold compensatedSourceGenerator
  rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∫ z, ‖φ (x + z) + φ (x - z) - 2 * φ x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C * compensatedJumpMoment z ∂μ :=
      integral_mono (integrable_compactC2_sourceSecondDifference μ hm hφ hs x).norm
        (hm.const_mul C) (hC x)
    _ = _ := integral_const_mul _ _

/-- Every genuine compact C² test has an actual L² full-source generator image. -/
theorem memLp_compensatedSourceGenerator_compactC2
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    MemLp (compensatedSourceGenerator μ φ) 2 volume := by
  have hi := integrable_compensatedSourceGenerator_compactC2 μ hm hφ hs
  obtain ⟨C, hC0, hC⟩ := exists_bound_compensatedSourceGenerator_compactC2 μ hm hφ hs
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  apply (hi.norm.const_mul C).mono' (hi.aestronglyMeasurable.pow 2)
  filter_upwards with x
  rw [Pi.pow_apply, norm_pow]
  nlinarith [hC x, norm_nonneg (compensatedSourceGenerator μ φ x)]

end PartialBalayage.Maximal.Square
