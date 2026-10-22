/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.FullCompensatedSource

/-!
# The true finite jump moment from a punctured positive source

Deleted-origin quadratic tests control the small-jump moment. Large cutoffs
control the tail. Both estimates follow from the actual kernel generator
pairing and local source integrability, without a finite total source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Fatou's lemma in a form retaining actual real integrability of nonnegative limits. -/
theorem integrable_nonneg_of_tendsto_integrals {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F : ℕ → X → ℝ} {f : X → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hF : ∀ k, Integrable (F k) μ) (hF0 : ∀ k, ∀ᵐ x ∂μ, 0 ≤ F k x)
    (hpt : ∀ᵐ x ∂μ, Tendsto (fun k ↦ F k x) atTop (𝓝 (f x)))
    (hlim : Tendsto (fun k ↦ ∫ x, F k x ∂μ) atTop (𝓝 c)) : Integrable f μ := by
  have hl : Tendsto (fun k ↦ ∫⁻ x, ENNReal.ofReal (F k x) ∂μ) atTop
      (𝓝 (ENNReal.ofReal c)) := by
    simpa only [← ofReal_integral_eq_lintegral_ofReal (hF _) (hF0 _), Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal c := by
    calc
      _ = ∫⁻ x, liminf (fun k ↦ ENNReal.ofReal (F k x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpt] with x hx
        exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq).symm
      _ ≤ liminf (fun k ↦ ∫⁻ x, ENNReal.ofReal (F k x) ∂μ) atTop :=
        lintegral_liminf_le' fun k ↦ (hF k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = _ := hl.liminf_eq
  exact (lintegral_ofReal_ne_top_iff_integrable hf hf0).mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)

/-- A nonnegative zero-jet test is genuinely source-integrable by the small-cutoff bound. -/
theorem integrable_nonneg_zero_jet_of_punctured_source
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (μ : Measure E)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) (hφpos : ∀ x, 0 ≤ φ x) :
    Integrable φ μ := by
  let q (k : ℕ) := quadraticContactCutoff (sourceInverseRadius k) φ
  let F (k : ℕ) (x : E) := φ x - q k x
  have hc (k : ℕ) : ContDiff ℝ 2 (q k) := quadraticContactCutoff_contDiff hφ
  have hcs (k : ℕ) : HasCompactSupport (q k) :=
    quadraticContactCutoff_hasCompactSupport (sourceInverseRadius_pos k) φ
  have hFc (k : ℕ) : ContDiff ℝ 2 (F k) := hφ.sub (hc k)
  have hFs (k : ℕ) : HasCompactSupport (F k) := hs.sub (hcs k)
  have hFa (k : ℕ) : 0 ∉ tsupport (F k) :=
    quadraticContactCutoff_complement_away_origin (sourceInverseRadius_pos k) φ
  have he (k : ℕ) : (∫ x, F k x ∂μ) =
      (∫ x, K x * coordinateStableGenerator α φ x) -
        ∫ x, K x * coordinateStableGenerator α (q k) x := by
    rw [← haway (F k) (hFc k) (hFs k) (hFa k)]
    calc
      _ = ∫ x, K x * coordinateStableGenerator α φ x -
          K x * coordinateStableGenerator α (q k) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [coordinateStableGenerator_sub hα0 hα2 hφ hs (hc k) (hcs k)]
        ring
      _ = _ := integral_sub
        (integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hφ hs)
        (integrable_kernel_mul_coordinateStableGenerator_compactC2
          hα0 hα2 hK (hc k) (hcs k))
  have hsmall : Tendsto sourceInverseRadius atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_sourceInverseRadius,
      Eventually.of_forall sourceInverseRadius_pos⟩
  have ht := (tendsto_integral_kernel_quadraticContactCutoff_generator_zero
    hα0 hα2 hK hφ hs hφ0 hφ'0).comp hsmall
  apply integrable_nonneg_of_tendsto_integrals μ hφ.continuous.aestronglyMeasurable
    (Eventually.of_forall hφpos)
    (fun k ↦ hlocal (F k) (hFc k) (hFs k) (hFa k))
  · intro k
    filter_upwards with x
    change 0 ≤ φ x - sourceCutoff 2 ((sourceInverseRadius k)⁻¹ • x) * φ x
    exact sub_nonneg.mpr (mul_le_of_le_one_left (hφpos x) (sourceCutoff_le_one 2 _))
  · filter_upwards with x
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_quadraticContactCutoff_sourceInverseRadius_zero hφ0 x)
  · have hl : Tendsto (fun k ↦ (∫ x, K x * coordinateStableGenerator α φ x) -
        ∫ x, K x * coordinateStableGenerator α (q k) x) atTop
        (𝓝 (∫ x, K x * coordinateStableGenerator α φ x)) := by
      simpa only [sub_zero, Function.comp_def, q] using tendsto_const_nhds.sub ht
    simpa only [← he] using hl

/-- The positive source tail is finite by genuine large-cutoff conservation. -/
theorem integrable_sourceCutoff_complement_of_punctured_source
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (μ : Measure E)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ) :
    Integrable (fun x : E ↦ 1 - sourceCutoff 2 x) μ := by
  let χ (k : ℕ) := sourceCutoffScale 2 (sourceInverseRadius (k + 2))
  let F (k : ℕ) (x : E) := χ k x - sourceCutoff 2 x
  have hc (k : ℕ) : ContDiff ℝ 2 (χ k) := sourceCutoffScale_contDiff 2 _
  have hcs (k : ℕ) : HasCompactSupport (χ k) :=
    sourceCutoffScale_hasCompactSupport 2 (sourceInverseRadius_pos _)
  have hχone (k : ℕ) {x : E} (hx : ‖x‖ ≤ 2) : χ k x = 1 := by
    apply sourceCutoff_eq_one_of_norm_le_one
    rw [norm_smul, Real.norm_of_nonneg (sourceInverseRadius_pos _).le]
    apply (mul_le_mul_of_nonneg_left hx (sourceInverseRadius_pos _).le).trans
    dsimp [sourceInverseRadius]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hχzero {x : E} (hx : 2 ≤ ‖x‖) : sourceCutoff 2 x = 0 :=
    CenteredMaximal.Ball.smoothBallCutoff_zero 2 0 x (by norm_num) (by norm_num)
      (by simpa only [sub_zero, one_add_one_eq_two] using hx)
  have hFc (k : ℕ) : ContDiff ℝ 2 (F k) := (hc k).sub (sourceCutoff_contDiff 2)
  have hFs (k : ℕ) : HasCompactSupport (F k) := (hcs k).sub
    (sourceCutoff_hasCompactSupport 2)
  have hFa (k : ℕ) : 0 ∉ tsupport (F k) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
    have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    simp only [F, hχone k (by linarith : ‖x‖ ≤ 2),
      sourceCutoff_eq_one_of_norm_le_one hn.le, sub_self, Pi.zero_apply]
  have hFpos (k : ℕ) (x : E) : 0 ≤ F k x := by
    by_cases hx : ‖x‖ ≤ 2
    · change 0 ≤ χ k x - sourceCutoff 2 x
      rw [hχone k hx]
      exact sub_nonneg.mpr (sourceCutoff_le_one 2 x)
    · change 0 ≤ χ k x - sourceCutoff 2 x
      rw [hχzero (le_of_not_ge hx), sub_zero]
      exact sourceCutoff_nonneg 2 _
  have he (k : ℕ) : (∫ x, F k x ∂μ) =
      (∫ x, K x * coordinateStableGenerator α (χ k) x) -
        ∫ x, K x * coordinateStableGenerator α (sourceCutoff 2) x := by
    rw [← haway (F k) (hFc k) (hFs k) (hFa k)]
    calc
      _ = ∫ x, K x * coordinateStableGenerator α (χ k) x -
          K x * coordinateStableGenerator α (sourceCutoff 2) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [coordinateStableGenerator_sub hα0 hα2 (hc k) (hcs k)
          (sourceCutoff_contDiff 2) (sourceCutoff_hasCompactSupport 2)]
        ring
      _ = _ := integral_sub
        (integrable_kernel_mul_coordinateStableGenerator_compactC2
          hα0 hα2 hK (hc k) (hcs k))
        (integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK
          (sourceCutoff_contDiff 2) (sourceCutoff_hasCompactSupport 2))
  apply integrable_nonneg_of_tendsto_integrals μ
    (continuous_const.sub (sourceCutoff_contDiff 2).continuous).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ sub_nonneg.mpr (sourceCutoff_le_one 2 x))
    (fun k ↦ hlocal (F k) (hFc k) (hFs k) (hFa k))
    (fun k ↦ Eventually.of_forall (hFpos k))
  · filter_upwards with x
    exact ((tendsto_sourceCutoffScale_sourceInverseRadius_one x).comp
      (tendsto_add_atTop_nat 2)).sub_const _
  · have ht := (tendsto_integral_kernel_large_sourceCutoff_generator_zero hα0 hα2 hK).comp
      (tendsto_add_atTop_nat 2)
    have hl : Tendsto (fun k ↦ (∫ x, K x * coordinateStableGenerator α (χ k) x) -
        ∫ x, K x * coordinateStableGenerator α (sourceCutoff 2) x) atTop
        (𝓝 (-(∫ x, K x * coordinateStableGenerator α (sourceCutoff 2) x))) := by
      simpa only [zero_sub, Function.comp_def, χ] using ht.sub_const
        (∫ x, K x * coordinateStableGenerator α (sourceCutoff 2) x)
    simpa only [← he] using hl

/-- The full actual positive punctured source has its true finite truncated second moment. -/
theorem integrable_compensatedJumpMoment_of_punctured_source
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (μ : Measure E)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ) :
    Integrable compensatedJumpMoment μ := by
  let φ (x : E) := ‖x‖ ^ 2 * sourceCutoff 2 x
  have hc : ContDiff ℝ 2 φ := (contDiff_norm_sq ℝ).mul (sourceCutoff_contDiff 2)
  have hs : HasCompactSupport φ := (sourceCutoff_hasCompactSupport 2).mul_left
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hd : fderiv ℝ φ 0 = 0 := by
    apply fderiv_even_zero
    intro x
    simp only [φ, norm_neg, sourceCutoff_even]
  have hφpos (x : E) : 0 ≤ φ x := mul_nonneg (sq_nonneg _) (sourceCutoff_nonneg 2 x)
  have hi := integrable_nonneg_zero_jet_of_punctured_source
    hα0 hα2 hK μ hlocal haway hc hs hφ0 hd hφpos
  have ht := integrable_sourceCutoff_complement_of_punctured_source
    hα0 hα2 hK μ hlocal haway
  apply (hi.add ht).mono'
    ((continuous_norm.pow 2).min continuous_const).aestronglyMeasurable
  filter_upwards with x
  change ‖compensatedJumpMoment x‖ ≤ φ x + (1 - sourceCutoff 2 x)
  rw [Real.norm_of_nonneg (compensatedJumpMoment_nonneg x)]
  change compensatedJumpMoment x ≤ ‖x‖ ^ 2 * sourceCutoff 2 x + (1 - sourceCutoff 2 x)
  have h0 := sourceCutoff_nonneg 2 x
  have h1 := sourceCutoff_le_one 2 x
  by_cases hx : ‖x‖ ^ 2 ≤ 1
  · rw [compensatedJumpMoment, min_eq_left hx]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hx)]
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hx)]
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr (le_of_not_ge hx))]

/-- Genuine punctured source data imply the full compensated identity,
with the finite jump moment derived rather than assumed. -/
theorem integral_kernel_generator_eq_compensatedSymmetricSource_of_punctured_source
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (hKeven : ∀ x, K (-x) = K x) (μ : Measure E)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, K x * coordinateStableGenerator α φ x) = compensatedSymmetricSource μ φ :=
  integral_kernel_generator_eq_compensatedSymmetricSource hα0 hα2 hK hKeven μ
    (integrable_compensatedJumpMoment_of_punctured_source hα0 hα2 hK μ hlocal haway)
    haway hφ hs

end PartialBalayage.Maximal.Square
