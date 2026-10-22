/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedJumpSource

/-!
# Actual symmetric compensated kernel source

Large cutoffs remove the possible point-mass term. Evenness removes the first
jet. The resulting identity retains the genuine infinite jump measure through
its truncated second moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- A differentiable even test has an actual zero derivative at the origin. -/
theorem fderiv_even_zero {φ : E → ℝ} (heven : ∀ x, φ (-x) = φ x) :
    fderiv ℝ φ 0 = 0 := by
  have hfun : (fun x : E ↦ φ ((-1 : ℝ) • x)) = φ := by
    funext x
    simpa only [neg_one_smul] using heven x
  have hd := fderiv_comp_smul (-1 : ℝ) (f := φ) (x := (0 : E))
  rw [hfun, smul_zero, neg_one_smul] at hd
  have hs : (2 : ℝ) • fderiv ℝ φ 0 = 0 := by
    rw [two_smul]
    calc
      _ = -fderiv ℝ φ 0 + fderiv ℝ φ 0 := congrArg (fun A ↦ A + fderiv ℝ φ 0) hd
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

theorem sourceCutoff_even (x : E) : sourceCutoff 2 (-x) = sourceCutoff 2 x := by
  unfold sourceCutoff CenteredMaximal.Ball.smoothBallCutoff
  simp only [sub_zero, norm_neg]

theorem sourceCutoffScale_even (s : ℝ) (x : E) :
    sourceCutoffScale 2 s (-x) = sourceCutoffScale 2 s x := by
  simp only [sourceCutoffScale, smul_neg, sourceCutoff_even]

theorem tendsto_sourceCutoffScale_sourceInverseRadius_one (x : E) :
    Tendsto (fun k ↦ sourceCutoffScale 2 (sourceInverseRadius k) x) atTop (𝓝 1) := by
  have harg : Tendsto (fun k ↦ sourceInverseRadius k • x) atTop (𝓝 0) := by
    simpa only [zero_smul] using tendsto_sourceInverseRadius.smul_const x
  simpa only [sourceCutoffScale, sourceCutoff_zero, Function.comp_def] using
    (sourceCutoff_contDiff 2).continuous.continuousAt.tendsto.comp harg

/-- Actual large cutoffs have zero limiting generator pairing against every `L¹` kernel. -/
theorem tendsto_integral_kernel_large_sourceCutoff_generator_zero
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ} (hK : Integrable K volume) :
    Tendsto (fun k ↦ ∫ x, K x * coordinateStableGenerator α
      (sourceCutoffScale 2 (sourceInverseRadius k)) x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := sourceCutoff_coordinateStableGenerator_bound hα0 hα2
  have hC0 : 0 ≤ C := by
    have hb := hC 1 (by norm_num) 0
    simpa only [inv_one, Real.one_rpow, mul_one] using (norm_nonneg _).trans hb
  have he (k : ℕ) : sourceCutoffScale 2 (sourceInverseRadius k) =
      fun x : E ↦ sourceCutoff 2 (((k : ℝ) + 1)⁻¹ • x) := by
    funext x
    simp only [sourceCutoffScale, sourceInverseRadius, one_div]
  have hb (k : ℕ) (x : E) :
      ‖coordinateStableGenerator α (sourceCutoffScale 2 (sourceInverseRadius k)) x‖ ≤ C := by
    rw [he]
    exact (hC ((k : ℝ) + 1) (by positivity) x).trans (by
      have hr : ((k : ℝ) + 1) ^ (-α) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hC0)
  have hp (x : E) : Tendsto (fun k ↦ coordinateStableGenerator α
      (sourceCutoffScale 2 (sourceInverseRadius k)) x) atTop (𝓝 0) := by
    simp_rw [he]
    exact (tendsto_sourceCutoff_coordinateStableGenerator_zero hα0 hα2 x).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun k ↦ ∫ x, K x * coordinateStableGenerator α
      (sourceCutoffScale 2 (sourceInverseRadius k)) x) atTop (𝓝 (∫ x : E, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖K x‖ * C)
    · intro k
      exact hK.aestronglyMeasurable.mul
        (stronglyMeasurable_coordinateStableGenerator α
          (sourceCutoffScale_contDiff 2 _).continuous).aestronglyMeasurable
    · exact hK.norm.mul_const C
    · intro k
      filter_upwards with x
      change ‖K x * coordinateStableGenerator α
        (sourceCutoffScale 2 (sourceInverseRadius k)) x‖ ≤ ‖K x‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb k x) (norm_nonneg _)
    · filter_upwards with x
      simpa only [mul_zero] using (hp x).const_mul (K x)
  simpa only [integral_zero] using ht

/-- The actual compensated test and all large-cutoff versions have a common Lévy bound. -/
theorem exists_compensated_test_moment_bound {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hφ'0 : fderiv ℝ φ 0 = 0) :
    ∃ C : ℝ, (∀ x, ‖φ x - φ 0‖ ≤ C * compensatedJumpMoment x) ∧
      ∀ k : ℕ, ∀ x : E,
        ‖φ x - φ 0 * sourceCutoffScale 2 (sourceInverseRadius k) x‖ ≤
          C * compensatedJumpMoment x := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hφ.fderiv_right (by norm_num)) one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  let C := max (L : ℝ) (M + ‖φ 0‖)
  have hquad (x : E) : ‖φ x - φ 0‖ ≤ (L : ℝ) * ‖x‖ ^ 2 := by
    apply norm_le_quadratic_of_lipschitz_fderiv
      ((hφ.differentiable (by norm_num)).sub_const (φ 0))
    · have he : fderiv ℝ (fun y ↦ φ y - φ 0) = fderiv ℝ φ :=
        funext fun y ↦ fderiv_sub_const (φ 0)
      rw [he]
      exact hL
    · simp
    · simpa only [fderiv_sub_const] using hφ'0
  have hbound (x : E) : ‖φ x - φ 0‖ ≤ C * compensatedJumpMoment x := by
    by_cases hx : ‖x‖ ^ 2 ≤ 1
    · rw [compensatedJumpMoment, min_eq_left hx]
      exact (hquad x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hx), mul_one]
      have ha : ‖φ x‖ + ‖φ 0‖ ≤ M + ‖φ 0‖ := add_le_add (hM x) le_rfl
      exact (norm_sub_le _ _).trans (ha.trans (le_max_right _ _))
  refine ⟨C, hbound, ?_⟩
  intro k x
  by_cases hx : ‖x‖ ^ 2 ≤ 1
  · have hn : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    have harg : ‖sourceInverseRadius k • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (sourceInverseRadius_pos k).le]
      exact (mul_le_mul (sourceInverseRadius_le_one k) hn (norm_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
    rw [sourceCutoffScale, sourceCutoff_eq_one_of_norm_le_one harg, mul_one]
    exact hbound x
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hx), mul_one]
    have hχ : ‖sourceCutoffScale 2 (sourceInverseRadius k) x‖ ≤ 1 := by
      rw [sourceCutoffScale, Real.norm_of_nonneg (sourceCutoff_nonneg 2 _)]
      exact sourceCutoff_le_one 2 _
    calc
      _ ≤ ‖φ x‖ + ‖φ 0 * sourceCutoffScale 2 (sourceInverseRadius k) x‖ := norm_sub_le _ _
      _ ≤ M + ‖φ 0‖ := by
        rw [norm_mul]
        have hm := mul_le_mul_of_nonneg_left hχ (norm_nonneg (φ 0))
        rw [mul_one] at hm
        exact add_le_add (hM x) hm
      _ ≤ C := le_max_right _ _

/-- Large-cutoff conservation removes the value at zero for every zero-derivative test. -/
theorem integral_kernel_generator_eq_compensated_of_derivative_zero
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (μ : Measure E) (hm : Integrable compensatedJumpMoment μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ'0 : fderiv ℝ φ 0 = 0) :
    (∫ x, K x * coordinateStableGenerator α φ x) = ∫ x, φ x - φ 0 ∂μ := by
  let χ (k : ℕ) := sourceCutoffScale 2 (sourceInverseRadius k)
  let q (k : ℕ) (x : E) := φ x - φ 0 * χ k x
  have he (k : ℕ) :
      (∫ x, K x * coordinateStableGenerator α φ x) -
        φ 0 * (∫ x, K x * coordinateStableGenerator α (χ k) x) = ∫ x, q k x ∂μ := by
    have hχ := sourceCutoffScale_contDiff 2 (sourceInverseRadius k)
    have hχs := sourceCutoffScale_hasCompactSupport 2 (sourceInverseRadius_pos k)
    have hψ : ContDiff ℝ 2 (fun x ↦ φ 0 * χ k x) := contDiff_const.mul hχ
    have hψs : HasCompactSupport (fun x ↦ φ 0 * χ k x) := hχs.mul_left
    have hq : ContDiff ℝ 2 (q k) := hφ.sub hψ
    have hqs : HasCompactSupport (q k) := hs.sub hψs
    have hq0 : q k 0 = 0 := by simp [q, χ, sourceCutoffScale_zero]
    have hχ'0 : fderiv ℝ (χ k) 0 = 0 := fderiv_even_zero (sourceCutoffScale_even _)
    have hq'0 : fderiv ℝ (q k) 0 = 0 := by
      have hd := ((hφ.differentiable (by norm_num) 0).hasFDerivAt).sub
        ((hχ.differentiable (by norm_num) 0).hasFDerivAt.const_mul (φ 0))
      change fderiv ℝ (sourceCutoffScale 2 (sourceInverseRadius k)) 0 = 0 at hχ'0
      change fderiv ℝ (φ - fun y ↦ φ 0 * sourceCutoffScale 2 (sourceInverseRadius k) y) 0 = 0
      simpa only [hφ'0, hχ'0, smul_zero, sub_zero] using hd.fderiv
    have hi := integral_kernel_generator_eq_integral_of_zero_jet
      hα0 hα2 hK μ hm haway hq hqs hq0 hq'0
    have hl : (∫ x, K x * coordinateStableGenerator α (q k) x) =
        (∫ x, K x * coordinateStableGenerator α φ x) -
          φ 0 * (∫ x, K x * coordinateStableGenerator α (χ k) x) := by
      calc
        _ = ∫ x, K x * coordinateStableGenerator α φ x -
            φ 0 * (K x * coordinateStableGenerator α (χ k) x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [coordinateStableGenerator_sub hα0 hα2 hφ hs hψ hψs,
            coordinateStableGenerator_const_mul]
          ring
        _ = _ := by
          rw [integral_sub
            (integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hφ hs)
            ((integrable_kernel_mul_coordinateStableGenerator_compactC2
              hα0 hα2 hK hχ hχs).const_mul (φ 0)), integral_const_mul]
    rwa [hl] at hi
  obtain ⟨C, hCb, hCq⟩ := exists_compensated_test_moment_bound hφ hs hφ'0
  have hlim : Tendsto (fun k ↦ ∫ x, q k x ∂μ) atTop
      (𝓝 (∫ x, φ x - φ 0 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ C * compensatedJumpMoment x)
    · intro k
      exact (hφ.continuous.sub (continuous_const.mul
        (sourceCutoffScale_contDiff 2 _).continuous)).aestronglyMeasurable
    · exact hm.const_mul C
    · intro k
      exact Eventually.of_forall (hCq k)
    · filter_upwards with x
      have hp := (tendsto_sourceCutoffScale_sourceInverseRadius_one x).const_mul (φ 0)
      simpa only [mul_one] using tendsto_const_nhds.sub hp
  have hleft : Tendsto (fun k ↦ (∫ x, K x * coordinateStableGenerator α φ x) -
      φ 0 * (∫ x, K x * coordinateStableGenerator α (χ k) x)) atTop
      (𝓝 (∫ x, K x * coordinateStableGenerator α φ x)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub
      ((tendsto_integral_kernel_large_sourceCutoff_generator_zero hα0 hα2 hK).const_mul (φ 0))
  exact tendsto_nhds_unique hleft (hlim.congr' (Eventually.of_forall fun k ↦ (he k).symm))

end PartialBalayage.Maximal.Square
