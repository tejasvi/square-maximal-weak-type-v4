/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.QuadraticContactCutoff
public import PartialBalayage.Maximal.Square.GeneratorAlgebra

/-!
# Genuine compensated source passage through the origin

The punctured positive source may have infinite total mass. Its finite truncated
second moment controls quadratic-contact tests. Actual deleted-origin cutoffs
recover their source identity without assuming a finite Radon source at zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The true Lévy integrability weight; it does not require finite total source mass. -/
def compensatedJumpMoment (x : E) : ℝ := min (‖x‖ ^ 2) 1

theorem compensatedJumpMoment_nonneg (x : E) : 0 ≤ compensatedJumpMoment x :=
  le_min (sq_nonneg _) (by norm_num)

/-- Actual quadratic-contact compact tests are integrable against a possibly infinite source. -/
theorem integrable_compactC2_zero_jet_of_compensatedJumpMoment (μ : Measure E)
    (hm : Integrable compensatedJumpMoment μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) : Integrable φ μ := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hφ.fderiv_right (by norm_num)) one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  let C := max (K : ℝ) M
  apply (hm.const_mul C).mono' hφ.continuous.aestronglyMeasurable
  filter_upwards with x
  change ‖φ x‖ ≤ C * compensatedJumpMoment x
  by_cases hx : ‖x‖ ^ 2 ≤ 1
  · rw [compensatedJumpMoment, min_eq_left hx]
    exact (norm_le_quadratic_of_lipschitz_fderiv (hφ.differentiable (by norm_num))
      hK hφ0 hφ'0 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · rw [compensatedJumpMoment, min_eq_right (le_of_not_ge hx), mul_one]
    exact (hM x).trans (le_max_right _ _)

theorem sourceCutoff_eq_one_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    sourceCutoff 2 x = 1 :=
  CenteredMaximal.Ball.smoothBallCutoff_one 2 0 x (by norm_num) (by norm_num)
    (by simpa only [mem_closedBall, dist_zero_right] using hx)

/-- The actual complementary test is supported away from the origin. -/
theorem quadraticContactCutoff_complement_away_origin {ε : ℝ} (hε : 0 < ε)
    (φ : E → ℝ) : 0 ∉ tsupport (fun x ↦ φ x - quadraticContactCutoff ε φ x) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [ball_mem_nhds (0 : E) hε] with x hx
  have hnorm : ‖x‖ < ε := by simpa only [mem_ball, dist_zero_right] using hx
  have hs : ‖ε⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    apply (inv_mul_le_iff₀ hε).mpr
    linarith
  simp only [quadraticContactCutoff, sourceCutoff_eq_one_of_norm_le_one hs, one_mul,
    sub_self, Pi.zero_apply]

/-- The actual shrinking cutoffs remove every fixed nonzero point eventually. -/
theorem tendsto_quadraticContactCutoff_sourceInverseRadius_zero {φ : E → ℝ}
    (hφ0 : φ 0 = 0) (x : E) :
    Tendsto (fun k ↦ quadraticContactCutoff (sourceInverseRadius k) φ x) atTop (𝓝 0) := by
  by_cases hx : x = 0
  · simp only [hx, quadraticContactCutoff, hφ0, mul_zero]
    exact tendsto_const_nhds
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ht : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) * ‖x‖) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).atTop_mul_const hn
    have he : ∀ᶠ k : ℕ in atTop,
        quadraticContactCutoff (sourceInverseRadius k) φ x = 0 := by
      filter_upwards [ht.eventually (eventually_ge_atTop (2 : ℝ))] with k hk
      have hnorm : 2 ≤ ‖(sourceInverseRadius k)⁻¹ • x‖ := by
        simpa only [sourceInverseRadius, one_div, inv_inv, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < (k : ℝ) + 1)] using hk
      have hz : sourceCutoff 2 ((sourceInverseRadius k)⁻¹ • x) = 0 :=
        CenteredMaximal.Ball.smoothBallCutoff_zero 2 0 _ (by norm_num) (by norm_num)
          (by simpa only [sub_zero, one_add_one_eq_two] using hnorm)
      simp only [quadraticContactCutoff, hz, zero_mul]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

theorem integrable_quadraticContactCutoff (μ : Measure E) {φ : E → ℝ}
    (hφ : Integrable φ μ) (ε : ℝ) :
    Integrable (quadraticContactCutoff ε φ) μ := by
  apply hφ.bdd_mul (c := (1 : ℝ))
    (((sourceCutoff_contDiff 2).continuous.comp (continuous_const_smul ε⁻¹)).aestronglyMeasurable)
  filter_upwards with x
  change ‖sourceCutoff 2 (ε⁻¹ • x)‖ ≤ 1
  rw [Real.norm_of_nonneg (sourceCutoff_nonneg 2 _)]
  exact sourceCutoff_le_one 2 _

/-- The removed part tends to zero against the genuine infinite source by dominated convergence. -/
theorem tendsto_integral_quadraticContactCutoff_zero (μ : Measure E) {φ : E → ℝ}
    (hφ : Integrable φ μ) (hc : Continuous φ) (hφ0 : φ 0 = 0) :
    Tendsto (fun k ↦ ∫ x, quadraticContactCutoff (sourceInverseRadius k) φ x ∂μ)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun k ↦ ∫ x, quadraticContactCutoff (sourceInverseRadius k) φ x ∂μ)
      atTop (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖φ x‖)
    · intro k
      exact (((sourceCutoff_contDiff 2).continuous.comp
        (continuous_const_smul (sourceInverseRadius k)⁻¹)).aestronglyMeasurable).mul
          hc.aestronglyMeasurable
    · exact hφ.norm
    · intro k
      filter_upwards with x
      rw [quadraticContactCutoff, norm_mul]
      have hb : ‖sourceCutoff 2 ((sourceInverseRadius k)⁻¹ • x)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (sourceCutoff_nonneg 2 _)]
        exact sourceCutoff_le_one 2 _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (φ x))
    · filter_upwards with x
      exact tendsto_quadraticContactCutoff_sourceInverseRadius_zero hφ0 x
  simpa only [integral_zero] using ht

/-- A true punctured source identity extends to every compact C² test with zero first jet. -/
theorem integral_kernel_generator_eq_integral_of_zero_jet
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (μ : Measure E)
    (hm : Integrable compensatedJumpMoment μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) :
    (∫ x, K x * coordinateStableGenerator α φ x) = ∫ x, φ x ∂μ := by
  have hiφ := integrable_compactC2_zero_jet_of_compensatedJumpMoment μ hm
    hφ hs hφ0 hφ'0
  let h (k : ℕ) := quadraticContactCutoff (sourceInverseRadius k) φ
  have he (k : ℕ) :
      (∫ x, K x * coordinateStableGenerator α φ x) -
        (∫ x, K x * coordinateStableGenerator α (h k) x) =
      (∫ x, φ x ∂μ) - ∫ x, h k x ∂μ := by
    have hc := quadraticContactCutoff_contDiff (ε := sourceInverseRadius k) hφ
    have hcs := quadraticContactCutoff_hasCompactSupport (sourceInverseRadius_pos k) φ
    have hi := haway (fun x ↦ φ x - h k x) (hφ.sub hc) (hs.sub hcs)
      (quadraticContactCutoff_complement_away_origin (sourceInverseRadius_pos k) φ)
    have hleft : (∫ x, K x * coordinateStableGenerator α (fun x ↦ φ x - h k x) x) =
        (∫ x, K x * coordinateStableGenerator α φ x) -
          ∫ x, K x * coordinateStableGenerator α (h k) x := by
      calc
        _ = ∫ x, K x * coordinateStableGenerator α φ x -
            K x * coordinateStableGenerator α (h k) x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [coordinateStableGenerator_sub hα0 hα2 hφ hs hc hcs]
          ring
        _ = _ := integral_sub
          (integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hφ hs)
          (integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hc hcs)
    rw [hleft, integral_sub hiφ
      (integrable_quadraticContactCutoff μ hiφ (sourceInverseRadius k))] at hi
    exact hi
  have hsmall : Tendsto sourceInverseRadius atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_sourceInverseRadius,
      Eventually.of_forall sourceInverseRadius_pos⟩
  have hKlim := (tendsto_integral_kernel_quadraticContactCutoff_generator_zero
    hα0 hα2 hK hφ hs hφ0 hφ'0).comp hsmall
  have hμlim := tendsto_integral_quadraticContactCutoff_zero μ hiφ hφ.continuous hφ0
  have hl : Tendsto (fun k ↦ (∫ x, K x * coordinateStableGenerator α φ x) -
      ∫ x, K x * coordinateStableGenerator α (h k) x) atTop
      (𝓝 (∫ x, K x * coordinateStableGenerator α φ x)) := by
    simpa only [sub_zero, Function.comp_def, h] using tendsto_const_nhds.sub hKlim
  have hr : Tendsto (fun k ↦ (∫ x, φ x ∂μ) - ∫ x, h k x ∂μ) atTop
      (𝓝 (∫ x, φ x ∂μ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hμlim
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun k ↦ (he k).symm))

end PartialBalayage.Maximal.Square
