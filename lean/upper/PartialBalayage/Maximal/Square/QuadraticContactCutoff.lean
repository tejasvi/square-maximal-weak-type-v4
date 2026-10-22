/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorMeasurability
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Genuine shrinking quadratic contact cutoffs

A compact C² test with zero value and derivative at the origin is quadratically
small. Its actual shrinking cutoff has uniformly bounded second derivative;
the stable generator therefore vanishes at order `2 - α`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open PartialBalayage.Linear
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem norm_fderiv_le_linear_of_lipschitz {φ : E → ℝ} {K : ℝ≥0}
    (hφ' : LipschitzWith K (fderiv ℝ φ)) (hφ'0 : fderiv ℝ φ 0 = 0) (x : E) :
    ‖fderiv ℝ φ x‖ ≤ (K : ℝ) * ‖x‖ := by
  simpa only [hφ'0, sub_zero] using hφ'.norm_sub_le x 0

/-- A genuine zero first jet and a Lipschitz derivative give quadratic contact. -/
theorem norm_le_quadratic_of_lipschitz_fderiv {φ : E → ℝ} {K : ℝ≥0}
    (hφ : Differentiable ℝ φ) (hφ' : LipschitzWith K (fderiv ℝ φ))
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) (x : E) :
    ‖φ x‖ ≤ (K : ℝ) * ‖x‖ ^ 2 := by
  have hbound : ∀ y ∈ closedBall (0 : E) ‖x‖,
      ‖fderiv ℝ φ y‖ ≤ (K : ℝ) * ‖x‖ := by
    intro y hy
    exact (norm_fderiv_le_linear_of_lipschitz hφ' hφ'0 y).trans
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hy)
        K.coe_nonneg)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ ↦ hφ y) hbound
    (convex_closedBall (0 : E) ‖x‖)
    (show (0 : E) ∈ closedBall 0 ‖x‖ by simp)
    (show x ∈ closedBall 0 ‖x‖ by simp)
  simpa only [hφ0, sub_zero, pow_two, mul_assoc] using h

theorem tsupport_sourceCutoff_subset_closedBall :
    tsupport (sourceCutoff 2) ⊆ closedBall (0 : E) 2 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hball
  have hxnorm : 2 ≤ ‖x‖ := by
    exact le_of_lt
      (show 2 < ‖x‖ by simpa only [mem_closedBall, dist_zero_right, not_le] using hball)
  exact hx (CenteredMaximal.Ball.smoothBallCutoff_zero 2 0 x
    (by norm_num) (by norm_num) (by simpa only [sub_zero, one_add_one_eq_two] using hxnorm))

theorem tsupport_scaled_sourceCutoff_subset_closedBall {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun x : E ↦ sourceCutoff 2 (ε⁻¹ • x)) ⊆ closedBall (0 : E) (2 * ε) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hxs : ε⁻¹ • x ∈ tsupport (sourceCutoff 2) := subset_tsupport _ hx
  have hb := tsupport_sourceCutoff_subset_closedBall hxs
  have he : ‖ε⁻¹ • x‖ = ε⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  simp only [mem_closedBall, dist_zero_right, he] at hb ⊢
  calc
    ‖x‖ = ε * (ε⁻¹ * ‖x‖) := by rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    _ ≤ ε * 2 := mul_le_mul_of_nonneg_left hb hε.le
    _ = 2 * ε := mul_comm _ _

/-- The actual removed origin piece of a compact quadratic-contact test. -/
def quadraticContactCutoff (ε : ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  sourceCutoff 2 (ε⁻¹ • x) * φ x

theorem quadraticContactCutoff_contDiff {ε : ℝ} {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (quadraticContactCutoff ε φ) :=
  ((sourceCutoff_contDiff 2).comp (contDiff_const_smul ε⁻¹)).mul hφ

theorem quadraticContactCutoff_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (φ : E → ℝ) :
    HasCompactSupport (quadraticContactCutoff ε φ) :=
  (sourceCutoffScale_hasCompactSupport 2 (inv_pos.mpr hε)).mul_right

/-- The genuine cutoff amplitude has the required quadratic radius factor. -/
theorem norm_quadraticContactCutoff_le {φ : E → ℝ} {K : ℝ≥0}
    (hφ : Differentiable ℝ φ) (hφ' : LipschitzWith K (fderiv ℝ φ))
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖quadraticContactCutoff ε φ x‖ ≤ 4 * (K : ℝ) * ε ^ 2 := by
  by_cases hx : x ∈ tsupport (fun x : E ↦ sourceCutoff 2 (ε⁻¹ • x))
  · have hb : ‖x‖ ≤ 2 * ε := by
      simpa only [mem_closedBall, dist_zero_right] using
        tsupport_scaled_sourceCutoff_subset_closedBall hε hx
    have hχ : ‖sourceCutoff 2 (ε⁻¹ • x)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sourceCutoff_nonneg 2 _)]
      exact sourceCutoff_le_one 2 _
    rw [quadraticContactCutoff, norm_mul]
    calc
      _ ≤ ‖φ x‖ := by simpa using mul_le_mul_of_nonneg_right hχ (norm_nonneg (φ x))
      _ ≤ (K : ℝ) * ‖x‖ ^ 2 := norm_le_quadratic_of_lipschitz_fderiv hφ hφ' hφ0 hφ'0 x
      _ ≤ 4 * (K : ℝ) * ε ^ 2 := by
        have hs : ‖x‖ ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        nlinarith [mul_le_mul_of_nonneg_left hs K.coe_nonneg]
  · have hz : sourceCutoff 2 (ε⁻¹ • x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : E ↦ sourceCutoff 2 (ε⁻¹ • x)) hx
    simp only [quadraticContactCutoff, hz, zero_mul, norm_zero]
    positivity

theorem norm_iteratedFDeriv_two_le_of_lipschitz {φ : E → ℝ} {K : ℝ≥0}
    (hφ' : LipschitzWith K (fderiv ℝ φ)) (x : E) :
    ‖iteratedFDeriv ℝ 2 φ x‖ ≤ (K : ℝ) := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  exact norm_fderiv_le_of_lipschitz ℝ hφ'

/-- The actual cutoff second derivative is bounded independently of its shrinking radius. -/
theorem norm_iteratedFDeriv_two_quadraticContactCutoff_le
    {φ : E → ℝ} {K A B : ℝ≥0} (hφ : ContDiff ℝ 2 φ)
    (hφ' : LipschitzWith K (fderiv ℝ φ))
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0)
    (hA : ∀ x : E, ‖fderiv ℝ (sourceCutoff 2) x‖ ≤ (A : ℝ))
    (hB : ∀ x : E, ‖iteratedFDeriv ℝ 2 (sourceCutoff 2) x‖ ≤ (B : ℝ))
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖iteratedFDeriv ℝ 2 (quadraticContactCutoff ε φ) x‖ ≤
      (K : ℝ) * (1 + 4 * (A : ℝ) + 4 * (B : ℝ)) := by
  let χ := fun x : E ↦ sourceCutoff 2 (ε⁻¹ • x)
  by_cases hx : x ∈ tsupport χ
  · have hxnorm : ‖x‖ ≤ 2 * ε := by
      simpa only [mem_closedBall, dist_zero_right] using
        tsupport_scaled_sourceCutoff_subset_closedBall hε hx
    have hχ0 : ‖χ x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sourceCutoff_nonneg 2 _)]
      exact sourceCutoff_le_one 2 _
    have hχ1 : ‖iteratedFDeriv ℝ 1 χ x‖ ≤ ε⁻¹ * (A : ℝ) := by
      rw [norm_iteratedFDeriv_one]
      change ‖fderiv ℝ (sourceCutoffScale 2 ε⁻¹) x‖ ≤ _
      rw [sourceCutoffScale_fderiv, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)]
      exact mul_le_mul_of_nonneg_left (hA _) (inv_pos.mpr hε).le
    have hχ2 : ‖iteratedFDeriv ℝ 2 χ x‖ ≤ ε⁻¹ ^ 2 * (B : ℝ) := by
      change ‖iteratedFDeriv ℝ 2 (fun y : E ↦ sourceCutoff 2 (ε⁻¹ • y)) x‖ ≤ _
      rw [iteratedFDeriv_comp_const_smul ε⁻¹ (sourceCutoff_contDiff 2), norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε⁻¹)]
      exact mul_le_mul_of_nonneg_left (hB _) (sq_nonneg ε⁻¹)
    have hφ1 : ‖iteratedFDeriv ℝ 1 φ x‖ ≤ 2 * (K : ℝ) * ε := by
      rw [norm_iteratedFDeriv_one]
      calc
        _ ≤ (K : ℝ) * ‖x‖ := norm_fderiv_le_linear_of_lipschitz hφ' hφ'0 x
        _ ≤ 2 * (K : ℝ) * ε := by nlinarith [mul_le_mul_of_nonneg_left hxnorm K.coe_nonneg]
    have hφ2 := norm_iteratedFDeriv_two_le_of_lipschitz hφ' x
    have hφamp : ‖φ x‖ ≤ 4 * (K : ℝ) * ε ^ 2 := by
      have hq := norm_le_quadratic_of_lipschitz_fderiv
        (hφ.differentiable (by norm_num)) hφ' hφ0 hφ'0 x
      have hs : ‖x‖ ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxnorm 2
      nlinarith [mul_le_mul_of_nonneg_left hs K.coe_nonneg]
    have hprod := norm_iteratedFDeriv_mul_le
      ((sourceCutoff_contDiff 2).comp (contDiff_const_smul ε⁻¹)) hφ x
      (n := 2) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right,
      Nat.reduceSub, Nat.cast_one, Nat.cast_ofNat, one_mul,
      norm_iteratedFDeriv_zero] at hprod
    change ‖iteratedFDeriv ℝ 2 (quadraticContactCutoff ε φ) x‖ ≤
      ‖χ x‖ * ‖iteratedFDeriv ℝ 2 φ x‖ +
        2 * ‖iteratedFDeriv ℝ 1 χ x‖ * ‖iteratedFDeriv ℝ 1 φ x‖ +
        ‖iteratedFDeriv ℝ 2 χ x‖ * ‖φ x‖ at hprod
    have hp0 := mul_le_mul hχ0 hφ2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hp1 := mul_le_mul hχ1 hφ1 (norm_nonneg _) (by positivity : 0 ≤ ε⁻¹ * (A : ℝ))
    have hp2 := mul_le_mul hχ2 hφamp (norm_nonneg _)
      (by positivity : 0 ≤ ε⁻¹ ^ 2 * (B : ℝ))
    have he : (K : ℝ) + 2 * (ε⁻¹ * (A : ℝ) * (2 * (K : ℝ) * ε)) +
        (ε⁻¹ ^ 2 * (B : ℝ) * (4 * (K : ℝ) * ε ^ 2)) =
          (K : ℝ) * (1 + 4 * (A : ℝ) + 4 * (B : ℝ)) := by
      field_simp
      ring
    rw [← he]
    nlinarith
  · have hxH : x ∉ tsupport (quadraticContactCutoff ε φ) :=
      fun hh ↦ hx (tsupport_mul_subset_left hh)
    have hz : iteratedFDeriv ℝ 2 (quadraticContactCutoff ε φ) x = 0 :=
      Function.notMem_support.mp fun hh ↦ hxH (support_iteratedFDeriv_subset 2 hh)
    rw [hz, norm_zero]
    positivity

/-- Actual compact C² contact tests have uniform shrinking-cutoff amplitude
and derivative bounds. -/
theorem exists_quadraticContactCutoff_bounds {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) :
    ∃ C : ℝ≥0, ∀ ε > 0,
      (∀ x, ‖quadraticContactCutoff ε φ x‖ ≤ (C : ℝ) * ε ^ 2) ∧
      LipschitzWith C (fderiv ℝ (quadraticContactCutoff ε φ)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hφ.fderiv_right (by norm_num)) one_ne_zero
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (sourceCutoff_hasCompactSupport 2) (sourceCutoff_contDiff 2) (by norm_num)
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    ((sourceCutoff_hasCompactSupport 2).fderiv ℝ)
    ((sourceCutoff_contDiff 2).fderiv_right (by norm_num)) one_ne_zero
  let C : ℝ≥0 := K * (4 + 4 * A + 4 * B)
  have hCL : (K : ℝ) * (1 + 4 * (A : ℝ) + 4 * (B : ℝ)) ≤ (C : ℝ) := by
    simp only [C, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    nlinarith [K.coe_nonneg]
  refine ⟨C, fun ε hε ↦ ⟨?_, ?_⟩⟩
  · intro x
    apply (norm_quadraticContactCutoff_le (hφ.differentiable (by norm_num)) hK
      hφ0 hφ'0 hε x).trans
    have hc : 4 * (K : ℝ) ≤ (C : ℝ) := by
      simp only [C, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
      nlinarith [K.coe_nonneg, A.coe_nonneg, B.coe_nonneg]
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg ε)
  · apply lipschitzWith_of_nnnorm_fderiv_le
      ((quadraticContactCutoff_contDiff hφ).fderiv_right
        (by norm_num) |>.differentiable one_ne_zero)
    intro x
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact (norm_iteratedFDeriv_two_quadraticContactCutoff_le hφ hK hφ0 hφ'0
      (fun x ↦ norm_fderiv_le_of_lipschitz ℝ hA)
      (norm_iteratedFDeriv_two_le_of_lipschitz hB) hε x).trans hCL

/-- The actual generator of a deleted-origin quadratic piece has vanishing stable order. -/
theorem quadraticContactCutoff_coordinateStableGenerator_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) :
    ∃ C : ℝ, ∀ ε > 0, ∀ x : E,
      ‖coordinateStableGenerator α (quadraticContactCutoff ε φ) x‖ ≤ C * ε ^ (2 - α) := by
  obtain ⟨K, hK⟩ := exists_quadraticContactCutoff_bounds hφ hs hφ0 hφ'0
  refine ⟨stableNormalization α * 2 * (2 * (K : ℝ)) * (1 / (2 - α) + 4 / α), ?_⟩
  intro ε hε x
  have hd := (quadraticContactCutoff_contDiff (ε := ε) hφ).differentiable (by norm_num)
  have hnorm (i : Fin 2) :
      ‖stableGeneratorIntegral α (coordinateLine (quadraticContactCutoff ε φ) x i)‖ ≤
        (2 * (K : ℝ)) * (1 / (2 - α) + 4 / α) * ε ^ (2 - α) := by
    have hline := fun t ↦
      (coordinateLine_hasDerivAt (quadraticContactCutoff ε φ) hd x i t).differentiableAt
    simpa only [stableGeneratorIntegral] using
      norm_integral_stable_secondDifference_small_le hα0 hα2 hε hline
        (lipschitzWith_deriv_coordinateLine _ hd (hK ε hε).2 x i)
        (fun t ↦ (hK ε hε).1 _)
  have hc := (stableNormalization_pos hα0 hα2).le
  unfold coordinateStableGenerator
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, Fin.sum_univ_two]
  calc
    _ ≤ stableNormalization α *
        (‖stableGeneratorIntegral α (coordinateLine (quadraticContactCutoff ε φ) x 0)‖ +
          ‖stableGeneratorIntegral α (coordinateLine (quadraticContactCutoff ε φ) x 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
    _ ≤ _ := by nlinarith [hnorm 0, hnorm 1]

/-- The true deleted-origin error vanishes against any integrable kernel. -/
theorem tendsto_integral_kernel_quadraticContactCutoff_generator_zero
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K φ : E → ℝ}
    (hK : Integrable K volume) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hφ0 : φ 0 = 0) (hφ'0 : fderiv ℝ φ 0 = 0) :
    Tendsto (fun ε ↦ ∫ x, K x * coordinateStableGenerator α
      (quadraticContactCutoff ε φ) x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := quadraticContactCutoff_coordinateStableGenerator_bound
    hα0 hα2 hφ hs hφ0 hφ'0
  apply squeeze_zero_norm'
    (a := fun ε ↦ ((∫ x, ‖K x‖) * C) * ε ^ (2 - α))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := integrable_kernel_mul_coordinateStableGenerator hK
      (quadraticContactCutoff_contDiff hφ).continuous (hC ε hε)
    calc
      _ ≤ ∫ x, ‖K x * coordinateStableGenerator α (quadraticContactCutoff ε φ) x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖K x‖ * (C * ε ^ (2 - α)) := by
        apply integral_mono hi.norm (hK.norm.mul_const _)
        intro x
        change ‖K x * coordinateStableGenerator α (quadraticContactCutoff ε φ) x‖ ≤
          ‖K x‖ * (C * ε ^ (2 - α))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC ε hε x) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring
  · have hp : Tendsto (fun ε : ℝ ↦ ε ^ (2 - α)) (𝓝[>] 0)
        (𝓝 ((0 : ℝ) ^ (2 - α))) :=
      (Real.continuousAt_rpow_const 0 (2 - α)
        (Or.inr (by linarith : 0 ≤ 2 - α))).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow (by linarith : 2 - α ≠ 0), mul_zero] using
      hp.const_mul ((∫ x, ‖K x‖) * C)

end PartialBalayage.Maximal.Square
