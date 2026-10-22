/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.StableGeneratorScaling
public import PartialBalayage.Maximal.Square.JumpEnergy

/-!
# The actual coordinate-stable generator and its cutoff scaling

This is the normalized sum of the two genuine coordinate second-difference
integrals. Dilation homogeneity is proved by change of variables. Uniform
derivative and amplitude bounds give the actual large-cutoff decay.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open PartialBalayage.Linear
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual test function restricted to an oriented coordinate line. -/
def coordinateLine (φ : E → ℝ) (x : E) (i : Fin 2) (t : ℝ) : ℝ :=
  φ (x + t • EuclideanSpace.basisFun (Fin 2) ℝ i)

/-- The original normalized anisotropic stable generator on physical-space tests. -/
def coordinateStableGenerator (α : ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  stableNormalization α * ∑ i : Fin 2, stableGeneratorIntegral α (coordinateLine φ x i)

private theorem coordinateLine_dilate (φ : E → ℝ) (x : E) (i : Fin 2) (r t : ℝ) :
    coordinateLine (fun y ↦ φ (r⁻¹ • y)) x i t =
      coordinateLine φ (r⁻¹ • x) i (t / r) := by
  simp only [coordinateLine, smul_add, smul_smul, div_eq_inv_mul]

/-- The actual coordinate-stable generator has its exact inverse-power homogeneity. -/
theorem coordinateStableGenerator_dilate (α : ℝ) (φ : E → ℝ) (x : E)
    {r : ℝ} (hr : 0 < r) :
    coordinateStableGenerator α (fun y ↦ φ (r⁻¹ • y)) x =
      r ^ (-α) * coordinateStableGenerator α φ (r⁻¹ • x) := by
  unfold coordinateStableGenerator
  have he : ∀ i : Fin 2,
      coordinateLine (fun y ↦ φ (r⁻¹ • y)) x i =
        fun t ↦ coordinateLine φ (r⁻¹ • x) i (t / r) := by
    intro i
    funext t
    exact coordinateLine_dilate φ x i r t
  simp_rw [he, stableGeneratorIntegral_dilate α _ hr, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Bounded actual coordinate lines control the entire physical-space stable generator. -/
theorem norm_coordinateStableGenerator_le {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {M : ℝ} {K : ℝ≥0} (φ : E → ℝ) (hM : ∀ y, ‖φ y‖ ≤ M)
    (hφ : ∀ x i, Differentiable ℝ (coordinateLine φ x i))
    (hφ' : ∀ x i, LipschitzWith K (deriv (coordinateLine φ x i))) (x : E) :
    ‖coordinateStableGenerator α φ x‖ ≤
      stableNormalization α * 2 * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α) := by
  have hc := (stableNormalization_pos hα0 hα2).le
  have hi : ∀ i : Fin 2, ‖stableGeneratorIntegral α (coordinateLine φ x i)‖ ≤
      (2 * (K : ℝ)) / (2 - α) + 4 * M / α := by
    intro i
    have hb := norm_integral_stable_secondDifference_le hα0 hα2 (by norm_num : (0 : ℝ) < 1)
      (hφ x i) (hφ' x i) (fun t ↦ hM _)
    simpa only [stableGeneratorIntegral, Real.one_rpow, mul_one] using hb
  unfold coordinateStableGenerator
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, Fin.sum_univ_two]
  calc
    _ ≤ stableNormalization α *
        (‖stableGeneratorIntegral α (coordinateLine φ x 0)‖ +
          ‖stableGeneratorIntegral α (coordinateLine φ x 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
    _ ≤ _ := by nlinarith [hi 0, hi 1]

/-- The genuine spatial large-cutoff generator is uniformly of order `r^(−α)`. -/
theorem norm_coordinateStableGenerator_large_cutoff_le {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {M : ℝ} {K : ℝ≥0}
    (φ : E → ℝ) (hM : ∀ y, ‖φ y‖ ≤ M)
    (hφ : ∀ x i, Differentiable ℝ (coordinateLine φ x i))
    (hφ' : ∀ x i, LipschitzWith K (deriv (coordinateLine φ x i)))
    {r : ℝ} (hr : 0 < r) (x : E) :
    ‖coordinateStableGenerator α (fun y ↦ φ (r⁻¹ • y)) x‖ ≤
      r ^ (-α) * (stableNormalization α * 2 *
        ((2 * (K : ℝ)) / (2 - α) + 4 * M / α)) := by
  rw [coordinateStableGenerator_dilate α φ x hr, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  exact mul_le_mul_of_nonneg_left (norm_coordinateStableGenerator_le hα0 hα2 φ hM hφ hφ' _)
    (Real.rpow_nonneg hr.le _)

/-- The same uniform bound makes the actual large-cutoff generator vanish at every center. -/
theorem tendsto_coordinateStableGenerator_large_cutoff_zero {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {M : ℝ} {K : ℝ≥0}
    (φ : E → ℝ) (hM : ∀ y, ‖φ y‖ ≤ M)
    (hφ : ∀ x i, Differentiable ℝ (coordinateLine φ x i))
    (hφ' : ∀ x i, LipschitzWith K (deriv (coordinateLine φ x i))) (x : E) :
    Tendsto (fun r : ℝ ↦ coordinateStableGenerator α (fun y ↦ φ (r⁻¹ • y)) x)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun r : ℝ ↦ r ^ (-α) *
    (stableNormalization α * 2 * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact norm_coordinateStableGenerator_large_cutoff_le hα0 hα2 φ hM hφ hφ' hr x
  · simpa only [zero_mul] using (tendsto_rpow_neg_atTop hα0).mul_const
      (stableNormalization α * 2 * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α))

end PartialBalayage.Maximal.Square
