/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.StableSecondDifference
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Homogeneity of the actual stable second-difference integral

The change of variables is made in the genuine half-line integral. It yields
the inverse-power decay of large cutoffs and the small-cutoff vanishing order,
without assuming a generator scaling or a cutoff certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual symmetric stable singular integral at the origin. -/
def stableGeneratorIntegral (α : ℝ) (φ : ℝ → F) : F :=
  ∫ t in Ioi 0, t ^ (-1 - α) • stableSecondDifference φ t

/-- True dilation homogeneity of the actual stable singular integral. -/
theorem stableGeneratorIntegral_dilate (α : ℝ) (φ : ℝ → F) {r : ℝ} (hr : 0 < r) :
    stableGeneratorIntegral α (fun t ↦ φ (t / r)) =
      r ^ (-α) • stableGeneratorIntegral α φ := by
  have hd : ∀ t : ℝ,
      stableSecondDifference (fun t ↦ φ (t / r)) (r * t) = stableSecondDifference φ t := by
    intro t
    simp only [stableSecondDifference, mul_div_cancel_left₀ _ hr.ne', zero_div, neg_div]
  unfold stableGeneratorIntegral
  calc
    _ = r • ∫ t in Ioi 0, (r * t) ^ (-1 - α) • stableSecondDifference φ t := by
      simpa only [mul_zero, hd] using
        (integral_comp_mul_left_Ioi'
          (fun t ↦ t ^ (-1 - α) • stableSecondDifference (fun t ↦ φ (t / r)) t) 0 hr).symm
    _ = r • (r ^ (-1 - α) • ∫ t in Ioi 0,
        t ^ (-1 - α) • stableSecondDifference φ t) := by
      congr 1
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.mul_rpow hr.le ht.le, smul_smul]
    _ = _ := by
      rw [smul_smul]
      congr 1
      calc
        r * r ^ (-1 - α) = r ^ (1 : ℝ) * r ^ (-1 - α) := by rw [Real.rpow_one]
        _ = r ^ (1 + (-1 - α)) := (Real.rpow_add hr _ _).symm
        _ = r ^ (-α) := by congr 1; ring

/-- A quadratic-amplitude dilation has the true order `r^(2-α)` stable integral. -/
theorem stableGeneratorIntegral_small_dilate (α : ℝ) (φ : ℝ → F) {r : ℝ} (hr : 0 < r) :
    stableGeneratorIntegral α (fun t ↦ r ^ (2 : ℕ) • φ (t / r)) =
      r ^ (2 - α) • stableGeneratorIntegral α φ := by
  have hd : ∀ t : ℝ, stableSecondDifference (fun t ↦ r ^ (2 : ℕ) • φ (t / r)) t =
      r ^ (2 : ℕ) • stableSecondDifference (fun t ↦ φ (t / r)) t := by
    intro t
    simp only [stableSecondDifference, smul_add, smul_sub]
    rw [smul_comm (r ^ (2 : ℕ)) (2 : ℝ)]
  unfold stableGeneratorIntegral
  have hw : (fun t ↦ t ^ (-1 - α) •
      stableSecondDifference (fun t ↦ r ^ (2 : ℕ) • φ (t / r)) t) =
      fun t ↦ r ^ (2 : ℕ) • (t ^ (-1 - α) •
        stableSecondDifference (fun t ↦ φ (t / r)) t) := by
    funext t
    rw [hd, smul_comm]
  rw [hw, integral_smul]
  change r ^ (2 : ℕ) • stableGeneratorIntegral α (fun t ↦ φ (t / r)) = _
  rw [stableGeneratorIntegral_dilate α φ hr, smul_smul,
    ← Real.rpow_natCast r 2, ← Real.rpow_add hr]
  congr 1

/-- Actual large stable cutoffs tend to zero for every strictly positive generator order. -/
theorem tendsto_stableGeneratorIntegral_large_dilate_zero {α : ℝ} (hα : 0 < α)
    (φ : ℝ → F) :
    Tendsto (fun r ↦ stableGeneratorIntegral α (fun t ↦ φ (t / r))) atTop (𝓝 0) := by
  have he : (fun r ↦ stableGeneratorIntegral α (fun t ↦ φ (t / r))) =ᶠ[atTop]
      fun r ↦ r ^ (-α) • stableGeneratorIntegral α φ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact stableGeneratorIntegral_dilate α φ hr
  apply Tendsto.congr' he.symm
  simpa only [zero_smul] using (tendsto_rpow_neg_atTop hα).smul_const
    (stableGeneratorIntegral α φ)

/-- Actual quadratic-amplitude small cutoffs vanish below generator order two. -/
theorem tendsto_stableGeneratorIntegral_small_dilate_zero {α : ℝ} (hα : α < 2)
    (φ : ℝ → F) :
    Tendsto (fun r ↦ stableGeneratorIntegral α (fun t ↦ r ^ (2 : ℕ) • φ (t / r)))
      (𝓝[>] 0) (𝓝 0) := by
  have he : (fun r ↦ stableGeneratorIntegral α (fun t ↦ r ^ (2 : ℕ) • φ (t / r)))
      =ᶠ[𝓝[>] 0] fun r ↦ r ^ (2 - α) • stableGeneratorIntegral α φ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact stableGeneratorIntegral_small_dilate α φ hr
  have hp : Tendsto (fun r : ℝ ↦ r ^ (2 - α)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (2 - α))) :=
    (Real.continuousAt_rpow_const 0 (2 - α) (Or.inr (by linarith))).tendsto.mono_left
      nhdsWithin_le_nhds
  apply Tendsto.congr' he.symm
  simpa only [Real.zero_rpow (by linarith : 2 - α ≠ 0), zero_smul] using
    hp.smul_const (stableGeneratorIntegral α φ)

end PartialBalayage.Linear
