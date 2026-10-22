/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourcePairing

/-!
# Genuine convolution commutation for the infinite source generator

The actual compact kernel's quadratic cancellation makes the full source and
ordinary L¹ value integrations jointly integrable. Fubini therefore passes the
compensated generator through genuine convolution.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Filter
open scoped Convolution ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual full infinite-source generator commutes with compact smooth convolution. -/
theorem compensatedSourceGenerator_convolution_compactC2
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {u φ : E → ℝ} (hu : Integrable u volume)
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    compensatedSourceGenerator μ (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ((compensatedSourceGenerator μ φ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  obtain ⟨C, _, hb⟩ := exists_compactC2_symmetricSecondDifference_bound hφ hs
  let ψ (y : E) := φ (x - y)
  have hψ : Continuous ψ := by fun_prop
  have hbψ (y z : E) : ‖ψ (y + z) + ψ (y - z) - 2 * ψ y‖ ≤
      C * compensatedJumpMoment z := by
    have he₁ : x - (y + z) = (x - y) - z := by abel
    have he₂ : x - (y - z) = (x - y) + z := by abel
    dsimp [ψ]
    rw [he₁, he₂, add_comm (φ ((x - y) - z)) (φ ((x - y) + z))]
    exact hb (x - y) z
  have hi0 := integrable_value_mul_sourceSecondDifference μ hm hψ hu hbψ
  have hi : Integrable (fun p : E × E ↦ u p.1 *
      (φ (x + p.2 - p.1) + φ (x - p.2 - p.1) - 2 * φ (x - p.1)))
        (volume.prod μ) := by
    apply hi0.congr
    filter_upwards with p
    dsimp [ψ]
    rw [show x - (p.1 + p.2) = x - p.2 - p.1 by abel,
      show x - (p.1 - p.2) = x + p.2 - p.1 by abel]
    ring
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  have hprod (a : E) : Integrable (fun y ↦ u y * φ (a - y)) volume :=
    hu.mul_bdd (by fun_prop : Continuous (fun y : E ↦ φ (a - y))).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ hM (a - y))
  have hc (a : E) : (φ ⋆[lsmul ℝ ℝ, volume] u) a = ∫ y, u y * φ (a - y) := by
    rw [convolution_lsmul_swap]
    simp only [smul_eq_mul, mul_comm]
  have hδ (z : E) : (φ ⋆[lsmul ℝ ℝ, volume] u) (x + z) +
      (φ ⋆[lsmul ℝ ℝ, volume] u) (x - z) -
        2 * (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ∫ y, u y * (φ (x + z - y) + φ (x - z - y) - 2 * φ (x - y)) := by
    rw [hc, hc, hc]
    have he₁ := integral_add (hprod (x + z)) (hprod (x - z))
    have he₂ := integral_sub ((hprod (x + z)).add (hprod (x - z)))
      ((hprod x).const_mul 2)
    simp only [Pi.add_apply] at he₁ he₂
    rw [← integral_const_mul, ← he₁, ← he₂]
    apply integral_congr_ae
    filter_upwards with y
    ring
  unfold compensatedSourceGenerator
  simp only [hδ]
  rw [← integral_integral_swap hi, ← integral_const_mul]
  rw [convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_const_mul]
  have he₁ (z : E) : x + z - y = (x - y) + z := by abel
  have he₂ (z : E) : x - z - y = (x - y) - z := by abel
  simp only [he₁, he₂, smul_eq_mul]
  ring

end PartialBalayage.Maximal.Square
