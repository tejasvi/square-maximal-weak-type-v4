/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.DiamondSourceQuadratic
public import PartialBalayage.Maximal.Square.KernelSourceRepresentation

/-!
# Genuine punctured source identity for the truncated diamond

Compact tests away from the origin satisfy the actual spatial quadratic bound. Full
source-side Fubini therefore identifies the original generator with its positive density,
and the density pairing is genuinely absolutely integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem compact_support_away_zero_norm_bounds {φ : E → ℝ}
    (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧
      ∀ x, φ x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ L := by
  have hn : (tsupport φ)ᶜ ∈ 𝓝 (0 : E) :=
    (isClosed_tsupport φ).isOpen_compl.mem_nhds hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨L, hL, hbound⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : E)
  refine ⟨δ, L, hδ, hL.le, ?_⟩
  intro x hx
  have hxs : x ∈ tsupport φ := subset_tsupport φ hx
  have hnorm : δ ≤ ‖x‖ := by
    by_contra hn
    exact hball (mem_ball_zero_iff.mpr (lt_of_not_ge hn)) hxs
  exact ⟨hnorm, mem_closedBall_zero_iff.mp (hbound hxs)⟩

/-- Genuine compact C² tests away from zero have integrable original source-side jump products. -/
theorem integrable_compact_test_mul_diamondSecondDifference {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ)
    (i : Fin 2) : Integrable (fun p : E × ℝ ↦ φ p.1 *
      stableSecondDifference
        (coordinateLine (diamondTruncatedPower (47 / 40) supportRadius) p.1 i) p.2)
          (spatialJumpMeasure (47 / 40)) := by
  obtain ⟨δ, L, hδ, hL, hb⟩ := compact_support_away_zero_norm_bounds hs hzero
  obtain ⟨M, _, hM, _, _⟩ := compactC2_coordinateLine_bounds φ hφ hs
  obtain ⟨ρ, C, hρ, hnear⟩ := exists_diamond_test_secondDifference_quadratic_bound
    hδ hL (by exact (norm_nonneg (φ 0)).trans (hM 0)) hφ.continuous hM hb i
  exact integrable_source_product_of_spatial_secondDifference_bound
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num) hρ integrable_diamondTruncatedPower
    (measurable_diamondTruncatedPower _ _) hφ.continuous
    ((norm_nonneg (φ 0)).trans (hM 0)) hM i hnear

/-- The actual punctured generator density pairs absolutely integrably with compact C² tests. -/
theorem integrable_compact_test_mul_diamondGenerator {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    Integrable (fun x : E ↦ φ x * coordinateStableGenerator (47 / 40)
      (diamondTruncatedPower (47 / 40) supportRadius) x) :=
  integrable_mul_coordinateStableGenerator_of_products (by norm_num) (by norm_num)
    (integrable_compact_test_mul_diamondSecondDifference hφ hs hzero)

/-- The original two-coordinate operator has the genuine punctured diamond source identity. -/
theorem integral_diamondTruncatedPower_coordinateStableGenerator {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    (∫ x : E, diamondTruncatedPower (47 / 40) supportRadius x *
      coordinateStableGenerator (47 / 40) φ x) =
      ∫ x : E, φ x * coordinateStableGenerator (47 / 40)
        (diamondTruncatedPower (47 / 40) supportRadius) x :=
  integral_coordinateStableGenerator_source_representation (by norm_num) (by norm_num)
    integrable_diamondTruncatedPower hφ hs
    (integrable_compact_test_mul_diamondSecondDifference hφ hs hzero)

end PartialBalayage.Maximal.Square
