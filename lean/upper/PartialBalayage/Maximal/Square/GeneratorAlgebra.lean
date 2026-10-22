/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorMeasurability

/-!
# Genuine algebra of compact coordinate-stable generator tests

The generator subtraction identity uses actual integrability of its singular
half-line integrals. Reflection and scalar multiplication follow directly from
the symmetric second-difference formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem integrableOn_coordinateStableSecondDifference {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) (i : Fin 2) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) • stableSecondDifference (coordinateLine φ x i) t)
      (Ioi 0) := by
  obtain ⟨M, K, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds φ hφ hs
  exact integrable_stable_secondDifference hα0 hα2 (by norm_num : (0 : ℝ) < 1)
    (hd x i) (hLip x i) (fun t ↦ hM _)

theorem coordinateStableGenerator_sub {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {φ ψ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ)
    (hψ : ContDiff ℝ 2 ψ) (hψs : HasCompactSupport ψ) (x : E) :
    coordinateStableGenerator α (fun y ↦ φ y - ψ y) x =
      coordinateStableGenerator α φ x - coordinateStableGenerator α ψ x := by
  have hi (i : Fin 2) :
      stableGeneratorIntegral α (coordinateLine (fun y ↦ φ y - ψ y) x i) =
        stableGeneratorIntegral α (coordinateLine φ x i) -
          stableGeneratorIntegral α (coordinateLine ψ x i) := by
    unfold stableGeneratorIntegral
    calc
      _ = ∫ t in Ioi 0,
          (t ^ (-1 - α) • stableSecondDifference (coordinateLine φ x i) t) -
          (t ^ (-1 - α) • stableSecondDifference (coordinateLine ψ x i) t) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [stableSecondDifference, coordinateLine, smul_eq_mul]
        ring
      _ = _ := integral_sub
        (integrableOn_coordinateStableSecondDifference hα0 hα2 hφ hφs x i)
        (integrableOn_coordinateStableSecondDifference hα0 hα2 hψ hψs x i)
  unfold coordinateStableGenerator
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  ring

theorem coordinateStableGenerator_const_mul (α c : ℝ) (φ : E → ℝ) (x : E) :
    coordinateStableGenerator α (fun y ↦ c * φ y) x =
      c * coordinateStableGenerator α φ x := by
  have hi (i : Fin 2) :
      stableGeneratorIntegral α (coordinateLine (fun y ↦ c * φ y) x i) =
        c * stableGeneratorIntegral α (coordinateLine φ x i) := by
    unfold stableGeneratorIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [stableSecondDifference, coordinateLine, smul_eq_mul]
    ring
  unfold coordinateStableGenerator
  simp_rw [hi]
  rw [← Finset.mul_sum]
  ring

theorem coordinateStableGenerator_reflect (α : ℝ) (φ : E → ℝ) (x : E) :
    coordinateStableGenerator α (fun y ↦ φ (-y)) x =
      coordinateStableGenerator α φ (-x) := by
  unfold coordinateStableGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold stableGeneratorIntegral
  apply integral_congr_ae
  filter_upwards with t
  have hp : -(x + t • EuclideanSpace.basisFun (Fin 2) ℝ i) =
      -x + (-t) • EuclideanSpace.basisFun (Fin 2) ℝ i := by module
  have hn : -(x + (-t) • EuclideanSpace.basisFun (Fin 2) ℝ i) =
      -x + t • EuclideanSpace.basisFun (Fin 2) ℝ i := by module
  simp only [stableSecondDifference, coordinateLine, hp, hn, zero_smul, add_zero]
  congr 1
  ring

end PartialBalayage.Maximal.Square
