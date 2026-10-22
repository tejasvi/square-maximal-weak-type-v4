/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelGeneratorAlmostEverywhere

/-!
# Actual symmetries of the original full kernel generator

The true symmetric coordinate integral preserves reflection of a scalar profile.
The original kernel's sign and interchange symmetries therefore apply to its generator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual normalized coordinate generator, written with its two original scalar profiles. -/
def kernelGeneratorAt (α u v : ℝ) : ℝ := stableNormalization α *
  (stableGeneratorIntegral α (fun t ↦ kernel (u + t) v) +
    stableGeneratorIntegral α (fun t ↦ kernel u (v + t)))

theorem coordinateStableGenerator_euclideanKernel_eq_at (α : ℝ) (x : E) :
    coordinateStableGenerator α euclideanKernel x = kernelGeneratorAt α (x 0) (x 1) := by
  have h₀ : coordinateLine euclideanKernel x 0 = fun t ↦ kernel (x 0 + t) (x 1) := by
    funext t
    simp [coordinateLine, euclideanKernel, EuclideanSpace.basisFun_apply]
  have h₁ : coordinateLine euclideanKernel x 1 = fun t ↦ kernel (x 0) (x 1 + t) := by
    funext t
    simp [coordinateLine, euclideanKernel, EuclideanSpace.basisFun_apply]
  simp only [coordinateStableGenerator, Fin.sum_univ_two, h₀, h₁, kernelGeneratorAt]

private theorem stableGeneratorIntegral_reflect_scalar (α : ℝ) (f : ℝ → ℝ) :
    stableGeneratorIntegral α (fun t ↦ f (-t)) = stableGeneratorIntegral α f := by
  unfold stableGeneratorIntegral
  apply integral_congr_ae
  filter_upwards with t
  simp only [stableSecondDifference, neg_zero, neg_neg, smul_eq_mul]
  ring

theorem kernelGeneratorAt_neg_left (α u v : ℝ) :
    kernelGeneratorAt α (-u) v = kernelGeneratorAt α u v := by
  have he : (fun t : ℝ ↦ kernel (-u + t) v) = fun t ↦ kernel (u + -t) v := by
    funext t
    rw [show -u + t = -(u + -t) by ring, kernel_neg_left]
  simp only [kernelGeneratorAt, he, kernel_neg_left]
  rw [stableGeneratorIntegral_reflect_scalar α (fun t ↦ kernel (u + t) v)]

theorem kernelGeneratorAt_neg_right (α u v : ℝ) :
    kernelGeneratorAt α u (-v) = kernelGeneratorAt α u v := by
  have he : (fun t : ℝ ↦ kernel u (-v + t)) = fun t ↦ kernel u (v + -t) := by
    funext t
    rw [show -v + t = -(v + -t) by ring, kernel_neg_right]
  simp only [kernelGeneratorAt, he, kernel_neg_right]
  rw [stableGeneratorIntegral_reflect_scalar α (fun t ↦ kernel u (v + t))]

theorem kernelGeneratorAt_swap (α u v : ℝ) :
    kernelGeneratorAt α v u = kernelGeneratorAt α u v := by
  have he₀ : (fun t : ℝ ↦ kernel (v + t) u) = fun t ↦ kernel u (v + t) := by
    funext t
    exact kernel_swap _ _
  have he₁ : (fun t : ℝ ↦ kernel v (u + t)) = fun t ↦ kernel (u + t) v := by
    funext t
    exact kernel_swap _ _
  rw [kernelGeneratorAt, he₀, he₁, add_comm]
  rfl

/-- The actual generator retains the full coordinate sign symmetry at every point. -/
theorem kernelGeneratorAt_abs (α u v : ℝ) :
    kernelGeneratorAt α |u| |v| = kernelGeneratorAt α u v := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hu, abs_of_nonneg hv]
  · rw [abs_of_nonneg hu, abs_of_nonpos hv, kernelGeneratorAt_neg_right]
  · rw [abs_of_nonpos hu, abs_of_nonneg hv, kernelGeneratorAt_neg_left]
  · rw [abs_of_nonpos hu, abs_of_nonpos hv,
      kernelGeneratorAt_neg_left, kernelGeneratorAt_neg_right]

end PartialBalayage.Maximal.Square
