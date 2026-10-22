/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorScaling
public import PartialBalayage.Maximal.BoundedSourceTransfer

/-!
# Actual smooth compact cutoffs for the coordinate-stable generator

The derivative bounds required by the singular-integral estimates follow from
genuine compact C² test functions. In particular they hold for the fixed smooth
ball cutoff used in whole-space exhaustion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The derivative of the actual coordinate-line restriction. -/
theorem coordinateLine_hasDerivAt (φ : E → ℝ) (hφ : Differentiable ℝ φ)
    (x : E) (i : Fin 2) (t : ℝ) :
    HasDerivAt (coordinateLine φ x i)
      (fderiv ℝ φ (x + t • EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) t := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ i)).const_add x
  exact (hφ _).hasFDerivAt.comp_hasDerivAt t hl

/-- A globally Lipschitz full derivative controls every true coordinate-line derivative. -/
theorem lipschitzWith_deriv_coordinateLine (φ : E → ℝ) (hφ : Differentiable ℝ φ)
    {K : ℝ≥0} (hφ' : LipschitzWith K (fderiv ℝ φ)) (x : E) (i : Fin 2) :
    LipschitzWith K (deriv (coordinateLine φ x i)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  rw [(coordinateLine_hasDerivAt φ hφ x i s).deriv,
    (coordinateLine_hasDerivAt φ hφ x i t).deriv]
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.norm_eq_one i
  have he : (x + s • v) - (x + t • v) = (s - t) • v := by module
  change ‖fderiv ℝ φ (x + s • v) v - fderiv ℝ φ (x + t • v) v‖ ≤ _
  rw [← sub_apply]
  calc
    _ ≤ ‖fderiv ℝ φ (x + s • v) - fderiv ℝ φ (x + t • v)‖ := by
      simpa only [hv, mul_one] using
        (fderiv ℝ φ (x + s • v) - fderiv ℝ φ (x + t • v)).le_opNorm v
    _ ≤ (K : ℝ) * ‖(x + s • v) - (x + t • v)‖ := hφ'.norm_sub_le _ _
    _ = (K : ℝ) * ‖s - t‖ := by rw [he, norm_smul, hv, mul_one]

/-- A compact C² function has uniform amplitude and coordinate derivative bounds. -/
theorem compactC2_coordinateLine_bounds (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) :
    ∃ M : ℝ, ∃ K : ℝ≥0, (∀ y, ‖φ y‖ ≤ M) ∧
      (∀ x i, Differentiable ℝ (coordinateLine φ x i)) ∧
      (∀ x i, LipschitzWith K (deriv (coordinateLine φ x i))) := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hφ.continuous
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  obtain ⟨K, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) hd
    one_ne_zero
  refine ⟨M, K, hM, ?_, ?_⟩
  · intro x i t
    exact (coordinateLine_hasDerivAt φ (hφ.differentiable (by norm_num)) x i t).differentiableAt
  · intro x i
    exact lipschitzWith_deriv_coordinateLine φ (hφ.differentiable (by norm_num)) hLip x i

/-- The genuine fixed smooth ball cutoff has a uniform stable-generator dilation bound. -/
theorem sourceCutoff_coordinateStableGenerator_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ x : E,
      ‖coordinateStableGenerator α (fun y ↦ sourceCutoff 2 (r⁻¹ • y)) x‖ ≤ C * r ^ (-α) := by
  obtain ⟨M, K, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds (sourceCutoff 2)
    (sourceCutoff_contDiff 2) (sourceCutoff_hasCompactSupport 2)
  refine ⟨stableNormalization α * 2 * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α), ?_⟩
  intro r hr x
  exact (norm_coordinateStableGenerator_large_cutoff_le hα0 hα2 _ hM hd hLip hr x).trans_eq
    (mul_comm _ _)

/-- At every center the actual large smooth-ball cutoff generator tends to zero. -/
theorem tendsto_sourceCutoff_coordinateStableGenerator_zero {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (x : E) :
    Tendsto (fun r : ℝ ↦ coordinateStableGenerator α
      (fun y ↦ sourceCutoff 2 (r⁻¹ • y)) x) atTop (𝓝 0) := by
  obtain ⟨M, K, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds (sourceCutoff 2)
    (sourceCutoff_contDiff 2) (sourceCutoff_hasCompactSupport 2)
  exact tendsto_coordinateStableGenerator_large_cutoff_zero hα0 hα2 _ hM hd hLip x

end PartialBalayage.Maximal.Square
