/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupDefinitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Normalization of the heat kernel

The ordinary heat kernel defined for the table has total mass one in every dimension.
Mathlib's Gaussian integral supplies its exact mass and consequently its integrability.
-/

@[expose] public section

open MeasureTheory

namespace PartialBalayage

theorem integral_heatKernel (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), heatKernel n t x) = 1 := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have heq : (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.exp (-‖x‖ ^ 2 / (4 * t))) =
      fun x ↦ Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    funext x
    congr 1
    ring
  have hπ : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
    simp only [one_div, div_inv_eq_mul]
    ring
  unfold heatKernel
  rw [integral_const_mul, heq, GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hπ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg hbase.le]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hbase _).ne'

theorem integrable_heatKernel (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel n t) :=
  integrable_of_integral_eq_one (integral_heatKernel n ht)

end PartialBalayage
