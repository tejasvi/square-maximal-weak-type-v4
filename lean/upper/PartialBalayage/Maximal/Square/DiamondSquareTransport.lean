/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Kernel
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The actual diamond-to-square transformation and radial integration

The article's map sends `(u,v)` to `(u+v,u-v)`. Its determinant has absolute
value two. Its sup norm is exactly the diamond radius, giving an exact
one-dimensional radial integration formula in the original Lebesgue measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped Matrix

namespace PartialBalayage.Maximal.Square

local notation "P" => Fin 2 → ℝ

/-- The actual matrix of the article's change of coordinates. -/
def diamondSquareMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- The actual diamond-to-square linear map. -/
def diamondSquareMap : P →ₗ[ℝ] P := Matrix.toLin' diamondSquareMatrix

theorem diamondSquareMap_zero (x : P) : diamondSquareMap x 0 = x 0 + x 1 := by
  simp [diamondSquareMap, diamondSquareMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

theorem diamondSquareMap_one (x : P) : diamondSquareMap x 1 = x 0 - x 1 := by
  simp [diamondSquareMap, diamondSquareMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- The exact determinant, with its orientation reversal. -/
theorem det_diamondSquareMap : LinearMap.det diamondSquareMap = -2 := by
  rw [diamondSquareMap, LinearMap.det_toLin']
  norm_num [diamondSquareMatrix, Matrix.det_fin_two]

/-- The invertible continuous transformation is constructed from the actual matrix. -/
def diamondSquareEquiv : P ≃L[ℝ] P :=
  LinearEquiv.toContinuousLinearEquiv
    (diamondSquareMap.equivOfDetNeZero (by rw [det_diamondSquareMap]; norm_num))

theorem diamondSquareEquiv_apply (x : P) : diamondSquareEquiv x = diamondSquareMap x := rfl

/-- The exact equality of the transformed sup norm and the original diamond radius. -/
theorem norm_diamondSquareMap (x : P) :
    ‖diamondSquareMap x‖ = diamondRadius (x 0) (x 1) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro i
    fin_cases i
    · change ‖diamondSquareMap x 0‖ ≤ _
      rw [diamondSquareMap_zero, Real.norm_eq_abs]
      exact abs_add_le (x 0) (x 1)
    · change ‖diamondSquareMap x 1‖ ≤ _
      rw [diamondSquareMap_one, Real.norm_eq_abs]
      exact abs_sub (x 0) (x 1)
  · have h₀ := norm_le_pi_norm (diamondSquareMap x) 0
    have h₁ := norm_le_pi_norm (diamondSquareMap x) 1
    rw [diamondSquareMap_zero, Real.norm_eq_abs] at h₀
    rw [diamondSquareMap_one, Real.norm_eq_abs] at h₁
    unfold diamondRadius
    rcases le_total 0 (x 0) with hx | hx <;>
      rcases le_total 0 (x 1) with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
      exact (le_abs_self _).trans h₀
    · rw [abs_of_nonneg hx, abs_of_nonpos hy]
      exact (le_abs_self _).trans h₁
    · rw [abs_of_nonpos hx, abs_of_nonneg hy]
      linarith [(neg_le_abs (x 0 - x 1)).trans h₁]
    · rw [abs_of_nonpos hx, abs_of_nonpos hy]
      linarith [(neg_le_abs (x 0 + x 1)).trans h₀]

/-- Closed diamond regions map exactly to the original closed sup-norm squares. -/
theorem diamondSquareMap_mem_closedBall_iff (x : P) (r : ℝ) :
    diamondSquareMap x ∈ closedBall 0 r ↔ diamondRadius (x 0) (x 1) ≤ r := by
  rw [mem_closedBall_zero_iff, norm_diamondSquareMap]

/-- The exact Lebesgue-measure Jacobian of the actual transformation. -/
theorem map_volume_diamondSquareMap :
    Measure.map diamondSquareMap volume = ENNReal.ofReal (1 / 2) • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (by rw [det_diamondSquareMap]; norm_num), det_diamondSquareMap]
  norm_num

/-- The genuine change of variables, valid even under the zero-integral convention. -/
theorem integral_comp_diamondSquareMap (f : P → ℝ) :
    (∫ x, f (diamondSquareMap x)) = (1 / 2 : ℝ) * ∫ y, f y := by
  have hmap : Measure.map diamondSquareEquiv.toHomeomorph.toMeasurableEquiv volume =
      ENNReal.ofReal (1 / 2) • volume := map_volume_diamondSquareMap
  calc
    _ = ∫ y, f y ∂Measure.map diamondSquareEquiv.toHomeomorph.toMeasurableEquiv volume :=
      (integral_map_equiv diamondSquareEquiv.toHomeomorph.toMeasurableEquiv f).symm
    _ = _ := by rw [hmap, integral_smul_measure]; norm_num

/-- Exact radial integration for the actual diamond radius in the plane. -/
theorem integral_diamondRadius (f : ℝ → ℝ) :
    (∫ x : P, f (diamondRadius (x 0) (x 1))) =
      4 * ∫ t in Ioi (0 : ℝ), t * f t := by
  have hu : volume.real (ball (0 : P) 1) = 4 := by
    rw [Measure.real, Real.volume_pi_ball _ (by norm_num)]
    norm_num
  have h := integral_fun_norm_addHaar (volume : Measure P) f
  simp only [Module.finrank_pi, Fintype.card_fin,
    Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul, hu] at h
  have ht := integral_comp_diamondSquareMap (fun y : P ↦ f ‖y‖)
  simp only [norm_diamondSquareMap] at ht
  rw [h] at ht
  nlinarith [ht]

end PartialBalayage.Maximal.Square
