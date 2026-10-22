/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondSquareTransport
public import PartialBalayage.Maximal.Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Exact transfer from diamonds to the table's squares

The genuine linear change of coordinates transports every closed averaging region,
its integral, and every maximal-function level set. Both measure factors cancel,
so the all-input weak constant is preserved exactly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "P" => Fin 2 → ℝ

/-- The actual closed diamond centered at `x`, of radius `r`. -/
def closedDiamond (x : P) (r : ℝ) : Set P :=
  {y | diamondRadius (y 0 - x 0) (y 1 - x 1) ≤ r}

/-- The centered maximal function for the actual closed diamond averages. -/
def diamondMaximalFunction (f : P → ℝ) (x : P) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r),
    (volume (closedDiamond x r))⁻¹ * ∫⁻ y in closedDiamond x r, ‖f y‖ₑ

/-- A weak bound for every integrable input and every level for the actual diamonds. -/
def IsDiamondWeakTypeBound (C : ℝ≥0∞) : Prop :=
  ∀ f : P → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < diamondMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The exact preimage of a square centered at the transformed center. -/
theorem preimage_closedBall_diamondSquareMap (x : P) (r : ℝ) :
    diamondSquareMap ⁻¹' closedBall (diamondSquareMap x) r = closedDiamond x r := by
  ext y
  simp only [mem_preimage, mem_closedBall, dist_eq_norm]
  rw [← diamondSquareMap.map_sub, norm_diamondSquareMap]
  rfl

/-- The Jacobian formula applies to every set, without a measurability assumption. -/
theorem volume_preimage_diamondSquareMap (s : Set P) :
    volume (diamondSquareMap ⁻¹' s) = (1 / 2 : ℝ≥0∞) * volume s := by
  have h := diamondSquareEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_apply
    (volume : Measure P) s
  change Measure.map diamondSquareMap volume s = _ at h
  rw [map_volume_diamondSquareMap, Measure.smul_apply, smul_eq_mul] at h
  have hc : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc] at h
  exact h.symm

/-- The genuine nonnegative change of variables applies to every function. -/
theorem lintegral_comp_diamondSquareMap (f : P → ℝ≥0∞) :
    (∫⁻ x, f (diamondSquareMap x)) = (1 / 2 : ℝ≥0∞) * ∫⁻ y, f y := by
  have h := lintegral_map_equiv (μ := (volume : Measure P)) f
    diamondSquareEquiv.toHomeomorph.toMeasurableEquiv
  change (∫⁻ y, f y ∂Measure.map diamondSquareMap volume) =
    ∫⁻ x, f (diamondSquareMap x) at h
  rw [map_volume_diamondSquareMap, lintegral_smul_measure] at h
  have hc : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc] at h
  exact h.symm

/-- Restriction to the true preimage preserves the same Jacobian. -/
theorem setLIntegral_comp_diamondSquareMap (s : Set P) (f : P → ℝ≥0∞) :
    (∫⁻ x in diamondSquareMap ⁻¹' s, f (diamondSquareMap x)) =
      (1 / 2 : ℝ≥0∞) * ∫⁻ y in s, f y := by
  have he : MeasurableEmbedding (diamondSquareMap : P → P) :=
    diamondSquareEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have h := he.lintegral_map (μ := volume.restrict (diamondSquareMap ⁻¹' s)) f
  change (∫⁻ y, f y ∂Measure.map diamondSquareMap
    (volume.restrict (diamondSquareMap ⁻¹' s))) =
    ∫⁻ x in diamondSquareMap ⁻¹' s, f (diamondSquareMap x) at h
  rw [← he.restrict_map, map_volume_diamondSquareMap, Measure.restrict_smul,
    lintegral_smul_measure] at h
  have hc : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc] at h
  exact h.symm

/-- Actual integrable square inputs pull back to actual integrable diamond inputs. -/
theorem integrable_comp_diamondSquareMap {f : P → ℝ} (hf : Integrable f) :
    Integrable (fun x ↦ f (diamondSquareMap x)) := by
  have h : Integrable f (Measure.map diamondSquareMap volume) := by
    rw [map_volume_diamondSquareMap]
    exact hf.smul_measure (by simp)
  exact h.comp_measurable diamondSquareEquiv.continuous.measurable

/-- Every actual square average equals its corresponding diamond average. -/
theorem cubeAverage_eq_diamondAverage (f : P → ℝ) (x : P) (r : ℝ) :
    (volume (closedBall (diamondSquareMap x) r))⁻¹ *
        ∫⁻ y in closedBall (diamondSquareMap x) r, ‖f y‖ₑ =
      (volume (closedDiamond x r))⁻¹ *
        ∫⁻ y in closedDiamond x r, ‖f (diamondSquareMap y)‖ₑ := by
  have hv := volume_preimage_diamondSquareMap (closedBall (diamondSquareMap x) r)
  have hi := setLIntegral_comp_diamondSquareMap
    (closedBall (diamondSquareMap x) r) (fun y ↦ ‖f y‖ₑ)
  rw [preimage_closedBall_diamondSquareMap] at hv hi
  have hc₀ : (1 / 2 : ℝ≥0∞) ≠ 0 := by simp
  have hct : (1 / 2 : ℝ≥0∞) ≠ ∞ := by simp
  rw [hv, hi, ENNReal.mul_inv (Or.inl hc₀) (Or.inl hct)]
  simp only [one_div, inv_inv]
  calc
    _ = (volume (closedBall (diamondSquareMap x) r))⁻¹ *
      ((2⁻¹ * 2) * ∫⁻ y in closedBall (diamondSquareMap x) r, ‖f y‖ₑ) := by
        rw [ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
    _ = _ := by simp only [mul_comm, mul_left_comm, mul_assoc]


/-- The supremum over all positive radii is transported exactly. -/
theorem cubeMaximalFunction_comp_diamondSquareMap (f : P → ℝ) (x : P) :
    cubeMaximalFunction f (diamondSquareMap x) =
      diamondMaximalFunction (fun y ↦ f (diamondSquareMap y)) x := by
  unfold cubeMaximalFunction diamondMaximalFunction
  simp_rw [cubeAverage_eq_diamondAverage]

/-- The exact level-set measure transformation, including infinite levels. -/
theorem volume_diamondMaximal_level (f : P → ℝ) (α : ℝ≥0∞) :
    volume {x | α < diamondMaximalFunction (fun y ↦ f (diamondSquareMap y)) x} =
      (1 / 2 : ℝ≥0∞) * volume {x | α < cubeMaximalFunction f x} := by
  convert volume_preimage_diamondSquareMap {x | α < cubeMaximalFunction f x} using 1
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, cubeMaximalFunction_comp_diamondSquareMap]

/-- A genuine all-input diamond weak bound implies the table's square weak bound. -/
theorem isCubeWeakTypeBound_of_diamond {C : ℝ≥0∞} (hC : IsDiamondWeakTypeBound C) :
    IsCubeWeakTypeBound 2 C := by
  intro f hf α
  have h := hC (fun y ↦ f (diamondSquareMap y))
    (integrable_comp_diamondSquareMap hf) α
  rw [volume_diamondMaximal_level,
    lintegral_comp_diamondSquareMap (fun y ↦ ‖f y‖ₑ)] at h
  have h' : (2 : ℝ≥0∞) * (α * (1 / 2 * volume {x | α < cubeMaximalFunction f x})) ≤
      2 * (C * (1 / 2 * ∫⁻ x, ‖f x‖ₑ)) := by
    simpa only [mul_comm] using mul_le_mul_left h (2 : ℝ≥0∞)
  have hl : (2 : ℝ≥0∞) * (α * (1 / 2 * volume {x | α < cubeMaximalFunction f x})) =
      α * volume {x | α < cubeMaximalFunction f x} := by
    calc
      _ = (2 * (1 / 2)) * (α * volume {x | α < cubeMaximalFunction f x}) := by ac_rfl
      _ = _ := by
        rw [ENNReal.mul_div_cancel (by norm_num) (by simp), one_mul]
  have hr : (2 : ℝ≥0∞) * (C * (1 / 2 * ∫⁻ x, ‖f x‖ₑ)) = C * ∫⁻ x, ‖f x‖ₑ := by
    calc
      _ = (2 * (1 / 2)) * (C * ∫⁻ x, ‖f x‖ₑ) := by ac_rfl
      _ = _ := by
        rw [ENNReal.mul_div_cancel (by norm_num) (by simp), one_mul]
  rwa [hl, hr] at h'

end PartialBalayage.Maximal.Square
