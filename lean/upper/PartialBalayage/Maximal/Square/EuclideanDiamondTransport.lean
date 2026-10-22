/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.EuclideanDiamondMaximal
public import PartialBalayage.Maximal.Square.MaximalTransport

/-!
# Genuine volume transfer from Euclidean to coordinate diamonds

The actual Euclidean coordinate equivalence preserves planar volume, every averaging
region, and every extended-real maximal level set. The all-input weak coefficient is
therefore preserved exactly under the change to the table's coordinate-space convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin 2 → ℝ

/-- The actual Euclidean-plane coordinate equivalence. -/
def euclideanCoordinateEquiv : E ≃ᵐ P := (MeasurableEquiv.toLp 2 P).symm

theorem measurePreserving_euclideanCoordinateEquiv :
    MeasurePreserving euclideanCoordinateEquiv volume volume :=
  PiLp.volume_preserving_ofLp (ι := Fin 2)

/-- Actual coordinate volume preservation applies to every set. -/
theorem volume_preimage_euclideanCoordinates (s : Set P) :
    volume (euclideanCoordinateEquiv ⁻¹' s) = volume s := by
  have h := euclideanCoordinateEquiv.measurableEmbedding.map_apply (volume : Measure E) s
  rw [measurePreserving_euclideanCoordinateEquiv.map_eq] at h
  exact h.symm

/-- The genuine nonnegative coordinate change applies to every function. -/
theorem lintegral_comp_euclideanCoordinates (f : P → ℝ≥0∞) :
    (∫⁻ x : E, f (euclideanCoordinateEquiv x)) = ∫⁻ y : P, f y := by
  have h := lintegral_map_equiv (μ := (volume : Measure E)) f euclideanCoordinateEquiv
  rw [measurePreserving_euclideanCoordinateEquiv.map_eq] at h
  exact h.symm

/-- The same exact nonnegative change of variables holds on each actual preimage region. -/
theorem setLIntegral_comp_euclideanCoordinates (s : Set P) (f : P → ℝ≥0∞) :
    (∫⁻ x in euclideanCoordinateEquiv ⁻¹' s, f (euclideanCoordinateEquiv x)) =
      ∫⁻ y in s, f y := by
  have he := euclideanCoordinateEquiv.measurableEmbedding
  have h := he.lintegral_map (μ := volume.restrict (euclideanCoordinateEquiv ⁻¹' s)) f
  rw [← he.restrict_map, measurePreserving_euclideanCoordinateEquiv.map_eq] at h
  exact h.symm

theorem integrable_comp_euclideanCoordinates {f : P → ℝ} (hf : Integrable f volume) :
    Integrable (fun x : E ↦ f (euclideanCoordinateEquiv x)) volume :=
  (measurePreserving_euclideanCoordinateEquiv.integrable_comp_emb
    euclideanCoordinateEquiv.measurableEmbedding).mpr hf

/-- The genuine closed Euclidean averaging region is the exact coordinate preimage. -/
theorem preimage_closedDiamond_euclideanCoordinates (x : E) (r : ℝ) :
    euclideanCoordinateEquiv ⁻¹' closedDiamond (euclideanCoordinateEquiv x) r =
      closedEuclideanDiamond x r := rfl

/-- Each original Euclidean diamond average equals the corresponding coordinate average. -/
theorem euclideanDiamondAverage_eq_coordinateAverage (f : P → ℝ) (x : E) (r : ℝ) :
    (volume (closedEuclideanDiamond x r))⁻¹ *
      (∫⁻ y in closedEuclideanDiamond x r, ‖f (euclideanCoordinateEquiv y)‖ₑ) =
        (volume (closedDiamond (euclideanCoordinateEquiv x) r))⁻¹ *
          ∫⁻ y in closedDiamond (euclideanCoordinateEquiv x) r, ‖f y‖ₑ := by
  have hv := volume_preimage_euclideanCoordinates
    (closedDiamond (euclideanCoordinateEquiv x) r)
  have hi := setLIntegral_comp_euclideanCoordinates
    (closedDiamond (euclideanCoordinateEquiv x) r) (fun y ↦ ‖f y‖ₑ)
  rw [preimage_closedDiamond_euclideanCoordinates] at hv hi
  rw [hv, hi]

/-- The full supremum over every positive radius is transported exactly. -/
theorem euclideanDiamondMaximalFunction_comp_euclideanCoordinates (f : P → ℝ) (x : E) :
    euclideanDiamondMaximalFunction (fun y ↦ f (euclideanCoordinateEquiv y)) x =
      diamondMaximalFunction f (euclideanCoordinateEquiv x) := by
  unfold euclideanDiamondMaximalFunction diamondMaximalFunction
  simp_rw [euclideanDiamondAverage_eq_coordinateAverage]

/-- Actual maximal level-set volume is preserved even when the level is infinite. -/
theorem volume_euclideanDiamondMaximal_level (f : P → ℝ) (α : ℝ≥0∞) :
    volume {x : E | α <
      euclideanDiamondMaximalFunction (fun y ↦ f (euclideanCoordinateEquiv y)) x} =
        volume {x : P | α < diamondMaximalFunction f x} := by
  convert volume_preimage_euclideanCoordinates {x : P | α < diamondMaximalFunction f x} using 1
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage,
    euclideanDiamondMaximalFunction_comp_euclideanCoordinates]

/-- A genuine Euclidean all-input weak bound is the table's exact coordinate diamond bound. -/
theorem isDiamondWeakTypeBound_of_euclidean {C : ℝ≥0∞}
    (hC : ∀ f : E → ℝ, Integrable f → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ) :
    IsDiamondWeakTypeBound C := by
  intro f hf α
  have h := hC (fun x : E ↦ f (euclideanCoordinateEquiv x))
    (integrable_comp_euclideanCoordinates hf) α
  rw [volume_euclideanDiamondMaximal_level,
    lintegral_comp_euclideanCoordinates (fun y ↦ ‖f y‖ₑ)] at h
  exact h

/-- The actual Euclidean diamond weak coefficient reaches the square table unchanged. -/
theorem isCubeWeakTypeBound_of_euclideanDiamond {C : ℝ≥0∞}
    (hC : ∀ f : E → ℝ, Integrable f → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ) :
    IsCubeWeakTypeBound 2 C :=
  isCubeWeakTypeBound_of_diamond (isDiamondWeakTypeBound_of_euclidean hC)

end PartialBalayage.Maximal.Square
