/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual translation-square control by the singular jump energy

The genuine stable jump density has a positive explicit lower bound on every
interval of positive jumps. Thus its actual Hilbert data control unweighted
translation squares there, including arbitrarily large intervals. These estimates
are the first step of physical-space averaging bounds for the stable obstacle.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual positive-jump averaging interval. -/
def jumpAveragingBand (R : ℝ) : Set ℝ := Icc R (2 * R)

/-- The actual stable-density lower bound on the averaging interval. -/
def jumpAveragingWeight (α R : ℝ) : ℝ :=
  stableNormalization α * (2 * R) ^ (-(1 + α))

theorem jumpAveragingWeight_pos {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) : 0 < jumpAveragingWeight α R :=
  mul_pos (stableNormalization_pos hα0 hα2)
    (Real.rpow_pos_of_pos (by positivity) _)

/-- The true singular measure controls every unweighted nonnegative interval integral. -/
theorem jumpAveragingWeight_mul_lintegral_le {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (F : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (jumpAveragingWeight α R) *
      (∫⁻ t in jumpAveragingBand R, F t) ≤ ∫⁻ t, F t ∂stableJumpMeasure α := by
  have hs : jumpAveragingBand R ⊆ Ioi 0 := by
    intro t ht
    exact lt_of_lt_of_le hR ht.1
  have hd : Measurable (fun t : ℝ ↦
      ENNReal.ofReal (stableNormalization α * t ^ (-(1 + α)))) := by fun_prop
  have he : ∫⁻ t, F t ∂stableJumpMeasure α =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (stableNormalization α * t ^ (-(1 + α))) * F t := by
    rw [stableJumpMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable
      _ hd (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
    rfl
  rw [he]
  calc
    _ = ∫⁻ t in jumpAveragingBand R, ENNReal.ofReal (jumpAveragingWeight α R) * F t :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in jumpAveragingBand R,
        ENNReal.ofReal (stableNormalization α * t ^ (-(1 + α))) * F t := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hR ht.1) ht.2
          (by linarith)) (stableNormalization_pos hα0 hα2).le
    _ ≤ _ := lintegral_mono_set hs

/-- Genuine singular jump data control the actual unweighted translation squares. -/
theorem jumpAveragingWeight_mul_translation_lintegral_le {α R : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R)
    (U : StableJumpEnergySpace α) (i : Fin 2) :
    ENNReal.ofReal (jumpAveragingWeight α R) *
      (∫⁻ x : E, ∫⁻ t in jumpAveragingBand R,
        ‖coordinateJump (stableJumpValue α U : E → ℝ) i (x, t)‖ₑ ^ (2 : ℕ)) ≤
      ‖stableJumpData α U i‖ₑ ^ (2 : ℕ) := by
  have hu := Lp.aestronglyMeasurable (stableJumpValue α U)
  have hm : AEStronglyMeasurable
      (coordinateJump (stableJumpValue α U : E → ℝ) i) (spatialJumpMeasure α) :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_coordinateJumpPoint α i)).sub
      (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fst
        (μ := (volume : Measure E)) (ν := stableJumpMeasure α)))
  rw [stableJumpData_enorm_sq]
  change _ ≤ ∫⁻ p : E × ℝ,
    ‖coordinateJump (stableJumpValue α U : E → ℝ) i p‖ₑ ^ (2 : ℕ)
      ∂((volume : Measure E).prod (stableJumpMeasure α))
  rw [lintegral_prod _ (hm.enorm.pow_const 2), ← lintegral_const_mul'
    _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun x ↦ jumpAveragingWeight_mul_lintegral_le hα0 hα2 hR _

/-- The same actual translation bound with the jump parameter integrated first. -/
theorem jumpAveragingWeight_mul_translation_lintegral_le_symm {α R : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R)
    (U : StableJumpEnergySpace α) (i : Fin 2) :
    ENNReal.ofReal (jumpAveragingWeight α R) *
      (∫⁻ t in jumpAveragingBand R, ∫⁻ x : E,
        ‖coordinateJump (stableJumpValue α U : E → ℝ) i (x, t)‖ₑ ^ (2 : ℕ)) ≤
      ‖stableJumpData α U i‖ₑ ^ (2 : ℕ) := by
  have hu := Lp.aestronglyMeasurable (stableJumpValue α U)
  have hm : AEStronglyMeasurable
      (coordinateJump (stableJumpValue α U : E → ℝ) i) (spatialJumpMeasure α) :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_coordinateJumpPoint α i)).sub
      (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fst
        (μ := (volume : Measure E)) (ν := stableJumpMeasure α)))
  have h := jumpAveragingWeight_mul_lintegral_le hα0 hα2 hR
    (fun t ↦ ∫⁻ x : E,
      ‖coordinateJump (stableJumpValue α U : E → ℝ) i (x, t)‖ₑ ^ (2 : ℕ))
  convert h using 1
  rw [stableJumpData_enorm_sq]
  exact lintegral_prod_symm _ (hm.enorm.pow_const 2)

end PartialBalayage.Maximal.Square
