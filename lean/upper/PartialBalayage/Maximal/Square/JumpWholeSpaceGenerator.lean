/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpWholeSpaceObstacle

/-!
# The actual normalized generator equation of whole-space jump balayage

The genuine form equation on all energy tests gives the original physical
singular-integral generator PDE on compact C² tests. The actual whole-space
constructor supplies every state, density, positivity, and mass hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine full form equation is the actual normalized physical generator equation. -/
theorem stableJump_generator_equation_of_form {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) (f ν : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (stableJumpValue α U : E → ℝ) volume)
    (hpde : ∀ V : StableJumpEnergySpace α, stableJumpForm α U V =
      ⟪f - ν, stableJumpValue α V⟫)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) =
      ∫ x : E, (ν x - f x) * φ x := by
  obtain ⟨V, hV, _⟩ :=
    exists_stableJumpCompactC1Test hα0 hα2 (hφ.of_le (by norm_num)) hs
  have he := hpde V
  rw [stableJumpForm_eq_neg_integral_coordinateStableGenerator
    hα0 hα2 U V hu φ hφ hs hV, L2.inner_def] at he
  have hright : (∫ x : E, ⟪(f - ν) x, stableJumpValue α V x⟫) =
      ∫ x : E, (f x - ν x) * φ x := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f ν, hV] with x hsub hv
    simp only [Real.inner_apply, hsub, Pi.sub_apply, hv]
  rw [hright] at he
  calc
    _ = -(∫ x : E, (f x - ν x) * φ x) := by linarith
    _ = _ := by
      rw [← integral_neg]
      congr 1
      funext x
      ring

/-- Positive physical input admits actual normalized coordinate-stable whole-space balayage,
with no state or mass certificate assumptions. -/
theorem exists_positive_stableJump_generator_obstacle {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (κ : ℝ≥0) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : Integrable (f : E → ℝ) volume)
    (hfpos : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∃ (ν : Lp ℝ 2 (volume : Measure E)) (U : StableJumpEnergySpace α),
      (∀ᵐ x ∂volume, 0 ≤ ν x ∧ ν x ≤ (κ : ℝ)) ∧
      Integrable (ν : E → ℝ) volume ∧ (∫ x : E, ν x) = ∫ x : E, f x ∧
      ‖ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x : E, ‖f x‖ ∧
      (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α U x) ∧
      Integrable (stableJumpValue α U : E → ℝ) volume ∧
      (∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        (∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) =
          ∫ x : E, (ν x - f x) * φ x) ∧
      (∀ᵐ x ∂volume, stableJumpValue α U x ≠ 0 → ν x = (κ : ℝ)) ∧
      ((κ : ℝ≥0∞) * volume (stableJumpActiveSet α U) ≤ ∫⁻ x : E, ‖f x‖ₑ) ∧
      volume (stableJumpActiveSet α U) ≠ ⊤ := by
  obtain ⟨ν, U, hν, hνint, hmass, hL2, hU, hUint, hpde, hsat, hactive, hfin⟩ :=
    exists_positive_stableJump_obstacle hα0 hα2 κ hκ f hf hfpos
  exact ⟨ν, U, hν, hνint, hmass, hL2, hU, hUint,
    stableJump_generator_equation_of_form hα0 hα2 U f ν hUint hpde, hsat, hactive, hfin⟩

end PartialBalayage.Maximal.Square
