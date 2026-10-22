/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourcePairing
public import PartialBalayage.Maximal.L2MollifiedSource

/-!
# Actual mollified states have bounded quadratic source differences

Compact smooth convolution kernels give genuinely bounded second derivatives
of L² inputs. The resulting global Lipschitz derivative supplies the full
source moment estimate for each actual mollified state.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped Convolution NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Compact C¹ convolution of an actual L² input is globally Lipschitz. -/
theorem exists_lipschitzWith_convolution_of_memLp_two
    {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : A →L[ℝ] ℝ →L[ℝ] F) {u : E → ℝ} {φ : E → A}
    (hu : MemLp u 2 volume) (hs : HasCompactSupport φ) (hφ : ContDiff ℝ 1 φ) :
    ∃ L : ℝ≥0, LipschitzWith L (φ ⋆[B, volume] u) := by
  have huLocal := hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  obtain ⟨G, hG, hb⟩ := PartialBalayage.exists_bound_convolution_of_memLp_two (B.precompL E)
    (hc.memLp_of_hasCompactSupport (hs.fderiv ℝ)) hu
  refine ⟨⟨G, hG⟩, lipschitzWith_of_nnnorm_fderiv_le (fun x ↦
    (hs.hasFDerivAt_convolution_left B hφ huLocal x).differentiableAt) ?_⟩
  intro x
  rw [(hs.hasFDerivAt_convolution_left B hφ huLocal x).fderiv]
  exact_mod_cast hb x

/-- The actual derivative of a compact smooth L² mollification is globally Lipschitz. -/
theorem mollification_has_lipschitz_fderiv
    (u φ : E → ℝ) (hu : MemLp u 2 volume)
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ L : ℝ≥0, LipschitzWith L (fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u)) := by
  have huLocal := hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hD : fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) =
      (fderiv ℝ φ) ⋆[((lsmul ℝ ℝ).precompL E), volume] u := by
    funext x
    exact (hs.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
      (hφ.of_le (by simp)) huLocal x).fderiv
  rw [hD]
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hψ : ContDiff ℝ 1 (fderiv ℝ φ) := hφtwo.fderiv_right (by norm_num)
  exact exists_lipschitzWith_convolution_of_memLp_two ((lsmul ℝ ℝ).precompL E)
    hu (hs.fderiv ℝ) hψ

/-- Every true smooth L² mollification obeys a genuine global full-source moment bound. -/
theorem exists_mollified_symmetricSecondDifference_bound
    (u φ : E → ℝ) (hu : MemLp u 2 volume)
    (hs : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : E,
      ‖(φ ⋆[lsmul ℝ ℝ, volume] u) (x + z) +
        (φ ⋆[lsmul ℝ ℝ, volume] u) (x - z) -
          2 * (φ ⋆[lsmul ℝ ℝ, volume] u) x‖ ≤ C * compensatedJumpMoment z := by
  obtain ⟨L, hL⟩ := mollification_has_lipschitz_fderiv u φ hu hs hφ
  obtain ⟨M, _, hM⟩ := PartialBalayage.exists_bound_convolution_of_memLp_two (lsmul ℝ ℝ)
    (hφ.continuous.memLp_of_hasCompactSupport hs) hu
  exact exists_bounded_symmetricSecondDifference_bound
    ((hs.contDiff_convolution_left (lsmul ℝ ℝ) hφ
      (hu.locallyIntegrable (by norm_num))).differentiable (by simp)) hL hM

end PartialBalayage.Maximal.Square
