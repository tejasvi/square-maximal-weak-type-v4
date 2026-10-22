/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceMassCompactness

/-!
# Actual integrability and energy of whole-space capped densities

Membership in the genuine cap-and-mass set gives true integrability, the ordinary full norm
mass bound, and the sharp squared L² norm bound. These conclusions hold on infinite ambient
measure spaces and need no additional density-integrability assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable {μ : Measure X} {κ mass : ℝ≥0} {f : Lp E 2 μ}

/-- The actual finite mass constraint implies genuine whole-space integrability. -/
theorem integrable_of_mem_normMassCap (hf : f ∈ normMassCap μ κ mass) :
    Integrable (f : X → E) μ := by
  refine ⟨Lp.aestronglyMeasurable f, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact hf.2.trans_lt ENNReal.coe_lt_top

/-- The true ordinary norm integral is bounded by the actual mass cap. -/
theorem integral_norm_le_of_mem_normMassCap (hf : f ∈ normMassCap μ κ mass) :
    (∫ x, ‖f x‖ ∂μ) ≤ (mass : ℝ) := by
  have hm := hf.2
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_of_mem_normMassCap hf),
    ← ENNReal.ofReal_coe_nnreal] at hm
  exact (ENNReal.ofReal_le_ofReal_iff mass.coe_nonneg).mp hm

/-- The cap and mass give the sharp energy bound for the actual L² density. -/
theorem norm_sq_le_of_mem_normMassCap (hf : f ∈ normMassCap μ κ mass) :
    ‖f‖ ^ (2 : ℕ) ≤ (κ : ℝ) * (mass : ℝ) := by
  have he := eLpNorm_two_sq_le_of_cap (Lp.aestronglyMeasurable f) hf.1
  have hm : ENNReal.ofReal (κ : ℝ) * (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      (κ : ℝ≥0∞) * (mass : ℝ≥0∞) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact mul_le_mul_right hf.2 _
  have hs : ‖f‖ₑ ^ (2 : ℕ) ≤ (κ : ℝ≥0∞) * (mass : ℝ≥0∞) := by
    simpa only [← Lp.enorm_def] using he.trans hm
  have hn : ‖f‖₊ ^ (2 : ℕ) ≤ κ * mass := by
    apply ENNReal.coe_le_coe.mp
    simpa only [enorm, ENNReal.coe_pow, ENNReal.coe_mul] using hs
  exact_mod_cast hn

end PartialBalayage.Linear
