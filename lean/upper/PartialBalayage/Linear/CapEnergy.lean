/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LevelSet
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Energy bounds for a capped integrable density

A pointwise cap `‖f‖ ≤ κ` implies `∫ ‖f‖² ≤ κ ∫ ‖f‖`. In particular a capped integrable density
belongs to `L²`, even when the ambient measure is infinite. A bounded operator on `L²` transports
this estimate to the energy bound used in the level-set argument.

All operators and decomposition hypotheses in this file are explicit. The construction of a
partial balayage with these properties remains a separate requirement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure X} {f : X → E} {g : X → F}

/-- A pointwise cap bounds the squared norm integral by the cap times the mass. -/
theorem lintegral_enorm_sq_le_of_cap {κ : ℝ} (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ ≤ ENNReal.ofReal κ * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  calc
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ ≤ ∫⁻ x, ENNReal.ofReal κ * ‖f x‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hcap] with x hx
      have hx' : ‖f x‖ₑ ≤ ENNReal.ofReal κ := by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
      simpa only [pow_two, mul_comm] using mul_le_mul_right hx' ‖f x‖ₑ
    _ = ENNReal.ofReal κ * ∫⁻ x, ‖f x‖ₑ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- An integrable density with an almost-everywhere finite cap belongs to `L²`. -/
theorem memLp_two_of_integrable_of_cap (hf : Integrable f μ) {κ : ℝ}
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) : MemLp f 2 μ := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hf.aestronglyMeasurable).mpr
  have hfinite := ENNReal.mul_lt_top (a := ENNReal.ofReal κ) ENNReal.ofReal_lt_top
    (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral)
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_enorm_sq_le_of_cap hcap).trans_lt hfinite

/-- The cap bounds the square of the standard `L²` seminorm by the `L¹` mass. -/
theorem eLpNorm_two_sq_le_of_cap (hf : AEStronglyMeasurable f μ) {κ : ℝ}
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) :
    eLpNorm f 2 μ ^ (2 : ℕ) ≤ ENNReal.ofReal κ * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have heq : eLpNorm f 2 μ ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
    simpa [ENNReal.rpow_two] using
      eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
  rw [heq]
  exact lintegral_enorm_sq_le_of_cap hcap

/-- An `L²` operator bound and the density's cap give the level-set proof's energy estimate. -/
theorem operator_energy_le_of_cap (hf : AEStronglyMeasurable f μ) {κ : ℝ}
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) {M : ℝ≥0}
    (hT : eLpNorm g 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ mass) :
    eLpNorm g 2 μ ^ (2 : ℕ) ≤ (M : ℝ≥0∞) ^ (2 : ℕ) * ENNReal.ofReal κ * mass := by
  calc
    eLpNorm g 2 μ ^ (2 : ℕ) ≤ ((M : ℝ≥0∞) * eLpNorm f 2 μ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hT _
    _ = (M : ℝ≥0∞) ^ (2 : ℕ) * eLpNorm f 2 μ ^ (2 : ℕ) := mul_pow _ _ _
    _ ≤ (M : ℝ≥0∞) ^ (2 : ℕ) * (ENNReal.ofReal κ * mass) := by
      exact mul_le_mul_right ((eLpNorm_two_sq_le_of_cap hf hcap).trans
        (mul_le_mul_right hmass _)) _
    _ = (M : ℝ≥0∞) ^ (2 : ℕ) * ENNReal.ofReal κ * mass := (mul_assoc _ _ _).symm

section ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- A bounded linear operator on the actual `L²` spaces satisfies the capped energy estimate. -/
theorem continuousLinearMap_energy_le_of_cap (T : Lp E 2 μ →L[𝕜] Lp F 2 μ)
    (hf : Integrable f μ) {κ : ℝ} (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) {M : ℝ≥0}
    (hT : ‖T‖₊ ≤ M) {mass : ℝ≥0∞} (hmass : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ mass) :
    eLpNorm (T ((memLp_two_of_integrable_of_cap hf hcap).toLp f)) 2 μ ^ (2 : ℕ) ≤
      (M : ℝ≥0∞) ^ (2 : ℕ) * ENNReal.ofReal κ * mass := by
  have hf2 := memLp_two_of_integrable_of_cap hf hcap
  have hnorm : ‖T (hf2.toLp f)‖ₑ ≤ (M : ℝ≥0∞) * ‖hf2.toLp f‖ₑ := by
    have hnnnorm : ‖T (hf2.toLp f)‖₊ ≤ M * ‖hf2.toLp f‖₊ :=
      (T.le_opNNNorm _).trans (mul_le_mul_of_nonneg_right hT (by positivity))
    simpa only [enorm, ENNReal.coe_mul] using ENNReal.coe_le_coe.mpr hnnnorm
  have hT' : eLpNorm (T (hf2.toLp f)) 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ := by
    rw [Lp.enorm_toLp] at hnorm
    simpa only [Lp.enorm_def] using hnorm
  exact operator_energy_le_of_cap hf.aestronglyMeasurable hcap hT' hmass

end ContinuousLinearMap

/-- Capped integrable data and an `L²` operator bound give the parameterized level estimate. -/
theorem levelSet_bound_of_cap_and_L2_bound {H : X → F} {s : Set X}
    (hs : MeasurableSet s) (heq : ∀ᵐ x ∂μ, x ∉ s → H x = g x)
    (hf : Integrable f μ) {t κ M : ℝ≥0} (ht : 0 < t) (hκ : 0 < κ)
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (κ : ℝ)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ mass) (hs_mass : (κ : ℝ≥0∞) * μ s ≤ mass)
    (hT : eLpNorm g 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤
      ((t / κ + M ^ (2 : ℕ) * κ / t : ℝ≥0) : ℝ≥0∞) * mass := by
  apply levelSet_bound_of_capped_decomposition hs heq ht hκ hs_mass
  simpa only [ENNReal.ofReal_coe_nnreal] using
    operator_energy_le_of_cap hf.aestronglyMeasurable hcap hT hmass

/-- Choosing the cap `t/M` gives the optimized `2M` level estimate from genuine capped data. -/
theorem levelSet_bound_two_mul_of_cap_and_L2_bound {H : X → F} {s : Set X}
    (hs : MeasurableSet s) (heq : ∀ᵐ x ∂μ, x ∉ s → H x = g x)
    (hf : Integrable f μ) {t M : ℝ≥0} (ht : 0 < t) (hM : 0 < M)
    (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ (t / M : ℝ≥0)) {mass : ℝ≥0∞}
    (hmass : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ mass)
    (hs_mass : ((t / M : ℝ≥0) : ℝ≥0∞) * μ s ≤ mass)
    (hT : eLpNorm g 2 μ ≤ (M : ℝ≥0∞) * eLpNorm f 2 μ) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖H x‖ₑ} ≤ (2 : ℝ≥0∞) * M * mass := by
  apply levelSet_bound_two_mul_of_capped_decomposition hs heq ht hM hs_mass
  simpa only [ENNReal.ofReal_coe_nnreal] using
    operator_energy_le_of_cap hf.aestronglyMeasurable hcap hT hmass

end PartialBalayage.Linear
