/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierL1L2

/-!
# Low- and high-frequency estimates for the actual Fourier energy

The Fourier `L¹` bound controls the low-frequency region, while the isotropic power weight
controls its complement. The estimate applies to Hilbert-valued inputs in every dimension.
The energy is a nonnegative extended integral, so no artificial integrability convention is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Metric Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*}
variable [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Actual isotropic Fourier energy with power `α`, including infinite values. -/
def fourierEnergy (α : ℝ) (f : Lp E 2 (volume : Measure X)) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ α) * ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ)

/-- Squared Hilbert `L²` norm is the integral of the squared actual Fourier representative. -/
theorem enorm_sq_eq_lintegral_fourier (f : Lp E 2 (volume : Measure X)) :
    ‖f‖ₑ ^ (2 : ℕ) = ∫⁻ ξ, ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ) := by
  have hn : ‖(𝓕 f : Lp E 2 volume)‖ₑ = ‖f‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, Lp.norm_fourier_eq]
  rw [← hn, Lp.enorm_def]
  simpa [ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) (Lp.aestronglyMeasurable (𝓕 f))

/-- The low-frequency squared mass is bounded by the actual input mass and region volume. -/
theorem setLIntegral_fourier_enorm_sq_le (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) (s : Set X) :
    (∫⁻ ξ in s, ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume s := by
  calc
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (norm_fourier_L2_le_integral_norm f hf)] with ξ hξ
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hξ 2)
    _ = _ := setLIntegral_const _ _

/-- A positive isotropic weight controls every frequency outside the radius `R`. -/
theorem setLIntegral_fourier_high_le (f : Lp E 2 (volume : Measure X))
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R) :
    (∫⁻ ξ in (closedBall (0 : X) R)ᶜ,
      ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ)) ≤
        ENNReal.ofReal (R ^ (-α)) * fourierEnergy α f := by
  have hw (ξ : X) (hξ : ξ ∈ (closedBall (0 : X) R)ᶜ) :
      1 ≤ R ^ (-α) * ‖ξ‖ ^ α := by
    have hξR : R ≤ ‖ξ‖ := le_of_lt (by
      simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hξ)
    calc
      1 = R ^ (-α) * R ^ α := by
        rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hR.le hξR hα) (Real.rpow_nonneg hR.le _)
  calc
    _ ≤ ∫⁻ ξ in (closedBall (0 : X) R)ᶜ,
        ENNReal.ofReal (R ^ (-α)) *
          (ENNReal.ofReal (‖ξ‖ ^ α) * ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ)) := by
      apply setLIntegral_mono' measurableSet_closedBall.compl
      intro ξ hξ
      have hh : 1 ≤ ENNReal.ofReal (R ^ (-α)) * ENNReal.ofReal (‖ξ‖ ^ α) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
        exact_mod_cast ENNReal.ofReal_le_ofReal (hw ξ hξ)
      simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_right hh (‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ))
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (R ^ (-α)) *
        (ENNReal.ofReal (‖ξ‖ ^ α) * ‖(𝓕 f : Lp E 2 volume) ξ‖ₑ ^ (2 : ℕ)) :=
      setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Low/high splitting for the genuine Hilbert Fourier transform and isotropic energy. -/
theorem enorm_sq_le_fourier_energy_split (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R) :
    ‖f‖ₑ ^ (2 : ℕ) ≤
      ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume (closedBall (0 : X) R) +
        ENNReal.ofReal (R ^ (-α)) * fourierEnergy α f := by
  rw [enorm_sq_eq_lintegral_fourier,
    ← lintegral_add_compl _ measurableSet_closedBall]
  exact add_le_add (setLIntegral_fourier_enorm_sq_le f hf _)
    (setLIntegral_fourier_high_le f hα hR)

end PartialBalayage.Linear
