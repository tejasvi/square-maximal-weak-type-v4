/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Compatibility of integral and Hilbert Fourier transforms

For a genuine integrable Hilbert-valued `L²` function, its unitary `L²` Fourier transform
is represented almost everywhere by the ordinary Fourier integral. This supplies the
actual uniform Fourier bound needed in low-frequency coercivity estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PartialBalayage.Linear

variable {X E : Type*}
variable [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The ordinary Fourier integral of an integrable vector function is continuous. -/
theorem continuous_fourier_integral {f : X → E} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- Integral Fourier duality applies to an integrable vector function and a Schwartz test. -/
theorem integral_fourier_schwartz_smul {f : X → E} (hf : Integrable f)
    (g : SchwartzMap X ℂ) :
    (∫ ξ, g ξ • 𝓕 f ξ) = ∫ x, 𝓕 g x • f x := by
  simpa only [Real.fourier_eq, SchwartzMap.fourier_coe, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, VectorFourier.fourierIntegral,
    LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm] using
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).flip
      (L := innerₗ X) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner hf g.integrable

/-- The actual unitary `L²` Fourier transform agrees with its ordinary Fourier integral. -/
theorem fourier_L2_ae_eq_integral (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) :
    (𝓕 f : Lp E 2 volume) =ᵐ[volume] 𝓕 (f : X → E) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num))
    ((continuous_fourier_integral hf).locallyIntegrable)
  intro g hg hgsupp
  let φ : SchwartzMap X ℂ :=
    (hgsupp.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hd : (∫ x, φ x • (𝓕 f : Lp E 2 volume) x) = ∫ x, 𝓕 φ x • f x := by
    have he := congrArg (fun T : TemperedDistribution X E ↦ T φ)
      (Lp.fourier_toTemperedDistribution_eq f)
    simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] using he.symm
  have hi := integral_fourier_schwartz_smul hf φ
  have hφ (x : X) : φ x = (g x : ℂ) := rfl
  simpa only [hφ, Complex.coe_smul] using hd.trans hi.symm

/-- The actual `L²` Fourier transform has the true `L¹` uniform bound almost everywhere. -/
theorem norm_fourier_L2_le_integral_norm (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) :
    ∀ᵐ ξ, ‖(𝓕 f : Lp E 2 volume) ξ‖ ≤ ∫ x, ‖f x‖ := by
  filter_upwards [fourier_L2_ae_eq_integral f hf] with ξ hξ
  rw [hξ]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ X) (f : X → E) ξ

end PartialBalayage.Linear
