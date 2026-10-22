/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.L2ZeroExtension
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual mass preservation under L² zero extension

Zero extension discards the representatives outside the domain and preserves the true norm
integral whenever the restricted function is integrable. This supplies the whole-space mass
bound for finite-domain obstacle densities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable {μ : Measure X} {Ω : Set X}

/-- Genuine zero extension preserves integrability from the restricted measure. -/
theorem integrable_zeroExtendL2 (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω))
    (hf : Integrable (f : X → E) (μ.restrict Ω)) :
    Integrable (zeroExtendL2 hΩ f : X → E) μ :=
  ((integrable_indicator_iff hΩ).mpr hf).congr (zeroExtendL2_ae hΩ f).symm

/-- The actual whole-space norm integral equals the restricted norm integral. -/
theorem integral_norm_zeroExtendL2 (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω)) :
    (∫ x, ‖zeroExtendL2 hΩ f x‖ ∂μ) = ∫ x, ‖f x‖ ∂(μ.restrict Ω) := by
  calc
    (∫ x, ‖zeroExtendL2 hΩ f x‖ ∂μ) = ∫ x, ‖Ω.indicator (f : X → E) x‖ ∂μ :=
      integral_congr_ae ((zeroExtendL2_ae hΩ f).fun_comp norm)
    _ = ∫ x, Ω.indicator (fun y ↦ ‖f y‖) x ∂μ := by
      congr 1
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    _ = _ := integral_indicator hΩ

end PartialBalayage.Linear
