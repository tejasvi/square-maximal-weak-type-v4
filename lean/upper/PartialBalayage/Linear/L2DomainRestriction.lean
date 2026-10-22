/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.L2ZeroExtension
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual domain restriction of `L²` inputs

Restriction is the genuine bounded linear map between the actual measure-theoretic `L²`
spaces. Its representatives agree almost everywhere on the domain and its full-vector mass
does not exceed the whole-space input mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure X}

/-- Genuine scalar-linear restriction to an arbitrary domain. -/
def restrictL2CLM (Ω : Set X) : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict Ω) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self (μ := μ) (s := Ω)))

theorem restrictL2CLM_ae (Ω : Set X) (f : Lp E 2 μ) :
    restrictL2CLM Ω f =ᵐ[μ.restrict Ω] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- Domain restriction does not increase the actual `L²` norm. -/
theorem norm_restrictL2CLM_le (Ω : Set X) (f : Lp E 2 μ) : ‖restrictL2CLM Ω f‖ ≤ ‖f‖ := by
  have h := (restrictL2CLM (E := E) (μ := μ) Ω).le_opNorm f
  have hb : ‖restrictL2CLM (E := E) (μ := μ) Ω‖ ≤ 1 := by
    simpa only [restrictL2CLM, ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (p := (2 : ℝ≥0∞)) (E := E)
        (c := 1) (by simp) (by simpa using (Measure.restrict_le_self (μ := μ) (s := Ω)))
  exact h.trans ((mul_le_mul_of_nonneg_right hb (norm_nonneg f)).trans_eq (one_mul _))

/-- The actual restricted input's full-vector mass is at most the original input mass. -/
theorem integral_norm_restrictL2CLM_le (Ω : Set X) (f : Lp E 2 μ)
    (hf : Integrable (f : X → E) μ) :
    (∫ x, ‖restrictL2CLM Ω f x‖ ∂(μ.restrict Ω)) ≤ ∫ x, ‖f x‖ ∂μ := by
  have heq : (∫ x, ‖restrictL2CLM Ω f x‖ ∂(μ.restrict Ω)) = ∫ x in Ω, ‖f x‖ ∂μ :=
    integral_congr_ae ((restrictL2CLM_ae Ω f).fun_comp norm)
  rw [heq]
  exact setIntegral_le_integral hf.norm (Eventually.of_forall (fun x ↦ norm_nonneg (f x)))

end PartialBalayage.Linear
