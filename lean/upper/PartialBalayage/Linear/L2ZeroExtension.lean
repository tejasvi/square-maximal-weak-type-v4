/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Genuine linear zero extension of restricted L² classes

An actual restricted-measure class is extended by its measurable-set indicator. The resulting
map is a linear isometry into whole-space `L²`; arbitrary representatives outside the set are
discarded. This is the value-coordinate map needed for an exhaustion by bounded domains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure X} {Ω : Set X}

/-- Actual zero extension of a restricted Hilbert class. -/
def zeroExtendL2 (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp f)).toLp (Ω.indicator (f : X → E))

omit [NormedSpace ℝ E] in
theorem zeroExtendL2_ae (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω)) :
    zeroExtendL2 hΩ f =ᵐ[μ] Ω.indicator (f : X → E) :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℝ E] in
/-- Zero extension preserves the actual restricted L² norm. -/
theorem norm_zeroExtendL2 (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω)) :
    ‖zeroExtendL2 hΩ f‖ = ‖f‖ := by
  rw [zeroExtendL2, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hΩ, Lp.norm_def]

omit [NormedSpace ℝ E] in
theorem zeroExtendL2_add (hΩ : MeasurableSet Ω) (f g : Lp E 2 (μ.restrict Ω)) :
    zeroExtendL2 hΩ (f + g) = zeroExtendL2 hΩ f + zeroExtendL2 hΩ g := by
  apply Lp.ext
  filter_upwards [zeroExtendL2_ae hΩ (f + g), zeroExtendL2_ae hΩ f,
    zeroExtendL2_ae hΩ g, Lp.coeFn_add (zeroExtendL2 hΩ f) (zeroExtendL2 hΩ g),
    (ae_restrict_iff' hΩ).mp (Lp.coeFn_add f g)] with x hab hf hg hsum hadd
  rw [hab, hsum, Pi.add_apply, hf, hg]
  by_cases hx : x ∈ Ω
  · simp only [indicator_of_mem hx]
    exact hadd hx
  · simp only [indicator_of_notMem hx, zero_add]

theorem zeroExtendL2_smul (hΩ : MeasurableSet Ω) (c : ℝ) (f : Lp E 2 (μ.restrict Ω)) :
    zeroExtendL2 hΩ (c • f) = c • zeroExtendL2 hΩ f := by
  apply Lp.ext
  filter_upwards [zeroExtendL2_ae hΩ (c • f), zeroExtendL2_ae hΩ f,
    Lp.coeFn_smul c (zeroExtendL2 hΩ f),
    (ae_restrict_iff' hΩ).mp (Lp.coeFn_smul c f)] with x hcf hf hsmul hcf'
  rw [hcf, hsmul, Pi.smul_apply, hf]
  by_cases hx : x ∈ Ω
  · simp only [indicator_of_mem hx]
    exact hcf' hx
  · simp only [indicator_of_notMem hx, smul_zero]

/-- The genuine bounded linear zero-extension map, with norm at most one. -/
def zeroExtendL2CLM (hΩ : MeasurableSet Ω) : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 μ :=
  ({ toFun := zeroExtendL2 hΩ
     map_add' := zeroExtendL2_add hΩ
     map_smul' := zeroExtendL2_smul hΩ } :
    Lp E 2 (μ.restrict Ω) →ₗ[ℝ] Lp E 2 μ).mkContinuous 1 (fun f ↦ by
      change ‖zeroExtendL2 hΩ f‖ ≤ 1 * ‖f‖
      rw [norm_zeroExtendL2, one_mul])

omit [NormedSpace ℝ E] in
/-- The actual isometry preserves Hilbert norms and supports every value in the domain. -/
theorem zeroExtendL2_supported (hΩ : MeasurableSet Ω) (f : Lp E 2 (μ.restrict Ω)) :
    ∀ᵐ x ∂μ, x ∉ Ω → zeroExtendL2 hΩ f x = 0 := by
  filter_upwards [zeroExtendL2_ae hΩ f] with x hx hnot
  rw [hx, indicator_of_notMem hnot]

end PartialBalayage.Linear
