/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual singular second-difference bounds

A quadratic estimate near zero and a uniform estimate at infinity control the
full stable singular integral. Both parts use exact power integrals. This gives
the small-cutoff error required when deleting the singular origin of a kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact near-zero integral in a stable second-difference estimate. -/
theorem integral_stable_near_zero {α r : ℝ} (hα : α < 2) (hr : 0 < r) :
    (∫ t in Ioc 0 r, t ^ (1 - α)) = r ^ (2 - α) / (2 - α) := by
  rw [← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (show -1 < 1 - α by linarith))]
  have he : 1 - α + 1 = 2 - α := by ring
  rw [he, Real.zero_rpow (by linarith : 2 - α ≠ 0), sub_zero]

/-- The exact large-jump integral in a stable second-difference estimate. -/
theorem integral_stable_far {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    (∫ t in Ioi r, t ^ (-1 - α)) = r ^ (-α) / α := by
  rw [integral_Ioi_rpow_of_lt (show -1 - α < -1 by linarith) hr]
  have he : -1 - α + 1 = -α := by ring
  rw [he]
  simp only [neg_div_neg_eq]

private theorem stable_weighted_near_integrable {α r M : ℝ}
    (hα : α < 2) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ M * t ^ (1 - α)) (Ioc 0 r) := by
  apply Integrable.const_mul
  change IntegrableOn (fun t : ℝ ↦ t ^ (1 - α)) (Ioc 0 r)
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)

private theorem stable_weighted_far_integrable {α r M : ℝ}
    (hα : 0 < α) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ M * t ^ (-1 - α)) (Ioi r) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith) hr).const_mul M

private theorem stable_weighted_norm_le_near {α M : ℝ} (g : ℝ → F)
    {t : ℝ} (ht : 0 < t) (hg : ‖g t‖ ≤ M * t ^ 2) :
    ‖t ^ (-1 - α) • g t‖ ≤ M * t ^ (1 - α) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  calc
    _ ≤ t ^ (-1 - α) * (M * t ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg ht.le _)
    _ = M * t ^ (1 - α) := by
      rw [← Real.rpow_natCast t 2, mul_left_comm, ← Real.rpow_add ht]
      congr 2
      norm_num
      ring

/-- The actual stable singular integral exists under quadratic and bounded estimates. -/
theorem integrable_stable_weighted_difference {α r M₂ M₀ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (g : ℝ → F)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hnear : ∀ t ∈ Ioc 0 r, ‖g t‖ ≤ M₂ * t ^ 2)
    (hfar : ∀ t ∈ Ioi r, ‖g t‖ ≤ 4 * M₀) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) • g t) (Ioi 0) := by
  have hw : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-1 - α))
      (volume.restrict (Ioi 0)) := by fun_prop
  have hm : AEStronglyMeasurable (fun t ↦ t ^ (-1 - α) • g t)
      (volume.restrict (Ioi 0)) := hw.smul hg
  have hn : IntegrableOn (fun t ↦ t ^ (-1 - α) • g t) (Ioc 0 r) := by
    apply (stable_weighted_near_integrable hα2 hr (M := M₂)).mono'
      (hm.mono_measure (Measure.restrict_mono (by intro t ht; exact ht.1) le_rfl))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact stable_weighted_norm_le_near g ht.1 (hnear t ht)
  have hf : IntegrableOn (fun t ↦ t ^ (-1 - α) • g t) (Ioi r) := by
    apply (stable_weighted_far_integrable hα0 hr (M := 4 * M₀)).mono'
      (hm.mono_measure (Measure.restrict_mono (by intro t ht; exact hr.trans ht) le_rfl))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hr.trans ht).le _)]
    calc
      _ ≤ t ^ (-1 - α) * (4 * M₀) :=
        mul_le_mul_of_nonneg_left (hfar t ht) (Real.rpow_nonneg (hr.trans ht).le _)
      _ = _ := mul_comm _ _
  rw [← Ioc_union_Ioi_eq_Ioi hr.le, integrableOn_union]
  exact ⟨hn, hf⟩

/-- The full singular integral has its exact quadratic-plus-tail estimate. -/
theorem norm_integral_stable_weighted_difference_le [CompleteSpace F]
    {α r M₂ M₀ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (g : ℝ → F)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hnear : ∀ t ∈ Ioc 0 r, ‖g t‖ ≤ M₂ * t ^ 2)
    (hfar : ∀ t ∈ Ioi r, ‖g t‖ ≤ 4 * M₀) :
    ‖∫ t in Ioi 0, t ^ (-1 - α) • g t‖ ≤
      M₂ * r ^ (2 - α) / (2 - α) + 4 * M₀ * r ^ (-α) / α := by
  have hi := integrable_stable_weighted_difference hα0 hα2 hr g hg hnear hfar
  have hn := hi.mono_set (show Ioc 0 r ⊆ Ioi 0 from fun _ h ↦ h.1)
  have hf := hi.mono_set (show Ioi r ⊆ Ioi 0 from fun _ h ↦ hr.trans h)
  have hnle : (∫ t in Ioc 0 r, ‖t ^ (-1 - α) • g t‖) ≤
      M₂ * r ^ (2 - α) / (2 - α) := by
    calc
      _ ≤ ∫ t in Ioc 0 r, M₂ * t ^ (1 - α) := by
        apply integral_mono_ae hn.norm (stable_weighted_near_integrable hα2 hr)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact stable_weighted_norm_le_near g ht.1 (hnear t ht)
      _ = _ := by rw [integral_const_mul, integral_stable_near_zero hα2 hr]; ring
  have hfle : (∫ t in Ioi r, ‖t ^ (-1 - α) • g t‖) ≤
      4 * M₀ * r ^ (-α) / α := by
    calc
      _ ≤ ∫ t in Ioi r, (4 * M₀) * t ^ (-1 - α) := by
        apply integral_mono_ae hf.norm (stable_weighted_far_integrable hα0 hr)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (hr.trans ht).le _)]
        exact (mul_le_mul_of_nonneg_left (hfar t ht)
          (Real.rpow_nonneg (hr.trans ht).le _)).trans_eq (mul_comm _ _)
      _ = _ := by rw [integral_const_mul, integral_stable_far hα0 hr]; ring
  have hd : Disjoint (Ioc (0 : ℝ) r) (Ioi r) := by
    apply disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  calc
    _ ≤ ∫ t in Ioi 0, ‖t ^ (-1 - α) • g t‖ := norm_integral_le_integral_norm _
    _ = (∫ t in Ioc 0 r, ‖t ^ (-1 - α) • g t‖) +
        ∫ t in Ioi r, ‖t ^ (-1 - α) • g t‖ := by
      rw [← Ioc_union_Ioi_eq_Ioi hr.le, setIntegral_union hd measurableSet_Ioi hn.norm hf.norm]
    _ ≤ _ := add_le_add hnle hfle

/-- Small cutoffs with amplitude `C * ε²` have an actual `ε^(2-α)` generator error. -/
theorem norm_integral_stable_small_cutoff_le [CompleteSpace F]
    {α ε C : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hε : 0 < ε) (g : ℝ → F)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hnear : ∀ t ∈ Ioc 0 ε, ‖g t‖ ≤ C * t ^ 2)
    (hfar : ∀ t ∈ Ioi ε, ‖g t‖ ≤ 4 * (C * ε ^ 2)) :
    ‖∫ t in Ioi 0, t ^ (-1 - α) • g t‖ ≤
      C * (1 / (2 - α) + 4 / α) * ε ^ (2 - α) := by
  have hp : ε ^ (2 : ℕ) * ε ^ (-α) = ε ^ (2 - α) := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε]
    congr 1
  apply (norm_integral_stable_weighted_difference_le hα0 hα2 hε g hg hnear hfar).trans_eq
  calc
    _ = C * ε ^ (2 - α) / (2 - α) + (4 * C) * (ε ^ 2 * ε ^ (-α)) / α := by
      ring
    _ = _ := by rw [hp]; ring

end PartialBalayage.Linear
