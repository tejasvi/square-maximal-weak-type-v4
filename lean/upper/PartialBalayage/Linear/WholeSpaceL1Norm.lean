/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.L1NormFunctional
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# The full vector norm integral on sigma-finite spaces

Restricting an actual `L²` function to finite spanning sets gives continuous linear maps into
`L¹`. Their norms are convex and weakly lower semicontinuous. The supremum is exactly the
possibly infinite integral of the full vector norm, so that integral is weakly lower
semicontinuous without any scalar positivity assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure X} [SigmaFinite μ]

/-- The genuine `L²` restriction to a finite spanning set, followed by its `L¹` inclusion. -/
def spanningL1CLM (i : ℕ) : Lp E 2 μ →L[ℝ] Lp E 1 (μ.restrict (spanningSets μ i)) := by
  letI : Fact (μ (spanningSets μ i) < ∞) := ⟨measure_spanningSets_lt_top μ i⟩
  exact l2ToL1CLM.comp (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self (μ := μ) (s := spanningSets μ i))))

theorem coeFn_spanningL1CLM (i : ℕ) (f : Lp E 2 μ) :
    spanningL1CLM i f =ᵐ[μ.restrict (spanningSets μ i)] f := by
  have : Fact (μ (spanningSets μ i) < ∞) := ⟨measure_spanningSets_lt_top μ i⟩
  exact (coeFn_l2ToL1 _).trans (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f)

theorem ofReal_norm_spanningL1CLM (i : ℕ) (f : Lp E 2 μ) :
    ENNReal.ofReal ‖spanningL1CLM i f‖ = ∫⁻ x in spanningSets μ i, ‖f x‖ₑ ∂μ := by
  rw [ofReal_norm, Lp.enorm_def,
    eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _)]
  exact lintegral_congr_ae ((coeFn_spanningL1CLM i f).fun_comp enorm)

theorem lowerSemicontinuous_norm_spanningL1CLM_weak (i : ℕ) :
    LowerSemicontinuous (fun f : WeakSpace ℝ (Lp E 2 μ) =>
      ‖spanningL1CLM i ((toWeakSpace ℝ (Lp E 2 μ)).symm f)‖) := by
  have hc : ConvexOn ℝ univ (fun f : Lp E 2 μ => ‖spanningL1CLM i f‖) := by
    have h := (convexOn_norm (E := Lp E 1 (μ.restrict (spanningSets μ i)))
      convex_univ).comp_linearMap (spanningL1CLM (E := E) i).toLinearMap
    convert! h using 1
  exact hc.lowerSemicontinuous_comp_toWeakSpace_symm
    ((spanningL1CLM i).continuous.norm.lowerSemicontinuous)

/-- Exhaustion recovers the actual full vector norm integral, including infinite values. -/
theorem iSup_norm_spanningL1CLM (f : Lp E 2 μ) :
    (⨆ i, ENNReal.ofReal ‖spanningL1CLM i f‖) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [ofReal_norm_spanningL1CLM]
  rw [← setLIntegral_iUnion_of_directed _ (monotone_spanningSets μ).directed_le,
    iUnion_spanningSets, Measure.restrict_univ]

/-- The full vector norm integral is weakly lower semicontinuous on the whole `L²` space. -/
theorem lowerSemicontinuous_lintegral_norm_weak :
    LowerSemicontinuous (fun f : WeakSpace ℝ (Lp E 2 μ) =>
      ∫⁻ x, ‖((toWeakSpace ℝ (Lp E 2 μ)).symm f) x‖ₑ ∂μ) := by
  simp_rw [← iSup_norm_spanningL1CLM]
  exact lowerSemicontinuous_iSup fun i =>
    ENNReal.continuous_ofReal.comp_lowerSemicontinuous
      (lowerSemicontinuous_norm_spanningL1CLM_weak i)
      (fun _ _ h => ENNReal.ofReal_le_ofReal h)

/-- A whole-space vector mass bound is closed for the weak `L²` topology. -/
theorem isClosed_lintegral_norm_sublevel_weak (mass : ℝ≥0∞) :
    IsClosed {f : WeakSpace ℝ (Lp E 2 μ) |
      ∫⁻ x, ‖((toWeakSpace ℝ (Lp E 2 μ)).symm f) x‖ₑ ∂μ ≤ mass} :=
  lowerSemicontinuous_lintegral_norm_weak.isClosed_preimage mass

end PartialBalayage.Linear
