/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.NormTruncation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# True L¹ transfer for positive kernel maximal operators

Monotone norm truncations belong to L¹ and L². Monotone convergence identifies the
actual kernel maximal function with the increasing supremum of their maximal functions.
Continuity from below of outer measure then passes the exact weak coefficient to every
integrable input, without measurability of a selected level-set representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PartialBalayage

variable {X T : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The exact weak level estimate passes to a monotone supremum of actual functions. -/
theorem weak_level_bound_iSup_of_monotone (F : ℕ → X → ℝ≥0∞)
    (hF : ∀ x, Monotone (fun k ↦ F k x)) (α Cmass : ℝ≥0∞)
    (hb : ∀ k, α * μ {x | α < F k x} ≤ Cmass) :
    α * μ {x | α < ⨆ k : ℕ, F k x} ≤ Cmass := by
  have hset : {x | α < ⨆ k : ℕ, F k x} = ⋃ k : ℕ, {x | α < F k x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, lt_iSup_iff]
  have hmono : Monotone (fun k : ℕ ↦ {x | α < F k x}) := by
    intro k l hkl x hx
    exact hx.trans_le (hF x hkl)
  rw [hset, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hb

/-- A positive kernel maximal function is the supremum of its genuine L¹ and L² truncations. -/
theorem kernel_maximal_eq_iSup_normTruncation
    (K : T → X → X → ℝ≥0∞) (hK : ∀ t x, AEMeasurable (K t x) μ)
    {f : X → ℝ} (hf : Integrable f μ) (x : X) :
    (⨆ t : T, ∫⁻ y, K t x y * ‖f y‖ₑ ∂μ) =
      ⨆ k : ℕ, ⨆ t : T, ∫⁻ y, K t x y * ‖normTruncation f k y‖ₑ ∂μ := by
  have htime (t : T) : (∫⁻ y, K t x y * ‖f y‖ₑ ∂μ) =
      ⨆ k : ℕ, ∫⁻ y, K t x y * ‖normTruncation f k y‖ₑ ∂μ := by
    calc
      _ = ∫⁻ y, ⨆ k : ℕ, K t x y * ‖normTruncation f k y‖ₑ ∂μ := by
        apply lintegral_congr
        intro y
        rw [← ENNReal.mul_iSup, iSup_enorm_normTruncation]
      _ = _ := lintegral_iSup'
        (fun k ↦ (hK t x).mul
          (aestronglyMeasurable_normTruncation hf.aestronglyMeasurable k).aemeasurable.enorm)
        (Eventually.of_forall fun y k l hkl ↦ by
          apply mul_le_mul_right
          rw [← ofReal_norm, ← ofReal_norm, norm_normTruncation, norm_normTruncation]
          exact ENNReal.ofReal_le_ofReal (monotone_normTruncation f y hkl))
  simp_rw [htime]
  exact iSup_comm

/-- The exact coefficient for L¹ and L² inputs bounds the actual operator on every L¹ input. -/
theorem kernel_maximal_weak_bound_of_L1_L2
    (K : T → X → X → ℝ≥0∞) (hK : ∀ t x, AEMeasurable (K t x) μ) (C : ℝ≥0∞)
    (hb : ∀ f : X → ℝ, Integrable f μ → MemLp f 2 μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ⨆ t : T, ∫⁻ y, K t x y * ‖f y‖ₑ ∂μ} ≤
        C * ∫⁻ y, ‖f y‖ₑ ∂μ) :
    ∀ f : X → ℝ, Integrable f μ → ∀ α : ℝ≥0∞,
      α * μ {x | α < ⨆ t : T, ∫⁻ y, K t x y * ‖f y‖ₑ ∂μ} ≤
        C * ∫⁻ y, ‖f y‖ₑ ∂μ := by
  intro f hf α
  simp_rw [kernel_maximal_eq_iSup_normTruncation K hK hf]
  apply weak_level_bound_iSup_of_monotone
  · intro x k l hkl
    apply iSup_mono
    intro t
    apply lintegral_mono
    intro y
    apply mul_le_mul_right
    rw [← ofReal_norm, ← ofReal_norm, norm_normTruncation, norm_normTruncation]
    exact ENNReal.ofReal_le_ofReal (monotone_normTruncation f y hkl)
  · intro k
    exact (hb (normTruncation f k) (integrable_normTruncation hf k)
      (memLp_normTruncation hf k) α).trans
        (mul_le_mul_right (lintegral_enorm_normTruncation_le f k) C)

end PartialBalayage
