/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Genuine monotone L¹ and L² truncations

Clipping the input norm at `k + 1` gives a nonnegative L¹ and L² input on arbitrary
ambient measure. Its square is dominated by `(k + 1) * ‖f‖`. The actual truncations
increase pointwise to the original input norm and retain its L¹ mass bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace PartialBalayage

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Actual nonnegative clipping of the input norm, with no spatial support assumption. -/
def normTruncation (f : X → ℝ) (k : ℕ) (x : X) : ℝ := min ‖f x‖ (k + 1 : ℝ)

omit [MeasurableSpace X] in
theorem normTruncation_nonneg (f : X → ℝ) (k : ℕ) (x : X) :
    0 ≤ normTruncation f k x := le_min (norm_nonneg _) (by positivity)

omit [MeasurableSpace X] in
theorem normTruncation_le_norm (f : X → ℝ) (k : ℕ) (x : X) :
    normTruncation f k x ≤ ‖f x‖ := min_le_left _ _

omit [MeasurableSpace X] in
theorem norm_normTruncation (f : X → ℝ) (k : ℕ) (x : X) :
    ‖normTruncation f k x‖ = normTruncation f k x :=
  Real.norm_of_nonneg (normTruncation_nonneg f k x)

omit [MeasurableSpace X] in
theorem monotone_normTruncation (f : X → ℝ) (x : X) :
    Monotone (fun k ↦ normTruncation f k x) := by
  intro k l hkl
  exact min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hkl 1)

theorem aestronglyMeasurable_normTruncation {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (k : ℕ) :
    AEStronglyMeasurable (normTruncation f k) μ :=
  (hf.norm.aemeasurable.min aemeasurable_const).aestronglyMeasurable

theorem integrable_normTruncation {f : X → ℝ} (hf : Integrable f μ) (k : ℕ) :
    Integrable (normTruncation f k) μ := by
  apply hf.norm.mono' (aestronglyMeasurable_normTruncation hf.aestronglyMeasurable k)
  exact Eventually.of_forall fun x ↦ by
    rw [norm_normTruncation]
    exact normTruncation_le_norm f k x

/-- Every actual clipped norm belongs to L², even on infinite ambient measure. -/
theorem memLp_normTruncation {f : X → ℝ} (hf : Integrable f μ) (k : ℕ) :
    MemLp (normTruncation f k) 2 μ := by
  have hm := aestronglyMeasurable_normTruncation hf.aestronglyMeasurable k
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hf.norm.const_mul (k + 1 : ℝ)).mono' (hm.pow 2)
  exact Eventually.of_forall fun x ↦ by
    change ‖normTruncation f k x ^ 2‖ ≤ (k + 1 : ℝ) * ‖f x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := normTruncation_nonneg f k x
    have h1 := normTruncation_le_norm f k x
    have h2 : normTruncation f k x ≤ (k + 1 : ℝ) := min_le_right _ _
    nlinarith [norm_nonneg (f x)]

omit [MeasurableSpace X] in
theorem enorm_normTruncation_le (f : X → ℝ) (k : ℕ) (x : X) :
    ‖normTruncation f k x‖ₑ ≤ ‖f x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_normTruncation]
  exact ENNReal.ofReal_le_ofReal (normTruncation_le_norm f k x)

omit [MeasurableSpace X] in
/-- The genuine clipped inputs increase to the original norm at every spatial point. -/
theorem iSup_enorm_normTruncation (f : X → ℝ) (x : X) :
    (⨆ k : ℕ, ‖normTruncation f k x‖ₑ) = ‖f x‖ₑ := by
  apply le_antisymm (iSup_le fun k ↦ enorm_normTruncation_le f k x)
  obtain ⟨k, hk⟩ := exists_nat_gt ‖f x‖
  have hle : ‖f x‖ ≤ (k + 1 : ℝ) := by linarith
  have heq : normTruncation f k x = ‖f x‖ := min_eq_left hle
  calc
    _ = ‖normTruncation f k x‖ₑ := by rw [heq]; simp only [enorm_norm]
    _ ≤ _ := le_iSup (fun j : ℕ ↦ ‖normTruncation f j x‖ₑ) k

theorem lintegral_enorm_normTruncation_le (f : X → ℝ) (k : ℕ) :
    (∫⁻ x, ‖normTruncation f k x‖ₑ ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ∂μ :=
  lintegral_mono (enorm_normTruncation_le f k)

end PartialBalayage
