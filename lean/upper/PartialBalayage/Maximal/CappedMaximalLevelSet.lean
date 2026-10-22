/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# The level-set step of positive partial balayage

An actual comparison outside a capped active set bounds the maximal-function level set by
that active set. This outer-measure step requires no measurability of a chosen function
representative. The analytic kernel comparison and actual active-volume cap are supplied
by the concrete obstacle construction.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The true off-active comparison and active-volume cap give the maximal level-set bound. -/
theorem maximal_levelSet_bound_of_off_active {F : X → ℝ≥0∞} {s : Set X}
    {κ B mass : ℝ≥0∞}
    (hoff : ∀ᵐ x ∂μ, x ∉ s → F x ≤ κ * B) (hcap : κ * μ s ≤ mass) :
    (κ * B) * μ {x | κ * B < F x} ≤ B * mass := by
  have hm : μ {x | κ * B < F x} ≤ μ s := by
    apply measure_mono_ae
    filter_upwards [hoff] with x hx
    intro hlevel
    by_contra hnot
    exact (not_lt_of_ge (hx hnot)) hlevel
  calc
    (κ * B) * μ {x | κ * B < F x} ≤ (κ * B) * μ s := mul_le_mul_right hm _
    _ = B * (κ * μ s) := by ac_rfl
    _ ≤ B * mass := mul_le_mul_right hcap _

/-- Choosing the true cap as level divided by kernel mass yields the exact weak coefficient. -/
theorem maximal_levelSet_bound_of_cap_quotient {F : X → ℝ≥0∞} {s : Set X}
    {t B : ℝ≥0} (hB : 0 < B) {mass : ℝ≥0∞}
    (hoff : ∀ᵐ x ∂μ, x ∉ s → F x ≤ (t : ℝ≥0∞))
    (hcap : ((t / B : ℝ≥0) : ℝ≥0∞) * μ s ≤ mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < F x} ≤ (B : ℝ≥0∞) * mass := by
  have hprod : ((t / B : ℝ≥0) : ℝ≥0∞) * (B : ℝ≥0∞) = (t : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul, div_mul_cancel₀ t hB.ne']
  have h := maximal_levelSet_bound_of_off_active
    (κ := ((t / B : ℝ≥0) : ℝ≥0∞)) (B := (B : ℝ≥0∞))
      (by simpa only [hprod] using hoff) hcap
  simpa only [hprod] using h

end PartialBalayage
