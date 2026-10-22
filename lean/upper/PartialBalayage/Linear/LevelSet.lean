/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Level-set estimates from a capped decomposition

These supporting estimates assume concrete decomposition data: an active set, equality of two
functions outside that set, a cap on its measure, and an `L²` energy bound for the reduced function.
They prove the elementary measure-theoretic step of the article's first principle. Construction
of such decomposition data for the actual operators is a separate mathematical requirement.

The estimates hold for outer measures of level sets, so no measurability assumption on the original
function is necessary. The active set is measurable and the reduced function's `eLpNorm` is the
standard Mathlib `L²` seminorm.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable {μ : Measure X} {F G : X → E} {s : Set X}

/-- Equality off the active set reduces the original level set to that set and a level set of
the reduced function. -/
theorem measure_norm_gt_le_of_ae_eq_off (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → F x = G x) (t : ℝ≥0∞) :
    μ {x | t < ‖F x‖ₑ} ≤ μ s + μ {x | t ≤ ‖G x‖ₑ} := by
  rw [← measure_inter_add_sdiff {x | t < ‖F x‖ₑ} hs]
  refine add_le_add (measure_mono inter_subset_right) (measure_mono_ae ?_)
  filter_upwards [heq] with x hx
  intro hxlevel
  simpa only [hx hxlevel.2] using (show t < ‖F x‖ₑ from hxlevel.1).le

/-- Chebyshev's inequality and the two caps give the parameter-dependent weak estimate. -/
theorem levelSet_bound_of_capped_decomposition (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → F x = G x)
    {t κ M : ℝ≥0} (ht : 0 < t) (hκ : 0 < κ) {mass : ℝ≥0∞}
    (hcap : (κ : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm G 2 μ ^ (2 : ℕ) ≤ (M : ℝ≥0∞) ^ (2 : ℕ) * κ * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖F x‖ₑ} ≤
      ((t / κ + M ^ (2 : ℕ) * κ / t : ℝ≥0) : ℝ≥0∞) * mass := by
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ.ne'
  have hcheb : (t : ℝ≥0∞) ^ (2 : ℕ) * μ {x | (t : ℝ≥0∞) ≤ ‖G x‖ₑ} ≤
      eLpNorm G 2 μ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      mul_meas_ge_le_pow_eLpNorm' μ (p := 2) (f := G)
        (by norm_num) (by norm_num) (t : ℝ≥0∞)
  have hset := measure_norm_gt_le_of_ae_eq_off hs heq (t : ℝ≥0∞)
  have hcap' : (t : ℝ≥0∞) * μ s ≤ (t : ℝ≥0∞) / κ * mass := by
    calc
      (t : ℝ≥0∞) * μ s = (t : ℝ≥0∞) / κ * ((κ : ℝ≥0∞) * μ s) := by
        simp only [div_eq_mul_inv, mul_assoc,
          ENNReal.inv_mul_cancel_left hκ0 ENNReal.coe_ne_top]
      _ ≤ (t : ℝ≥0∞) / κ * mass := mul_le_mul_right hcap _
  have hcheb' : (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ ‖G x‖ₑ} ≤
      ((M : ℝ≥0∞) ^ (2 : ℕ) * κ / t) * mass := by
    calc
      (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ ‖G x‖ₑ} =
          (t : ℝ≥0∞)⁻¹ * ((t : ℝ≥0∞) ^ (2 : ℕ) *
            μ {x | (t : ℝ≥0∞) ≤ ‖G x‖ₑ}) := by
        simp only [pow_two, mul_assoc, ENNReal.inv_mul_cancel_left ht0 ENNReal.coe_ne_top]
      _ ≤ (t : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) ^ (2 : ℕ) * κ * mass) :=
        mul_le_mul_right (hcheb.trans henergy) _
      _ = ((M : ℝ≥0∞) ^ (2 : ℕ) * κ / t) * mass := by
        simp only [div_eq_mul_inv]
        ac_rfl
  calc
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖F x‖ₑ}
        ≤ (t : ℝ≥0∞) * μ s + (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) ≤ ‖G x‖ₑ} := by
          simpa only [mul_add] using mul_le_mul_right hset (t : ℝ≥0∞)
    _ ≤ (t : ℝ≥0∞) / κ * mass + ((M : ℝ≥0∞) ^ (2 : ℕ) * κ / t) * mass := by
      exact add_le_add hcap' hcheb'
    _ = ((t / κ + M ^ (2 : ℕ) * κ / t : ℝ≥0) : ℝ≥0∞) * mass := by
      rw [ENNReal.coe_add, ENNReal.coe_div hκ.ne', ENNReal.coe_div ht.ne',
        ENNReal.coe_mul, ENNReal.coe_pow, add_mul]

/-- Choosing the cap `κ = t / M` in genuine decomposition data gives the coefficient `2M`. -/
theorem levelSet_bound_two_mul_of_capped_decomposition (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂μ, x ∉ s → F x = G x)
    {t M : ℝ≥0} (ht : 0 < t) (hM : 0 < M) {mass : ℝ≥0∞}
    (hcap : ((t / M : ℝ≥0) : ℝ≥0∞) * μ s ≤ mass)
    (henergy : eLpNorm G 2 μ ^ (2 : ℕ) ≤
      (M : ℝ≥0∞) ^ (2 : ℕ) * (t / M : ℝ≥0) * mass) :
    (t : ℝ≥0∞) * μ {x | (t : ℝ≥0∞) < ‖F x‖ₑ} ≤
      (2 : ℝ≥0∞) * M * mass := by
  have h := levelSet_bound_of_capped_decomposition hs heq ht (div_pos ht hM) hcap henergy
  have hconstant : t / (t / M) + M ^ (2 : ℕ) * (t / M) / t = 2 * M := by
    field_simp
    norm_num
  simpa only [hconstant, ENNReal.coe_mul, ENNReal.coe_ofNat] using h

end PartialBalayage.Linear
