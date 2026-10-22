/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.EuclideanDiamondMaximal
public import PartialBalayage.Maximal.Square.KernelMassPositivity
public import PartialBalayage.Maximal.CappedMaximalLevelSet

/-!
# The exact level-set step for actual diamond contact caps

At each positive finite level, the true density cap is the level divided by
the genuine half-kernel mass. The actual contact averages and active-volume
cap give the original maximal level-set estimate. Zero and infinite levels
are included in the same conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- True all-radius contact caps and active-volume bounds give the exact original level bound. -/
theorem euclideanDiamondMaximalFunction_levelSet_bound_of_contact_caps [KernelMajorizationFacts] (f : E → ℝ)
    (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (hf₀ : ∀ᵐ y, 0 ≤ f y)
    (hdecomp : ∀ κ : ℝ≥0, 0 < κ → ∃ (ν : E → ℝ) (s : Set E),
      MemLp ν 2 volume ∧ (∀ᵐ y, ν y ≤ (κ : ℝ)) ∧
      ((κ : ℝ≥0∞) * volume s ≤ ∫⁻ y, ‖f y‖ₑ) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x, x ∉ s → 0 ≤
        ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y))
    (α : ℝ≥0∞) :
    α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤
      ENNReal.ofReal ((∫ y, euclideanKernel y) / 2) * ∫⁻ y, ‖f y‖ₑ := by
  by_cases hα₀ : α = 0
  · simp only [hα₀, zero_mul, zero_le]
  by_cases hαtop : α = ⊤
  · simp only [hαtop, not_top_lt, ofPred_false, measure_empty, mul_zero, zero_le]
  have hαeq : (α.toNNReal : ℝ≥0∞) = α := ENNReal.coe_toNNReal hαtop
  have ht : 0 < α.toNNReal := by
    apply pos_iff_ne_zero.mpr
    intro hz
    apply hα₀
    rw [← hαeq, hz, ENNReal.coe_zero]
  let B : ℝ≥0 := ⟨(∫ y, euclideanKernel y) / 2, half_integral_euclideanKernel_pos.le⟩
  have hB : 0 < B := by exact_mod_cast half_integral_euclideanKernel_pos
  let κ : ℝ≥0 := α.toNNReal / B
  have hκ : 0 < κ := div_pos ht hB
  obtain ⟨ν, s, hν₂, hcap, hvolume, hcontact⟩ := hdecomp κ hκ
  have hoff := ae_euclideanDiamondMaximalFunction_le_half_kernel_mass
    f ν hf₁ hf₂ hν₂ hf₀ (κ : ℝ) hcap (fun x ↦ x ∉ s) hcontact
  have hκB : (κ : ℝ) * ((∫ y, euclideanKernel y) / 2) = (α.toNNReal : ℝ) := by
    change ((α.toNNReal : ℝ) / (B : ℝ)) * (B : ℝ) = (α.toNNReal : ℝ)
    exact div_mul_cancel₀ _ (by exact_mod_cast hB.ne')
  have hoff' : ∀ᵐ x, x ∉ s →
      euclideanDiamondMaximalFunction f x ≤ (α.toNNReal : ℝ≥0∞) := by
    simpa only [hκB, ENNReal.ofReal_coe_nnreal] using hoff
  have h := maximal_levelSet_bound_of_cap_quotient hB hoff' hvolume
  have hBcoe : (B : ℝ≥0∞) = ENNReal.ofReal ((∫ y, euclideanKernel y) / 2) :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hBcoe, hαeq] at h
  exact h

end PartialBalayage.Maximal.Square
