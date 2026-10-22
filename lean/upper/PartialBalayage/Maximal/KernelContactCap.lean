/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SobolevKernelSourceBound

/-!
# Actual convolution caps at zero contact

The true source pairing comparison, density cap, and kernel majorization give a
convolution bound by the full majorant mass. Almost everywhere convolution existence
comes from the genuine nonnegative L¹-kernel L² Young estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Convolution

namespace PartialBalayage

variable {n : ℕ}

/-- The actual source comparison and density cap bound convolution by the true kernel mass. -/
theorem ae_kernel_source_pairing_le_cap
    (K₀ K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK₀ : Integrable K₀) (hK₀0 : ∀ᵐ y, 0 ≤ K₀ y)
    (hK : Integrable K) (hK0 : ∀ᵐ y, 0 ≤ K y)
    (hmajor : ∀ᵐ y, K₀ y ≤ K y)
    (f ν : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume) (hf0 : ∀ᵐ y, 0 ≤ f y)
    (κ : ℝ) (hcap : ∀ᵐ y, ν y ≤ κ) (P : EuclideanSpace ℝ (Fin n) → Prop)
    (hcontact : ∀ᵐ x, P x → 0 ≤ ∫ y, K (y - x) * (ν y - f y)) :
    ∀ᵐ x, P x → (∫ y, K₀ (y - x) * f y) ≤ κ * ∫ y, K y := by
  filter_upwards [ae_integrable_kernel_source_pairing hK₀ hK₀0 hf,
    ae_integrable_kernel_source_pairing hK hK0 hf,
    ae_integrable_kernel_source_pairing hK hK0 hν, hcontact]
    with x h₀ hfint hνint hx
  intro hP
  have hKx : ∀ᵐ y, 0 ≤ K (y - x) :=
    (measurePreserving_sub_right volume x).quasiMeasurePreserving.tendsto_ae.eventually hK0
  have hmajorx : ∀ᵐ y, K₀ (y - x) ≤ K (y - x) :=
    (measurePreserving_sub_right volume x).quasiMeasurePreserving.tendsto_ae.eventually hmajor
  have hνbound : (∫ y, K (y - x) * ν y) ≤ κ * ∫ y, K y := by
    calc
      _ ≤ ∫ y, K (y - x) * κ := by
        apply integral_mono_ae hνint ((hK.comp_sub_right x).mul_const κ)
        filter_upwards [hKx, hcap] with y hy hcy
        exact mul_le_mul_of_nonneg_left hcy hy
      _ = _ := by rw [integral_mul_const, integral_sub_right_eq_self]; ring
  have hdiff : (∫ y, K (y - x) * (ν y - f y)) =
      (∫ y, K (y - x) * ν y) - ∫ y, K (y - x) * f y := by
    simp_rw [mul_sub]
    exact integral_sub hνint hfint
  have hcontactx := hx hP
  rw [hdiff] at hcontactx
  calc
    _ ≤ ∫ y, K (y - x) * f y := by
      apply integral_mono_ae h₀ hfint
      filter_upwards [hmajorx, hf0] with y hy hfy
      exact mul_le_mul_of_nonneg_right hy hfy
    _ ≤ ∫ y, K (y - x) * ν y := sub_nonneg.mp hcontactx
    _ ≤ _ := hνbound

end PartialBalayage
