/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.RationalDiamondAverages
public import PartialBalayage.Maximal.KernelWeakBoundTransfer

/-!
# The actual Euclidean diamond maximal operator

The original region averages have both a genuine positive-kernel expression
and the actual nonnegative real integral normalization. True source contact
therefore controls the full maximal function. Monotone norm truncations pass
the exact coefficient from L¹ and L² inputs to every integrable input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine centered diamond maximal function in the Euclidean plane. -/
def euclideanDiamondMaximalFunction (f : E → ℝ) (x : E) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r),
    (volume (closedEuclideanDiamond x r))⁻¹ *
      ∫⁻ y in closedEuclideanDiamond x r, ‖f y‖ₑ

/-- The actual normalized averaging kernel at a positive radius. -/
def euclideanDiamondAveragingKernel (r : {r : ℝ // 0 < r}) (x y : E) : ℝ≥0∞ :=
  (volume (closedEuclideanDiamond x r))⁻¹ *
    (closedEuclideanDiamond x r).indicator (fun _ ↦ (1 : ℝ≥0∞)) y

theorem measurable_euclideanDiamondAveragingKernel (r : {r : ℝ // 0 < r}) (x : E) :
    Measurable (euclideanDiamondAveragingKernel r x) :=
  measurable_const.mul
    (measurable_const.indicator (measurableSet_closedEuclideanDiamond x r))

/-- The genuine positive kernel pairing is exactly the original normalized region average. -/
theorem lintegral_euclideanDiamondAveragingKernel (r : {r : ℝ // 0 < r})
    (f : E → ℝ) (x : E) :
    (∫⁻ y, euclideanDiamondAveragingKernel r x y * ‖f y‖ₑ) =
      (volume (closedEuclideanDiamond x r))⁻¹ *
        ∫⁻ y in closedEuclideanDiamond x r, ‖f y‖ₑ := by
  have hr : 0 < (r : ℝ) := r.property
  have hv : (volume (closedEuclideanDiamond x r))⁻¹ ≠ ∞ := by
    rw [volume_closedEuclideanDiamond x r.property.le]
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  simp only [euclideanDiamondAveragingKernel, mul_assoc]
  rw [lintegral_const_mul' _ _ hv]
  congr 1
  rw [← lintegral_indicator (measurableSet_closedEuclideanDiamond x r)]
  apply lintegral_congr
  intro y
  classical
  simp only [indicator_apply]
  split_ifs <;> simp

/-- The original maximal function is the supremum of the genuine positive kernel pairings. -/
theorem euclideanDiamondMaximalFunction_eq_kernel_iSup (f : E → ℝ) (x : E) :
    euclideanDiamondMaximalFunction f x =
      ⨆ r : {r : ℝ // 0 < r}, ∫⁻ y, euclideanDiamondAveragingKernel r x y * ‖f y‖ₑ := by
  simp_rw [lintegral_euclideanDiamondAveragingKernel]
  unfold euclideanDiamondMaximalFunction
  rw [iSup_subtype]

/-- Actual nonnegative real region averages agree with the original extended-real averages. -/
theorem euclideanDiamondAverage_eq_ofReal {f : E → ℝ} (hf : Integrable f)
    (hf₀ : ∀ᵐ y, 0 ≤ f y) (x : E) {r : ℝ} (hr : 0 < r) :
    (volume (closedEuclideanDiamond x r))⁻¹ *
        (∫⁻ y in closedEuclideanDiamond x r, ‖f y‖ₑ) =
      ENNReal.ofReal ((2 * r ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x r, f y)) := by
  have hi := ofReal_integral_eq_lintegral_ofReal
    (hf.integrableOn (s := closedEuclideanDiamond x r)) (ae_restrict_of_ae hf₀)
  have hn : (∫⁻ y in closedEuclideanDiamond x r, ‖f y‖ₑ) =
      ENNReal.ofReal (∫ y in closedEuclideanDiamond x r, f y) := by
    rw [hi]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hf₀] with y hy
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hy]
  rw [volume_closedEuclideanDiamond x hr.le, hn,
    ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- The genuine source contact comparison bounds the actual all-radius maximal function. -/
theorem ae_euclideanDiamondMaximalFunction_le_half_kernel_mass [KernelMajorizationFacts] (f ν : E → ℝ)
    (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (hν₂ : MemLp ν 2 volume)
    (hf₀ : ∀ᵐ y, 0 ≤ f y) (κ : ℝ) (hcap : ∀ᵐ y, ν y ≤ κ) (P : E → Prop)
    (hcontact : ∀ r : ℝ, 0 < r → ∀ᵐ x, P x → 0 ≤
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y)) :
    ∀ᵐ x, P x → euclideanDiamondMaximalFunction f x ≤
      ENNReal.ofReal (κ * ((∫ y, euclideanKernel y) / 2)) := by
  have hall := ae_all_diamondAverages_le_half_kernel_mass
    f ν hf₁ hf₂ hν₂ hf₀ κ hcap P hcontact
  filter_upwards [hall] with x hx
  intro hP
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  rw [euclideanDiamondAverage_eq_ofReal hf₁ hf₀ x hr]
  exact ENNReal.ofReal_le_ofReal (hx hP r hr)

/-- The exact coefficient for actual L¹ and L² inputs bounds every genuine integrable input. -/
theorem euclideanDiamondMaximalFunction_weak_bound_of_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : E → ℝ, Integrable f → MemLp f 2 volume → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤
        C * ∫⁻ x, ‖f x‖ₑ) :
    ∀ f : E → ℝ, Integrable f → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ := by
  simp_rw [euclideanDiamondMaximalFunction_eq_kernel_iSup] at hb ⊢
  exact kernel_maximal_weak_bound_of_L1_L2 euclideanDiamondAveragingKernel
    (fun r x ↦ (measurable_euclideanDiamondAveragingKernel r x).aemeasurable) C hb

end PartialBalayage.Maximal.Square
