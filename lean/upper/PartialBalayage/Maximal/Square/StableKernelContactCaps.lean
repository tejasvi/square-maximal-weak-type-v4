/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5; the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.SourceContactComparison
public import PartialBalayage.Maximal.Square.SquareSourcePrerequisites
public import PartialBalayage.Maximal.Square.DilatedSourceSigmaFinite
public import PartialBalayage.Maximal.Square.JumpWholeSpaceGenerator
public import PartialBalayage.Maximal.Square.KernelMajorization

/-!
# Actual all-radius contact caps from the constructed stable obstacle

The genuine whole-space constructor supplies the state, capped density,
physical compact equation and active-volume bound. The true singular source
comparison applies at every positive radius. The sole remaining geometric
premise here is nonnegativity of the original source density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- The actual constructed state has the true dilated kernel comparison at each radius. -/
theorem ae_dilated_kernel_contact_of_square_source_nonneg [KernelMajorizationFacts]
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x)
    (ν f : L²) (U : StableJumpEnergySpace (47 / 40))
    (hu₁ : Integrable (stableJumpValue (47 / 40) U : E → ℝ))
    (hu₀ : ∀ᵐ x, 0 ≤ stableJumpValue (47 / 40) U x)
    (hpde : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ x, stableJumpValue (47 / 40) U x * coordinateStableGenerator (47 / 40) φ x) =
        ∫ x, (ν x - f x) * φ x)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x, stableJumpValue (47 / 40) U x = 0 → 0 ≤
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y) := by
  let μ := dilatedSourceMeasure (47 / 40) r squareSourceMeasure
  let : SigmaFinite μ := sigmaFinite_dilatedSourceMeasure (47 / 40) hr squareSourceMeasure
  have hlocal : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      0 ∉ tsupport φ → Integrable φ μ := by
    intro φ hφ hs hz
    exact integrable_dilatedSourceMeasure_test
      (fun _ hc hsupport hzero ↦ integrable_compact_test_squareSourceMeasure hc hsupport hzero)
      (47 / 40) hr hφ hs hz
  have haway : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      0 ∉ tsupport φ →
      (∫ x, dilatedComparisonKernel r euclideanKernel x *
        coordinateStableGenerator (47 / 40) φ x) = ∫ x, φ x ∂μ := by
    intro φ hφ hs hz
    exact integral_dilatedComparisonKernel_generator_eq_source
      (fun _ hc hsupport hzero ↦
        integral_kernel_generator_eq_squareSourceMeasure_of_nonneg hpositive hc hsupport hzero)
      hr hφ hs hz
  have hpde' : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ x, stableJumpValue (47 / 40) U x * coordinateStableGenerator (47 / 40) φ x) =
        ∫ x, (ν - f) x * φ x := by
    intro φ hφ hs
    rw [hpde φ hφ hs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ν f] with x hx
    simp only [hx, Pi.sub_apply]
  have h := ae_kernel_convolution_nonneg_on_stable_contact (α := 47 / 40)
    (by norm_num) (by norm_num)
    (integrable_dilatedComparisonKernel integrable_euclideanKernel hr)
    (Eventually.of_forall (fun x ↦ euclideanKernel_nonneg (r⁻¹ • x)))
    (dilatedComparisonKernel_even euclideanKernel_neg r) μ hlocal haway
    (stableJumpValue (47 / 40) U) (ν - f) hu₁ hu₀ hpde'
  filter_upwards [h] with x hx
  intro hz
  have he : (∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν - f) y) =
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ν f] with y hy
    simp only [hy, Pi.sub_apply]
  simpa only [he] using hx hz

/-- Genuine positive L¹ and L² input has actual all-radius kernel caps and active-volume control. -/
theorem exists_stable_kernel_contact_caps_Lp_of_square_source_nonneg [KernelMajorizationFacts]
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x)
    (f : L²) (hf₁ : Integrable (f : E → ℝ)) (hf₀ : ∀ᵐ y, 0 ≤ f y)
    (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : E → ℝ) (s : Set E), MemLp ν 2 volume ∧ (∀ᵐ y, ν y ≤ (κ : ℝ)) ∧
      ((κ : ℝ≥0∞) * volume s ≤ ∫⁻ y, ‖f y‖ₑ) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x, x ∉ s → 0 ≤
        ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y) := by
  obtain ⟨ν, U, hν, _, _, _, hU, hU₁, hpde, _, hactive, _⟩ :=
    exists_positive_stableJump_generator_obstacle (α := 47 / 40)
      (by norm_num) (by norm_num) κ hκ f hf₁ hf₀
  refine ⟨ν, stableJumpActiveSet (47 / 40) U, Lp.memLp ν, hν.mono (fun _ h ↦ h.2),
    hactive, fun r hr ↦ ?_⟩
  have h := ae_dilated_kernel_contact_of_square_source_nonneg hpositive ν f U hU₁ hU hpde hr
  filter_upwards [h] with x hx
  intro hnot
  apply hx
  simpa only [stableJumpActiveSet, mem_ofPred_eq, not_not] using hnot

/-- The actual contact caps apply to every nonnegative genuine L¹ and L² representative. -/
theorem exists_stable_kernel_contact_caps_of_square_source_nonneg [KernelMajorizationFacts]
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x)
    (f : E → ℝ) (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (hf₀ : ∀ᵐ y, 0 ≤ f y)
    (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : E → ℝ) (s : Set E), MemLp ν 2 volume ∧ (∀ᵐ y, ν y ≤ (κ : ℝ)) ∧
      ((κ : ℝ≥0∞) * volume s ≤ ∫⁻ y, ‖f y‖ₑ) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x, x ∉ s → 0 ≤
        ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y) := by
  let F := hf₂.toLp f
  have hF : (F : E → ℝ) =ᵐ[volume] f := hf₂.coeFn_toLp
  have hF₁ : Integrable (F : E → ℝ) := hf₁.congr hF.symm
  have hF₀ : ∀ᵐ y, 0 ≤ F y := by
    filter_upwards [hF, hf₀] with y hy hpos
    rwa [hy]
  obtain ⟨ν, s, hν, hcap, hvolume, hcontact⟩ :=
    exists_stable_kernel_contact_caps_Lp_of_square_source_nonneg hpositive F hF₁ hF₀ κ hκ
  have hm : (∫⁻ y, ‖F y‖ₑ) = ∫⁻ y, ‖f y‖ₑ :=
    lintegral_congr_ae (hF.mono (fun y h ↦ by
      change ‖F y‖ₑ = ‖f y‖ₑ
      rw [h]))
  rw [hm] at hvolume
  refine ⟨ν, s, hν, hcap, hvolume, fun r hr ↦ ?_⟩
  filter_upwards [hcontact r hr] with x hx
  intro hs
  have he : (∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - F y)) =
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y) :=
    integral_congr_ae (hF.mono (fun _ h ↦ by dsimp only; rw [h]))
  simpa only [he] using hx hs

end PartialBalayage.Maximal.Square
