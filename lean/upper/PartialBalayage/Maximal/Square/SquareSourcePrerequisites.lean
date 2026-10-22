/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.SquareSourceMeasure
public import PartialBalayage.Maximal.Square.SourceMomentIntegrability

/-!
# Actual square source prerequisites from density positivity

The concrete positive measure is reflection invariant independently of the density's
geometric positivity. Once the actual signed density is nonnegative almost everywhere,
its genuine punctured pairing gives the finite jump moment and full compensated source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Reflection invariance holds for the actual positive-part source measure. -/
theorem map_neg_squareSourceMeasure :
    Measure.map (fun x : E ↦ -x) squareSourceMeasure = squareSourceMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs, squareSourceMeasure,
    withDensity_apply _ (hs.preimage measurable_neg), withDensity_apply _ hs]
  have he := (Measure.measurePreserving_neg (volume : Measure E)).setLIntegral_comp_preimage
    hs measurable_squareSourceDensity
  simpa only [squareGeneratorDensity_neg] using he

theorem measurePreserving_neg_squareSourceMeasure :
    MeasurePreserving (fun x : E ↦ -x) squareSourceMeasure squareSourceMeasure :=
  ⟨measurable_neg, map_neg_squareSourceMeasure⟩

/-- Nonnegativity identifies the fixed measure with the actual signed density. -/
theorem integral_squareSourceMeasure_eq_density_of_nonneg
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x) (φ : E → ℝ) :
    (∫ x, φ x ∂squareSourceMeasure) = ∫ x : E, φ x * squareGeneratorDensity x := by
  rw [integral_squareSourceMeasure]
  apply integral_congr_ae
  filter_upwards [hpositive] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

/-- This source pairing has only the explicit, genuine density positivity premise. -/
theorem integral_kernel_generator_eq_squareSourceMeasure_of_nonneg
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    (∫ x : E, euclideanKernel x * coordinateStableGenerator (47 / 40) φ x) =
      ∫ x, φ x ∂squareSourceMeasure := by
  rw [integral_squareSourceMeasure_eq_density_of_nonneg hpositive]
  exact integral_euclideanKernel_coordinateStableGenerator hφ hs hzero

/-- The full jump moment is derived from the actual punctured source, not a mass assumption. -/
theorem integrable_squareSourceMeasure_jumpMoment_of_nonneg
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x) :
    Integrable compensatedJumpMoment squareSourceMeasure :=
  integrable_compensatedJumpMoment_of_punctured_source (by norm_num) (by norm_num)
    integrable_euclideanKernel squareSourceMeasure
    (fun _ hφ hs hzero ↦ integrable_compact_test_squareSourceMeasure hφ hs hzero)
    (fun _ hφ hs hzero ↦
      integral_kernel_generator_eq_squareSourceMeasure_of_nonneg hpositive hφ hs hzero)

/-- The concrete source has the full compensated identity after genuine density positivity. -/
theorem integral_kernel_generator_eq_squareCompensatedSource_of_nonneg
    (hpositive : ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x : E, euclideanKernel x * coordinateStableGenerator (47 / 40) φ x) =
      compensatedSymmetricSource squareSourceMeasure φ :=
  integral_kernel_generator_eq_compensatedSymmetricSource_of_punctured_source
    (by norm_num) (by norm_num) integrable_euclideanKernel euclideanKernel_neg squareSourceMeasure
    (fun _ hc hsupport hzero ↦ integrable_compact_test_squareSourceMeasure hc hsupport hzero)
    (fun _ hc hsupport hzero ↦
      integral_kernel_generator_eq_squareSourceMeasure_of_nonneg hpositive hc hsupport hzero) hφ hs

end PartialBalayage.Maximal.Square
