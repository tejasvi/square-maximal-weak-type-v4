/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5; spline scale 32 instead of 16. -/
module

public import PartialBalayage.Maximal.Square.RadialPuncturedSource
public import PartialBalayage.Maximal.Square.TensorSplineGenerator

/-!
# Genuine punctured source of the complete square kernel

The original radial and finite tensor-spline sources combine as an actual measurable
even density. Its compact away-origin pairing is genuinely integrable, and equals the
original kernel's normalized coordinate generator against the same test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual signed radial-plus-spline source density before its geometric positivity proof. -/
def squareGeneratorDensity (x : E) : ℝ := radialGeneratorDensity x +
  coordinateStableGenerator (47 / 40) (fun y : E ↦ splineCorrection (y 0) (y 1)) x

/-- The concrete physical-space density has the exact correction used in the certificate. -/
theorem squareGeneratorDensity_eq_formula (x : E) :
    squareGeneratorDensity x = radialGeneratorDensity x +
      stableNormalization (47 / 40) * splineGeneratorFactor *
        splineGeneratorCorrectionPower (32 * x 0) (32 * x 1) := by
  unfold squareGeneratorDensity
  rw [coordinateStableGenerator_splineCorrection]

theorem stronglyMeasurable_squareGeneratorDensity :
    StronglyMeasurable squareGeneratorDensity :=
  stronglyMeasurable_radialGeneratorDensity.add
    (stronglyMeasurable_coordinateStableGenerator (47 / 40) continuous_splineCorrection)

/-- Reflection preserves the original radial and actual correction generators. -/
theorem squareGeneratorDensity_neg (x : E) :
    squareGeneratorDensity (-x) = squareGeneratorDensity x := by
  unfold squareGeneratorDensity
  rw [radialGeneratorDensity_neg, ← coordinateStableGenerator_reflect]
  have he : (fun y : E ↦ splineCorrection ((-y) 0) ((-y) 1)) =
      fun y ↦ splineCorrection (y 0) (y 1) := by
    funext y
    simp only [PiLp.neg_apply, splineCorrection_neg_left, splineCorrection_neg_right]
  rw [he]

/-- Every actual compact C² away-origin test pairs absolutely integrably with the full density. -/
theorem integrable_compact_test_mul_squareGeneratorDensity {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    Integrable (fun x : E ↦ φ x * squareGeneratorDensity x) := by
  have hr := integrable_compact_test_mul_radialGeneratorDensity hφ hs hzero
  have hg := integrable_compact_test_mul_splineGeneratorCorrection hφ hs
  apply (hr.add hg).congr
  filter_upwards with x
  simp only [Pi.add_apply, squareGeneratorDensity_eq_formula, mul_add]

/-- The complete original kernel has its actual punctured distributional source density. -/
theorem integral_euclideanKernel_coordinateStableGenerator {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    (∫ x : E, euclideanKernel x * coordinateStableGenerator (47 / 40) φ x) =
      ∫ x : E, φ x * squareGeneratorDensity x := by
  have hr := integrable_kernel_mul_coordinateStableGenerator_compactC2
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num) integrable_radialBase hφ hs
  have hg := integrable_kernel_mul_coordinateStableGenerator_compactC2
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num) integrable_splineCorrection hφ hs
  have hsr := integrable_compact_test_mul_radialGeneratorDensity hφ hs hzero
  have hsg := integrable_compact_test_mul_splineGeneratorCorrection hφ hs
  have he₁ := integral_add hr hg
  have he₂ := integral_add hsr hsg
  calc
    _ = ∫ x : E, radialBase (x 0) (x 1) * coordinateStableGenerator (47 / 40) φ x +
        splineCorrection (x 0) (x 1) * coordinateStableGenerator (47 / 40) φ x := by
      apply integral_congr_ae
      filter_upwards [euclideanKernel_ae_eq] with x hx
      rw [hx]
      ring
    _ = _ := he₁
    _ = (∫ x : E, φ x * radialGeneratorDensity x) +
        ∫ x : E, φ x * (stableNormalization (47 / 40) * splineGeneratorFactor *
          splineGeneratorCorrectionPower (32 * x 0) (32 * x 1)) := by
      rw [integral_radialBase_coordinateStableGenerator hφ hs hzero,
        integral_splineCorrection_coordinateStableGenerator hφ hs]
    _ = _ := by
      rw [← he₂]
      apply integral_congr_ae
      filter_upwards with x
      rw [squareGeneratorDensity_eq_formula, mul_add]

end PartialBalayage.Maximal.Square
