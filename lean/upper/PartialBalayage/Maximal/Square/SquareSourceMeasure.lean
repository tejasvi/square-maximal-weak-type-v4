/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.KernelPuncturedSource
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The concrete positive measure from the actual square source density

This fixed measure has the positive part of the genuine radial-plus-spline density. It
is sigma finite, and every compact C² away-origin test is actually integrable against it.
The identification with the full generator additionally uses the density positivity proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The concrete positive candidate source measure, with no finite total-mass requirement. -/
def squareSourceMeasure : Measure E :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (squareGeneratorDensity x))

instance sigmaFinite_squareSourceMeasure : SigmaFinite squareSourceMeasure :=
  SigmaFinite.withDensity_ofReal squareGeneratorDensity

theorem measurable_squareSourceDensity :
    Measurable (fun x : E ↦ ENNReal.ofReal (squareGeneratorDensity x)) :=
  stronglyMeasurable_squareGeneratorDensity.measurable.ennreal_ofReal

private theorem norm_positivePart_source_mul_le (φ : E → ℝ) (x : E) :
    ‖(ENNReal.ofReal (squareGeneratorDensity x)).toReal • φ x‖ ≤
      ‖φ x * squareGeneratorDensity x‖ := by
  by_cases hg : 0 ≤ squareGeneratorDensity x
  · rw [ENNReal.toReal_ofReal hg, smul_eq_mul, mul_comm]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hg), ENNReal.toReal_zero,
      zero_smul, norm_zero]
    exact norm_nonneg _

/-- The actual source-side local integrability holds before using any positivity certificate. -/
theorem integrable_compact_test_squareSourceMeasure {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    Integrable φ squareSourceMeasure := by
  unfold squareSourceMeasure
  apply (integrable_withDensity_iff_integrable_smul' measurable_squareSourceDensity
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mpr
  have hm : AEStronglyMeasurable (fun x : E ↦
      (ENNReal.ofReal (squareGeneratorDensity x)).toReal • φ x) volume := by
    apply Measurable.aestronglyMeasurable
    have hg := stronglyMeasurable_squareGeneratorDensity.measurable
    have hc := hφ.continuous.measurable
    fun_prop
  exact (integrable_compact_test_mul_squareGeneratorDensity hφ hs hzero).norm.mono'
    hm (Filter.Eventually.of_forall (norm_positivePart_source_mul_le φ))

/-- The integral against the concrete measure is the actual positive-part density integral. -/
theorem integral_squareSourceMeasure (φ : E → ℝ) :
    (∫ x, φ x ∂squareSourceMeasure) =
      ∫ x : E, (ENNReal.ofReal (squareGeneratorDensity x)).toReal • φ x :=
  integral_withDensity_eq_integral_toReal_smul measurable_squareSourceDensity
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) φ

end PartialBalayage.Maximal.Square
