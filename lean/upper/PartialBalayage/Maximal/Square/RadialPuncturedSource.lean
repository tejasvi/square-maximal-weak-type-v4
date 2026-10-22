/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.DiamondPuncturedSource
public import PartialBalayage.Maximal.Square.GeneratorAlgebra

/-!
# Actual source density of the scaled radial base

The density is the original normalized physical generator. Its exact interior formula,
evenness, almost everywhere positivity, and genuine punctured pairing are established.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine punctured density of the original scaled radial kernel. -/
def radialGeneratorDensity (x : E) : ℝ := radialCoefficient *
  coordinateStableGenerator (47 / 40) (diamondTruncatedPower (47 / 40) supportRadius) x

theorem coordinateStableGenerator_radialBase (x : E) :
    coordinateStableGenerator (47 / 40) (fun y : E ↦ radialBase (y 0) (y 1)) x =
      radialGeneratorDensity x := by
  have he : (fun y : E ↦ radialBase (y 0) (y 1)) =
      fun y ↦ radialCoefficient * diamondTruncatedPower (47 / 40) supportRadius y := rfl
  rw [he, coordinateStableGenerator_const_mul]
  rfl

theorem stronglyMeasurable_radialGeneratorDensity :
    StronglyMeasurable radialGeneratorDensity :=
  (stronglyMeasurable_coordinateStableGenerator_of_measurable (47 / 40)
    (measurable_diamondTruncatedPower _ _)).const_mul _

theorem ae_radialGeneratorDensity_nonneg : ∀ᵐ x : E ∂volume, 0 ≤ radialGeneratorDensity x := by
  filter_upwards [ae_coordinateStableGenerator_diamondTruncatedPower_nonneg] with x hx
  exact mul_nonneg radialCoefficient_pos.le hx

theorem radialGeneratorDensity_eq_interior (x : E) (hx₀ : x 0 ≠ 0) (hx₁ : x 1 ≠ 0)
    (hr : diamondRadius (x 0) (x 1) < supportRadius) :
    radialGeneratorDensity x = radialCoefficient * diamondInteriorSourceModel x := by
  unfold radialGeneratorDensity
  rw [coordinateStableGenerator_diamondTruncatedPower_eq_interior x hx₀ hx₁ hr]

theorem diamondTruncatedPower_neg (α R : ℝ) (x : E) :
    diamondTruncatedPower α R (-x) = diamondTruncatedPower α R x := by
  simp only [diamondTruncatedPower, diamondPower, diamondRadius, PiLp.neg_apply, abs_neg]

/-- Reflection of the true coordinate generator preserves the even radial density. -/
theorem radialGeneratorDensity_neg (x : E) :
    radialGeneratorDensity (-x) = radialGeneratorDensity x := by
  unfold radialGeneratorDensity
  rw [← coordinateStableGenerator_reflect]
  have he : (fun y : E ↦ diamondTruncatedPower (47 / 40) supportRadius (-y)) =
      diamondTruncatedPower (47 / 40) supportRadius := by
    funext y
    exact diamondTruncatedPower_neg _ _ y
  rw [he]

/-- The genuine scaled radial density is locally integrable against each actual away-origin test. -/
theorem integrable_compact_test_mul_radialGeneratorDensity {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    Integrable (fun x : E ↦ φ x * radialGeneratorDensity x) := by
  have hi := (integrable_compact_test_mul_diamondGenerator hφ hs hzero).const_mul
    radialCoefficient
  apply hi.congr
  filter_upwards with x
  unfold radialGeneratorDensity
  ring

/-- The original scaled radial base has this actual punctured distributional source. -/
theorem integral_radialBase_coordinateStableGenerator {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (hzero : (0 : E) ∉ tsupport φ) :
    (∫ x : E, radialBase (x 0) (x 1) * coordinateStableGenerator (47 / 40) φ x) =
      ∫ x : E, φ x * radialGeneratorDensity x := by
  have he : (fun x : E ↦ radialBase (x 0) (x 1) * coordinateStableGenerator (47 / 40) φ x) =
      fun x ↦ radialCoefficient * (diamondTruncatedPower (47 / 40) supportRadius x *
        coordinateStableGenerator (47 / 40) φ x) := by
    funext x
    rw [radialBase_eq_coefficient_diamondTruncatedPower]
    ring
  have he' : (fun x : E ↦ φ x * radialGeneratorDensity x) =
      fun x ↦ radialCoefficient * (φ x * coordinateStableGenerator (47 / 40)
        (diamondTruncatedPower (47 / 40) supportRadius) x) := by
    funext x
    unfold radialGeneratorDensity
    ring
  rw [he, he', integral_const_mul, integral_const_mul,
    integral_diamondTruncatedPower_coordinateStableGenerator hφ hs hzero]

end PartialBalayage.Maximal.Square
