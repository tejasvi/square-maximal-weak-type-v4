/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.DiamondGeneratorModel
public import PartialBalayage.Maximal.Square.Integrability

/-!
# Measurability and positivity of the actual diamond source

The original singular diamond kernel is genuinely integrable. Its actual normalized
coordinate generator is measurable and nonnegative almost everywhere for planar volume.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem measurable_diamondTruncatedPower (α R : ℝ) :
    Measurable (diamondTruncatedPower α R) := by
  unfold diamondTruncatedPower diamondPower diamondRadius
  fun_prop

theorem integrable_diamondTruncatedPower :
    Integrable (diamondTruncatedPower (47 / 40) supportRadius) volume := by
  have he : (fun x : E ↦ radialBase (x 0) (x 1)) =
      fun x ↦ radialCoefficient * diamondTruncatedPower (47 / 40) supportRadius x := rfl
  have hi := integrable_radialBase
  rw [he] at hi
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr radialCoefficient_pos.ne') _).mp hi

/-- A measurable singular kernel still has a genuinely measurable actual generator. -/
theorem stronglyMeasurable_coordinateStableGenerator_of_measurable (α : ℝ) {K : E → ℝ}
    (hK : Measurable K) : StronglyMeasurable (coordinateStableGenerator α K) := by
  have hi (i : Fin 2) : StronglyMeasurable
      (fun x ↦ stableGeneratorIntegral α (coordinateLine K x i)) := by
    have hm : Measurable (fun p : E × ℝ ↦ p.2 ^ (-1 - α) •
        stableSecondDifference (coordinateLine K p.1 i) p.2) := by
      unfold stableSecondDifference coordinateLine
      fun_prop
    exact hm.stronglyMeasurable.integral_prod_right'
  unfold coordinateStableGenerator
  simp only [Fin.sum_univ_two]
  exact ((hi 0).add (hi 1)).const_mul _

theorem ae_euclidean_coordinate_ne_zero (i : Fin 2) :
    ∀ᵐ x : E ∂volume, x i ≠ 0 := by
  have hp := PiLp.volume_preserving_ofLp (ι := Fin 2)
  have ha : ∀ᵐ x : Fin 2 → ℝ ∂volume, x i ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 ↦ (volume : Measure ℝ)) i 0
  have hm : MeasurableSet {x : Fin 2 → ℝ | x i ≠ 0} :=
    (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl
  rw [← hp.map_eq, ae_map_iff hp.measurable.aemeasurable hm] at ha
  exact ha

/-- Axis values have planar measure zero, so the actual source is nonnegative almost everywhere. -/
theorem ae_coordinateStableGenerator_diamondTruncatedPower_nonneg :
    ∀ᵐ x : E ∂volume,
      0 ≤ coordinateStableGenerator (47 / 40) (diamondTruncatedPower (47 / 40) supportRadius) x := by
  filter_upwards [ae_euclidean_coordinate_ne_zero 0, ae_euclidean_coordinate_ne_zero 1]
    with x hx₀ hx₁
  exact coordinateStableGenerator_diamondTruncatedPower_nonneg x hx₀ hx₁

end PartialBalayage.Maximal.Square
