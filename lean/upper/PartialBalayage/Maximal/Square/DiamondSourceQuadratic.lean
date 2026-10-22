/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.DiamondLocalCuspBounds
public import PartialBalayage.Maximal.Square.DiamondCoordinateProfiles
public import PartialBalayage.Maximal.Square.DiamondGeneratorBasic
public import PartialBalayage.Maximal.Square.DiamondStripVolume
public import PartialBalayage.Maximal.Square.KernelSourceIntegrability

/-!
# Actual integrated quadratic cancellation away from the origin

The genuine axis and truncation boundary strips have volume of order the jump length.
Their linear pointwise errors therefore give a true quadratic spatial integral bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem integrable_indicator_const_of_measure_le {s : Set E} {V : ℝ}
    (hs : MeasurableSet s) (hV : volume s ≤ ENNReal.ofReal V) (c : ℝ) :
    Integrable (s.indicator (fun _ : E ↦ c)) volume := by
  apply (integrable_indicator_iff hs).mpr
  exact integrableOn_const (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV)

private theorem integral_indicator_const_le_of_measure_le {s : Set E} {V c : ℝ}
    (hs : MeasurableSet s) (hV : volume s ≤ ENNReal.ofReal V) (hV0 : 0 ≤ V) (hc : 0 ≤ c) :
    (∫ x : E, s.indicator (fun _ : E ↦ c) x) ≤ V * c := by
  rw [integral_indicator_const c hs, smul_eq_mul]
  have hm : volume.real s ≤ V := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hV).trans_eq
      (ENNReal.toReal_ofReal hV0)
  exact mul_le_mul_of_nonneg_right hm hc

private theorem diamond_radius_abs_coordinates (x : E) (i : Fin 2) :
    |x i| + |x (1 - i)| = diamondRadius (x 0) (x 1) := by
  fin_cases i
  · rfl
  · change |x 1| + |x 0| = |x 0| + |x 1|
    ring

private theorem measure_norm_le_ne_top (L : ℝ) :
    volume {x : E | ‖x‖ ≤ L} ≠ ⊤ := by
  have he : {x : E | ‖x‖ ≤ L} = Metric.closedBall (0 : E) L := by
    ext x
    exact mem_closedBall_zero_iff.symm
  rw [he]
  exact (isCompact_closedBall (0 : E) L).measure_ne_top

private theorem diamond_test_secondDifference_point_bound {δ L M t : ℝ} {φ : E → ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M)
    (hs : ∀ x, φ x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ L) (i : Fin 2)
    (ht : 0 ≤ t) (hdt : t ≤ δ / 2) (x : E) :
    ‖φ x * stableSecondDifference
      (coordinateLine (diamondTruncatedPower (47 / 40) supportRadius) x i) t‖ ≤
      {x : E | ‖x‖ ≤ L}.indicator (fun _ ↦ M *
        (2 * (47 / 40 : ℝ) * (negativePowerLipConst (-1 - (47 / 40)) (δ / 2)
          (by norm_num) (by positivity) : ℝ)) * t ^ 2) x +
      {x : E | |x i| < t ∧ ‖x‖ ≤ L}.indicator (fun _ ↦ M *
        (2 * (negativePowerLipConst (-(47 / 40)) (δ / 2)
          (by norm_num) (by positivity) : ℝ)) * t) x +
      {x : E | |supportRadius - diamondRadius (x 0) (x 1)| < t}.indicator (fun _ ↦ M *
        (2 * (negativePowerLipConst (-(47 / 40)) (δ / 2)
          (by norm_num) (by positivity) : ℝ)) * t) x := by
  by_cases hx : φ x = 0
  · simp only [hx, zero_mul, norm_zero]
    unfold Set.indicator
    exact add_nonneg (add_nonneg (by split_ifs <;> positivity)
      (by split_ifs <;> positivity)) (by split_ifs <;> positivity)
  · have hsx := hs x hx
    have hr : δ ≤ |x i| + |x (1 - i)| := by
      rw [diamond_radius_abs_coordinates]
      exact hsx.1.trans (norm_le_diamondRadius x)
    have hp := norm_diamondTruncatedSecondDifference_strips_le
      (by norm_num : (0 : ℝ) < 47 / 40) hδ supportRadius_pos (abs_nonneg (x i)) hr ht hdt
    rw [← coordinateSecondDifference_diamondTruncatedPower,
      diamond_radius_abs_coordinates] at hp
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left hp hM).trans_eq
    simp only [Set.indicator, mem_ofPred_eq, hsx.2, and_true, ite_true]
    split_ifs <;> ring

/-- A bounded actual test supported away from zero has genuine quadratic spatial cancellation. -/
theorem exists_diamond_test_secondDifference_quadratic_bound {δ L M : ℝ} {φ : E → ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hφ : Continuous φ)
    (hb : ∀ x, ‖φ x‖ ≤ M)
    (hs : ∀ x, φ x ≠ 0 → δ ≤ ‖x‖ ∧ ‖x‖ ≤ L) (i : Fin 2) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ t ∈ Ioc 0 ρ,
      (∫ x : E, ‖φ x * stableSecondDifference
        (coordinateLine (diamondTruncatedPower (47 / 40) supportRadius) x i) t‖) ≤ C * t ^ 2 := by
  let B : Set E := {x | ‖x‖ ≤ L}
  let Q : ℝ := 2 * (47 / 40 : ℝ) *
    (negativePowerLipConst (-1 - (47 / 40)) (δ / 2) (by norm_num) (by positivity) : ℝ)
  let P : ℝ := 2 *
    (negativePowerLipConst (-(47 / 40)) (δ / 2) (by norm_num) (by positivity) : ℝ)
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by positivity
  have hR := supportRadius_pos
  have hB : MeasurableSet B := (isClosed_le continuous_norm continuous_const).measurableSet
  have hBfin : volume B ≠ ⊤ := measure_norm_le_ne_top L
  let C : ℝ := M * Q * volume.real B + M * P * (4 * L + 8 * supportRadius)
  refine ⟨min (δ / 2) (supportRadius / 2), C, by positivity, ?_⟩
  intro t ht
  have htpos : 0 < t := ht.1
  have hdt : t ≤ δ / 2 := ht.2.trans (min_le_left _ _)
  have htR : t < supportRadius :=
    (ht.2.trans (min_le_right _ _)).trans_lt (by linarith [supportRadius_pos])
  let A : Set E := {x | |x i| < t ∧ ‖x‖ ≤ L}
  let D : Set E := {x | |supportRadius - diamondRadius (x 0) (x 1)| < t}
  have hA : MeasurableSet A := by
    change MeasurableSet ({x : E | |x i| < t} ∩ B)
    exact ((isOpen_lt (show Continuous (fun x : E ↦ |x i|) by fun_prop)
      continuous_const).measurableSet).inter hB
  have hD : MeasurableSet D := (isOpen_lt (by unfold diamondRadius; fun_prop)
    continuous_const).measurableSet
  have hAv := volume_coordinateStrip_le i hL ht.1.le
  have hDv := volume_diamondBoundaryStrip_le supportRadius_pos ht.1 htR
  have hBi : Integrable (B.indicator (fun _ : E ↦ M * Q * t ^ 2)) :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hBfin)
  have hAi := integrable_indicator_const_of_measure_le hA hAv (M * P * t)
  have hDi := integrable_indicator_const_of_measure_le hD hDv (M * P * t)
  have hi := ((integrable_coordinateSecondDifference_kernel
    integrable_diamondTruncatedPower i t).bdd_mul hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).norm
  have hm := integral_mono hi ((hBi.add hAi).add hDi)
    (diamond_test_secondDifference_point_bound hδ hM hb hs i ht.1.le hdt)
  have he₁ := integral_add (hBi.add hAi) hDi
  have he₂ := integral_add hBi hAi
  simp only [Pi.add_apply] at he₁ he₂ hm
  rw [he₁, he₂, integral_indicator_const _ hB, smul_eq_mul] at hm
  have hAb := integral_indicator_const_le_of_measure_le hA hAv
    (by positivity : 0 ≤ 4 * L * t) (by positivity : 0 ≤ M * P * t)
  have hDb := integral_indicator_const_le_of_measure_le hD hDv
    (by positivity : 0 ≤ 8 * supportRadius * t) (by positivity : 0 ≤ M * P * t)
  apply hm.trans
  change _ ≤ (M * Q * volume.real B + M * P * (4 * L + 8 * supportRadius)) * t ^ 2
  nlinarith

end PartialBalayage.Maximal.Square
