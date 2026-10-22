/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: spline spacing 1/32 instead of 1/16 (each tensor has mass 1/1024). -/
module

public import PartialBalayage.Maximal.Square.Integrability
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The exact signed mass of the actual spline correction

Every actual tensor spline has mass one over 1024. Integration over all real
coordinate signs and orbit multiplicities gives the exact signed coefficient
sum, including the negative correction in the article's candidate kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin 2 → ℝ

/-- The actual affine coordinate spline is integrable. -/
theorem integrable_scaled_cubicSpline (a : ℝ) :
    Integrable (fun t : ℝ ↦ cubicSpline (32 * t - a)) :=
  (integrable_cubicSpline.comp_sub_right a).comp_mul_left' (by norm_num)

/-- The actual affine coordinate spline has exact mass one thirty-second. -/
theorem integral_scaled_cubicSpline (a : ℝ) :
    (∫ t : ℝ, cubicSpline (32 * t - a)) = 1 / 32 := by
  rw [Measure.integral_comp_mul_left (fun t ↦ cubicSpline (t - a)) 32,
    integral_sub_right_eq_self, integral_cubicSpline]
  norm_num

private theorem integrable_tensor_pi (a b : ℝ) :
    Integrable (fun x : P ↦ cubicSpline (32 * x 0 - a) * cubicSpline (32 * x 1 - b)) := by
  have hp := (integrable_scaled_cubicSpline a).mul_prod (integrable_scaled_cubicSpline b)
  exact ((volume_preserving_finTwoArrow ℝ).integrable_comp
    hp.aestronglyMeasurable).mpr hp

/-- Each actual translated tensor is integrable in the original Euclidean volume. -/
theorem integrable_tensorSpline (a b : ℝ) :
    Integrable (fun x : E ↦ cubicSpline (32 * x 0 - a) * cubicSpline (32 * x 1 - b)) :=
  ((PiLp.volume_preserving_ofLp (Fin 2)).integrable_comp
    (integrable_tensor_pi a b).aestronglyMeasurable).mpr (integrable_tensor_pi a b)

/-- Each actual translated tensor has exact mass one over 1024. -/
theorem integral_tensorSpline (a b : ℝ) :
    (∫ x : E, cubicSpline (32 * x 0 - a) * cubicSpline (32 * x 1 - b)) = 1 / 1024 := by
  have he := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp'
    (fun x : P ↦ cubicSpline (32 * x 0 - a) * cubicSpline (32 * x 1 - b))
  simp only [MeasurableEquiv.toLp_symm_apply] at he
  rw [he]
  have hp := (volume_preserving_finTwoArrow ℝ).integral_comp'
    (fun x : ℝ × ℝ ↦ cubicSpline (32 * x.1 - a) * cubicSpline (32 * x.2 - b))
  change (∫ x : P, cubicSpline (32 * x 0 - a) * cubicSpline (32 * x 1 - b)) = _ at hp
  rw [hp]
  change (∫ y : ℝ × ℝ, cubicSpline (32 * y.1 - a) * cubicSpline (32 * y.2 - b)
    ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_mul (μ := (volume : Measure ℝ)) (ν := volume)
      (fun t : ℝ ↦ cubicSpline (32 * t - a)) (fun t : ℝ ↦ cubicSpline (32 * t - b)),
    integral_scaled_cubicSpline, integral_scaled_cubicSpline]
  norm_num

/-- Every genuine finite orbit is integrable. -/
theorem integrable_orbitSpline (i j : ℕ) : Integrable (fun x : E ↦ orbitSpline i j (x 0) (x 1)) :=
  integrable_finsetSum _ (fun p _ ↦ integrable_tensorSpline (p.1 : ℝ) (p.2 : ℝ))

/-- An actual orbit contributes its true cardinality divided by 1024. -/
theorem integral_orbitSpline (i j : ℕ) :
    (∫ x : E, orbitSpline i j (x 0) (x 1)) = (splineOrbit i j).card / 1024 := by
  unfold orbitSpline
  rw [integral_finsetSum _ (fun p _ ↦ integrable_tensorSpline _ _)]
  simp only [integral_tensorSpline, Finset.sum_const, nsmul_eq_mul]
  ring

private theorem integrable_orbitList (L : List (ℕ × ℕ × ℚ)) :
    Integrable (fun x : E ↦
      (L.map (fun t ↦ (t.2.2 : ℝ) * orbitSpline t.1 t.2.1 (x 0) (x 1))).sum) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply] using
      ((integrable_orbitSpline t.1 t.2.1).const_mul (t.2.2 : ℝ)).fun_add ih

private theorem integral_orbitList (L : List (ℕ × ℕ × ℚ)) :
    (∫ x : E,
      (L.map (fun t ↦ (t.2.2 : ℝ) * orbitSpline t.1 t.2.1 (x 0) (x 1))).sum) =
      (L.map (fun t ↦ ((splineOrbit t.1 t.2.1).card : ℝ) * (t.2.2 : ℝ))).sum / 1024 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add ((integrable_orbitSpline t.1 t.2.1).const_mul _) (integrable_orbitList L),
      integral_const_mul, integral_orbitSpline, ih]
    ring

/-- The original signed spline correction has the exact coefficient mass. -/
theorem integral_splineCorrection :
    (∫ x : E, splineCorrection (x 0) (x 1)) = (coefficientSum : ℝ) / 1024 := by
  unfold splineCorrection
  rw [integral_orbitList]
  congr 1
  unfold coefficientSum
  induction splineOrbits with
  | nil => simp
  | cons t L ih => simpa only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast] using congrArg (fun r : ℝ ↦ (splineOrbit t.1 t.2.1).card *
        (t.2.2 : ℝ) + r) ih

end PartialBalayage.Maximal.Square
