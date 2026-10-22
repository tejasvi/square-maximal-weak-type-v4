/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: power 73/40 instead of 9/5; 40th-power enclosures (IsPowerEnclosureDeg 40, numerators 73, 33, -87); error constants 33/40 and 264187/20480000. -/
module

public import PartialBalayage.Maximal.Square.TaylorIntervalEnclosure
public import PartialBalayage.Maximal.Square.SplineTaylorSum

/-!
# Sound literal Taylor data for the generator rectangles

The validity predicate contains only exact rational ordering and 40th-power
checks. Its soundness connects the proposed coefficient intervals and error
bound to the genuine absolute power throughout the stated closed interval.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Literal power enclosures for one actual absolute-power Taylor approximation. -/
structure GeneratorPowerTaylorData where
  center : ℚ
  radius : ℚ
  boundary : Bool
  powers : Fin 4 → RationalInterval
  errorPower : RationalInterval

namespace GeneratorPowerTaylorData

/-- Ordinary exact rational checks needed by this actual approximation. -/
def IsValid (D : GeneratorPowerTaylorData) : Prop :=
  0 ≤ D.radius ∧ D.center ≠ 0 ∧
    if D.boundary then
      D.radius = |D.center| ∧
        IsPowerEnclosureDeg 40 |D.center| 73 (D.powers 0).lower (D.powers 0).upper ∧
        IsPowerEnclosureDeg 40 |D.center| 33 (D.powers 1).lower (D.powers 1).upper
    else
      D.radius < |D.center| ∧
        (∀ i, IsPowerEnclosureDeg 40 |D.center| (absPowerTaylorExponents i)
          (D.powers i).lower (D.powers i).upper) ∧
        IsPowerEnclosureDeg 40 (|D.center| - D.radius) (-87) D.errorPower.lower D.errorPower.upper

instance (D : GeneratorPowerTaylorData) : Decidable D.IsValid := by
  unfold IsValid IsPowerEnclosureDeg
  infer_instance

/-- Proposed exact coefficient intervals, including the linear boundary approximation. -/
def intervals (D : GeneratorPowerTaylorData) : Fin 4 → RationalInterval :=
  if D.boundary then
    ![D.powers 0, (D.powers 1).scale ((73 / 40) * rationalCenterSign D.center),
      RationalInterval.point 0, RationalInterval.point 0]
  else absPowerTaylorIntervals D.center D.powers

/-- The genuine real coefficients of the same absolute-power approximation. -/
def coefficients (D : GeneratorPowerTaylorData) : Fin 4 → ℝ :=
  if D.boundary then
    ![|(D.center : ℝ)| ^ (73 / 40 : ℝ),
      (73 / 40 : ℝ) * powerCenterSign (D.center : ℝ) * |(D.center : ℝ)| ^ (33 / 40 : ℝ), 0, 0]
  else absPowerTaylorCoefficients (D.center : ℝ)

/-- The exact rational error bound obtained from the ordinary 40th-power checks. -/
def error (D : GeneratorPowerTaylorData) : ℚ :=
  if D.boundary then (33 / 40) * (D.powers 0).upper
  else (264187 / 20480000) * D.radius ^ (4 : ℕ) * D.errorPower.upper

/-- The data's actual approximation polynomial at an actual real point. -/
def polynomial (D : GeneratorPowerTaylorData) (x : ℝ) : ℝ :=
  centeredCubic D.coefficients (x - (D.center : ℝ))

/-- Exact rational validity encloses every genuine Taylor coefficient. -/
theorem intervals_contains {D : GeneratorPowerTaylorData} (hD : D.IsValid) :
    ∀ i, (D.intervals i).Contains (D.coefficients i) := by
  by_cases hb : D.boundary = true
  · have h := hD.2.2
    simp only [hb, ↓reduceIte] at h
    have h₀ : (D.powers 0).Contains (|(D.center : ℝ)| ^ (73 / 40 : ℝ)) := by
      have hp := h.2.1.rpow_bounds (by norm_num) (abs_nonneg D.center)
      simpa only [RationalInterval.Contains, Rat.cast_abs, Int.cast_ofNat, Nat.cast_ofNat] using hp
    have h₁ : (D.powers 1).Contains (|(D.center : ℝ)| ^ (33 / 40 : ℝ)) := by
      have hp := h.2.2.rpow_bounds (by norm_num) (abs_nonneg D.center)
      simpa only [RationalInterval.Contains, Rat.cast_abs, Int.cast_ofNat, Nat.cast_ofNat] using hp
    intro i
    fin_cases i
    · simpa [intervals, coefficients, hb] using h₀
    · have hp := h₁.scale ((73 / 40) * rationalCenterSign D.center)
      simpa [intervals, coefficients, hb, rationalCenterSign_cast] using hp
    · simpa [intervals, coefficients, hb] using RationalInterval.point_contains 0
    · simpa [intervals, coefficients, hb] using RationalInterval.point_contains 0
  · have h := hD.2.2
    simp only [hb] at h
    simpa [intervals, coefficients, hb] using
      absPowerTaylorIntervals_contains D.center D.powers h.2.1

/-- The actual polynomial agrees with the proved approximation in both knot regimes. -/
theorem polynomial_eq (D : GeneratorPowerTaylorData) (x : ℝ) :
    D.polynomial x = if D.boundary then absPowerTaylorOne (D.center : ℝ) x
      else absPowerTaylorThree (D.center : ℝ) x := by
  by_cases hb : D.boundary = true
  · simp only [polynomial, coefficients, hb, ↓reduceIte]
    norm_num [centeredCubic, Fin.sum_univ_succ, absPowerTaylorOne]
  · simp only [polynomial, coefficients, hb, centeredCubic]
    exact absPowerTaylorCoefficients_eval _ _

/-- Exact rational validity gives the true approximation error on the whole closed interval. -/
theorem error_bound {D : GeneratorPowerTaylorData} (hD : D.IsValid) {x : ℝ}
    (hx : |x - (D.center : ℝ)| ≤ (D.radius : ℝ)) :
    |(|x| ^ (73 / 40 : ℝ) - D.polynomial x)| ≤ (D.error : ℝ) := by
  rw [D.polynomial_eq]
  by_cases hb : D.boundary = true
  · have h := hD.2.2
    simp only [hb, ↓reduceIte] at h
    simp only [error, hb, ↓reduceIte]
    have hx' : |x - (D.center : ℝ)| ≤ |(D.center : ℝ)| := by
      simpa only [h.1, Rat.cast_abs] using hx
    exact absPowerTaylorOne_error_le_rational hD.2.1 hx' (D.powers 0) h.2.1
  · have h := hD.2.2
    simp only [hb] at h
    simp only [error, hb]
    exact absPowerTaylorThree_error_le_rational hD.1 h.1 hx D.errorPower h.2.2

/-- A valid error enclosure is nonnegative by its proved error at the center. -/
theorem error_nonneg {D : GeneratorPowerTaylorData} (hD : D.IsValid) : 0 ≤ D.error := by
  have hδ : (0 : ℝ) ≤ (D.radius : ℝ) := by exact_mod_cast hD.1
  have he := D.error_bound hD (x := (D.center : ℝ)) (by simpa using hδ)
  exact_mod_cast (abs_nonneg _).trans he

end GeneratorPowerTaylorData

end PartialBalayage.Maximal.Square
