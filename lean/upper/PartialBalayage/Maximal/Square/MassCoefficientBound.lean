/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: our kernel's mass: R^(33/40) is enclosed by 40th powers, the spline mass is
coefficientSum/1024, and the target is our 359123/100000 instead of 452/125. -/
module

public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Exact rational bound for the square mass coefficient

A rational 40th-power inequality encloses the true radius to the power 33/40.
Together with the actual signed coefficient sum it puts the exact
half-mass expression strictly below the rational value 359123/100000.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- A kernel-checked rational enclosure for the actual support-radius power. -/
theorem supportRadius_rpow_33_40_le :
    supportRadius ^ (33 / 40 : ℝ) ≤ 377889010841 / 250000000000 := by
  have he : IsPowerEnclosureDeg 40 (33 / 20) 33 0 (377889010841 / 250000000000) := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
    decide +kernel
  have hp := (he.rpow_bounds (by norm_num) (by norm_num)).2
  have hc : ((33 : ℤ) : ℝ) / ((40 : ℕ) : ℝ) = 33 / 40 := by norm_num
  rw [hc] at hp
  simpa only [supportRadius, Rat.cast_div, Rat.cast_ofNat] using hp

/-- The true half-mass formula is strictly less than our certificate's bound. -/
theorem half_mass_coefficient_lt :
    (94 / 33 * radialCoefficient * supportRadius ^ (33 / 40 : ℝ) +
      (coefficientSum : ℝ) / 1024) / 2 < 359123 / 100000 := by
  calc
    _ ≤ (94 / 33 * radialCoefficient * (377889010841 / 250000000000) +
        (coefficientSum : ℝ) / 1024) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left supportRadius_rpow_33_40_le
        (mul_nonneg (by norm_num) radialCoefficient_pos.le)) le_rfl
    _ < _ := by rw [coefficientSum_eq]; norm_num [radialCoefficient]

end PartialBalayage.Maximal.Square
