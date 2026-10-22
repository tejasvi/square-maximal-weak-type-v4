/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: at order 47/40 the intrinsic constant is the positive-beta combination 2 (87/7 B(33/40,47/20) - 1404/329 B(33/40,33/40)), bounded below from the kernel-checked beta bounds. -/
module

public import PartialBalayage.Maximal.Square.BetaBound
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A genuine lower bound for the square's intrinsic fractional constant

The intrinsic constant is the exact combination of two convergent positive beta
integrals produced by the diagonal integral. Kernel-checked rational bounds for the
two actual beta integrals give the rational constant used by the generator arithmetic.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual intrinsic constant at order forty-seven fortieths. -/
def squareIntrinsicConstant : ℝ :=
  2 * ((87 / 7 : ℝ) * realBetaIntegral (33 / 40) (47 / 20) -
    (1404 / 329 : ℝ) * realBetaIntegral (33 / 40) (33 / 40))

/-- The actual intrinsic constant exceeds an exact rational lower estimate. -/
theorem squareIntrinsic_lower : (2119593029863 / 1000000000000 : ℝ) ≤ squareIntrinsicConstant := by
  have h₁ := realBetaIntegral_33_40_47_20_ge
  have h₂ := realBetaIntegral_33_40_33_40_le
  unfold squareIntrinsicConstant
  linarith

/-- The shorter rational lower estimate used by the generator arithmetic. -/
theorem squareIntrinsicConstant_ge : (2119593029 / 1000000000 : ℝ) ≤ squareIntrinsicConstant :=
  le_trans (by norm_num) squareIntrinsic_lower

/-- The exact intrinsic constant is strictly positive. -/
theorem squareIntrinsicConstant_pos : 0 < squareIntrinsicConstant :=
  lt_of_lt_of_le (by norm_num) squareIntrinsic_lower

end PartialBalayage.Maximal.Square
