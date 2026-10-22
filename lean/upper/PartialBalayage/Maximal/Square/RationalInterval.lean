/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Sound exact rational interval operations for the generator certificate

Every endpoint operation is rational arithmetic. The soundness theorems connect these
ordinary kernel-checkable operations to the actual real quantities being enclosed.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- Exact rational endpoints; existence of a contained real value enforces their ordering. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

namespace RationalInterval

/-- The actual real quantity lies between the rational endpoints. -/
def Contains (I : RationalInterval) (x : ℝ) : Prop := (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

/-- An exact rational singleton. -/
def point (q : ℚ) : RationalInterval := ⟨q, q⟩

/-- Exact interval addition. -/
def add (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

/-- Exact scalar multiplication with the necessary reversal for a negative scalar. -/
def scale (q : ℚ) (I : RationalInterval) : RationalInterval :=
  if 0 ≤ q then ⟨q * I.lower, q * I.upper⟩ else ⟨q * I.upper, q * I.lower⟩

/-- Exact multiplication when the first interval is nonnegative. -/
def nonnegMul (I J : RationalInterval) : RationalInterval :=
  ⟨if 0 ≤ J.lower then I.lower * J.lower else I.upper * J.lower,
    if 0 ≤ J.upper then I.upper * J.upper else I.lower * J.upper⟩

/-- The exact absolute endpoint bound. -/
def absBound (I : RationalInterval) : ℚ := max |I.lower| |I.upper|

theorem point_contains (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem Contains.add {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  change ((I.lower + J.lower : ℚ) : ℝ) ≤ x + y ∧
    x + y ≤ ((I.upper + J.upper : ℚ) : ℝ)
  simp only [Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem Contains.scale {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (q : ℚ) : (I.scale q).Contains ((q : ℝ) * x) := by
  unfold RationalInterval.scale
  split_ifs with hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    simp only [Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hq', mul_le_mul_of_nonneg_left hx.2 hq'⟩
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
    simp only [Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hq', mul_le_mul_of_nonpos_left hx.1 hq'⟩

theorem Contains.nonnegMul {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (hI : 0 ≤ I.lower) :
    (I.nonnegMul J).Contains (x * y) := by
  have hI' : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI
  have hx₀ : 0 ≤ x := hI'.trans hx.1
  constructor
  · change ((if 0 ≤ J.lower then I.lower * J.lower else I.upper * J.lower : ℚ) : ℝ) ≤ _
    split_ifs with hJ
    · have hJ' : (0 : ℝ) ≤ J.lower := by exact_mod_cast hJ
      rw [Rat.cast_mul]
      exact (mul_le_mul_of_nonneg_right hx.1 hJ').trans
        (mul_le_mul_of_nonneg_left hy.1 hx₀)
    · have hJ' : (J.lower : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hJ)
      rw [Rat.cast_mul]
      exact (mul_le_mul_of_nonpos_right hx.2 hJ').trans
        (mul_le_mul_of_nonneg_left hy.1 hx₀)
  · change _ ≤ ((if 0 ≤ J.upper then I.upper * J.upper else I.lower * J.upper : ℚ) : ℝ)
    split_ifs with hJ
    · have hJ' : (0 : ℝ) ≤ J.upper := by exact_mod_cast hJ
      rw [Rat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hy.2 hx₀).trans
        (mul_le_mul_of_nonneg_right hx.2 hJ')
    · have hJ' : (J.upper : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hJ)
      rw [Rat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hy.2 hx₀).trans
        (mul_le_mul_of_nonpos_right hx.1 hJ')

theorem Contains.abs_le {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.absBound : ℝ) := by
  have hl : (-(I.absBound : ℝ)) ≤ (I.lower : ℝ) := by
    calc
      _ ≤ -|(I.lower : ℝ)| := by
        apply neg_le_neg
        exact_mod_cast (le_max_left |I.lower| |I.upper|)
      _ ≤ _ := neg_abs_le _
  have hu : (I.upper : ℝ) ≤ (I.absBound : ℝ) := by
    calc
      _ ≤ |(I.upper : ℝ)| := le_abs_self _
      _ ≤ _ := by exact_mod_cast (le_max_right |I.lower| |I.upper|)
  exact _root_.abs_le.mpr ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem absBound_nonneg (I : RationalInterval) : 0 ≤ I.absBound :=
  (abs_nonneg I.lower).trans (le_max_left _ _)

end RationalInterval

end PartialBalayage.Maximal.Square
