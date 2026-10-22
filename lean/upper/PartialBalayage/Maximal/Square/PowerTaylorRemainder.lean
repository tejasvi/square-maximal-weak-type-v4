/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: power 73/40 instead of 9/5: far-knot error constant 264187/20480000 = (792561/2560000)/24 and exponent -87/40. -/
module

public import PartialBalayage.Maximal.Square.PowerTaylor

/-!
# The exact cubic Taylor remainder bound away from a power singularity

The bound is obtained from the actual fourth derivative and Taylor's theorem with
the genuine Lagrange remainder. It is the analytic estimate used by the rational
rectangle certificate, before any numerical enclosure is substituted.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace PartialBalayage.Maximal.Square

/-- The far-knot error constant `264187/20480000`. -/
theorem abs_rpow_nine_fifths_sub_taylorThree_le {a δ x : ℝ}
    (hδ : 0 ≤ δ) (haδ : δ < a) (hx : |x - a| ≤ δ) :
    |x ^ (73 / 40 : ℝ) - powerTaylorThree a x| ≤
      (264187 / 20480000 : ℝ) * δ ^ (4 : ℕ) * (a - δ) ^ (-87 / 40 : ℝ) := by
  have ha : 0 < a := hδ.trans_lt haδ
  have ham : 0 < a - δ := sub_pos.mpr haδ
  have hxlo : a - δ ≤ x := by linarith [neg_abs_le (x - a)]
  have hxpos : 0 < x := ham.trans_le hxlo
  have hlo : ∀ y ∈ uIcc a x, a - δ ≤ y := by
    intro y hy
    exact (le_min (by linarith) hxlo).trans hy.1
  have hpos : ∀ y ∈ uIcc a x, 0 < y := fun y hy ↦ ham.trans_le (hlo y hy)
  by_cases hax : a = x
  · subst x
    simp only [powerTaylorThree, sub_self, mul_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_pow (by omega : (3 : ℕ) ≠ 0), add_zero, sub_zero, abs_zero]
    positivity
  have hf : ContDiffOn ℝ (3 + 1 : ℕ) (fun t : ℝ ↦ t ^ (73 / 40 : ℝ)) (uIcc a x) :=
    contDiffOn_id.rpow_const_of_ne (fun y hy ↦ (hpos y hy).ne')
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) hax hf
  have hycc : y ∈ uIcc a x := mem_Icc_of_Ioo hy
  rw [taylorWithinEval_rpow_nine_fifths_three (uniqueDiffOn_uIcc hax) ha
      (left_mem_uIcc), iteratedDeriv_four_rpow_nine_fifths (hpos y hycc)] at heq
  rw [heq]
  have hp : y ^ (-87 / 40 : ℝ) ≤ (a - δ) ^ (-87 / 40 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ham (hlo y hycc) (by norm_num)
  have hpow : |x - a| ^ (4 : ℕ) ≤ δ ^ (4 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg (x - a)) hx 4
  have hn : 0 ≤ y ^ (-87 / 40 : ℝ) := Real.rpow_nonneg (hpos y hycc).le _
  calc
    |792561 / 2560000 * y ^ (-87 / 40 : ℝ) * (x - a) ^ (3 + 1) / (Nat.factorial (3 + 1) : ℝ)| =
        (264187 / 20480000 : ℝ) * |x - a| ^ (4 : ℕ) * y ^ (-87 / 40 : ℝ) := by
      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hn]
      norm_num
      ring
    _ ≤ _ := by
      gcongr

end PartialBalayage.Maximal.Square
