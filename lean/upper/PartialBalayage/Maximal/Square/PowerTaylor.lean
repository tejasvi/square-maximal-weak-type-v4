/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: power 73/40 (= 3 - alpha at alpha = 47/40) instead of 9/5: Taylor coefficients 73/40, 2409/3200, -5621/128000 and fourth derivative 792561/2560000 x^(-87/40). -/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorScaling
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Genuine Taylor coefficients for the certificate's fractional power

The formulas are derivatives of the actual real power function on the positive half-line.
The cubic Taylor polynomial and fourth derivative are identified before any rational
enclosure or rectangle arithmetic is applied.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PartialBalayage.Maximal.Square

/-- All actual iterated derivatives of a real power at a strictly positive point. -/
theorem iteratedDeriv_real_rpow (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun t : ℝ ↦ t ^ p) x =
      (∏ k ∈ Finset.range n, (p - (k : ℝ))) * x ^ (p - (n : ℝ)) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, Finset.range_zero, Finset.prod_empty,
      Nat.cast_zero, sub_zero, one_mul]
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ ↦ t ^ p) =ᶠ[𝓝 x]
        fun t : ℝ ↦ (∏ k ∈ Finset.range n, (p - (k : ℝ))) * t ^ (p - (n : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := p - (n : ℝ))
      (Or.inl hx.ne')).const_mul (∏ k ∈ Finset.range n, (p - (k : ℝ)))
    rw [hd.deriv, Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : p - (n : ℝ) - 1 = p - ((n : ℝ) + 1) := by ring
    rw [hp]
    ring

/-- The actual cubic Taylor polynomial at a positive center. -/
def powerTaylorThree (a x : ℝ) : ℝ :=
  a ^ (73 / 40 : ℝ) + (73 / 40 : ℝ) * a ^ (33 / 40 : ℝ) * (x - a) +
    (2409 / 3200 : ℝ) * a ^ (-7 / 40 : ℝ) * (x - a) ^ (2 : ℕ) -
      (5621 / 128000 : ℝ) * a ^ (-47 / 40 : ℝ) * (x - a) ^ (3 : ℕ)

theorem taylorWithinEval_rpow_nine_fifths_three {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) {a : ℝ} (ha : 0 < a) (has : a ∈ s) (x : ℝ) :
    taylorWithinEval (fun t : ℝ ↦ t ^ (73 / 40 : ℝ)) 3 s a x = powerTaylorThree a x := by
  have hcd : ContDiffAt ℝ ω (fun t : ℝ ↦ t ^ (73 / 40 : ℝ)) a :=
    contDiffAt_id.rpow_const_of_ne ha.ne'
  have hi (n : ℕ) : iteratedDerivWithin n (fun t : ℝ ↦ t ^ (73 / 40 : ℝ)) s a =
      (∏ k ∈ Finset.range n, ((73 / 40 : ℝ) - (k : ℝ))) *
        a ^ ((73 / 40 : ℝ) - (n : ℝ)) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hcd.of_le le_top) has,
      iteratedDeriv_real_rpow (73 / 40) n ha]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hi]
  norm_num [Finset.prod_range_succ, powerTaylorThree, Nat.factorial, smul_eq_mul]
  ring

theorem iteratedDeriv_four_rpow_nine_fifths {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 (fun t : ℝ ↦ t ^ (73 / 40 : ℝ)) x =
      (792561 / 2560000 : ℝ) * x ^ (-87 / 40 : ℝ) := by
  rw [iteratedDeriv_real_rpow (73 / 40) 4 hx]
  norm_num [Finset.prod_range_succ]

end PartialBalayage.Maximal.Square
