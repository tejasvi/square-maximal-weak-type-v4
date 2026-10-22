/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the fifth-root coefficients are replaced by the rational binomial coefficients of (1-t)^p for any rational p, with one-sided truncation bounds when the tail has one sign. -/
module

public import PartialBalayage.Maximal.Square.PowerEnclosure
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Genuine binomial bounds for the beta integrals of the intrinsic constant

The rational coefficient recurrence is identified with the actual analytic
binomial series of `(1-t)^p`. A tail of one sign gives finite polynomial
bounds on `[0,1)` without assuming an arithmetic certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- Exact rational coefficients of `(1-t)^p`. -/
def ratBinomialCoefficient (p : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ((n : ℚ) - p) / (n + 1) * ratBinomialCoefficient p n

/-- The genuine generalized binomial coefficients satisfy their multiplicative recurrence. -/
theorem real_choose_succ (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = (a - n) / (n + 1) * Ring.choose a n := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The rational recurrence is exactly the real analytic binomial coefficient. -/
theorem ratBinomialCoefficient_eq (p : ℚ) (n : ℕ) :
    (ratBinomialCoefficient p n : ℝ) = (-1 : ℝ) ^ n * Ring.choose (p : ℝ) n := by
  induction n with
  | zero => simp [ratBinomialCoefficient]
  | succ n ih =>
    simp only [ratBinomialCoefficient, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_one, ih, real_choose_succ, pow_succ]
    ring

/-- Past `p` every recurrence factor is nonnegative, so a nonnegative coefficient stays so. -/
theorem ratBinomialCoefficient_nonneg_of_le {p : ℚ} {N : ℕ} (hp : p ≤ N)
    (hN : 0 ≤ ratBinomialCoefficient p N) {n : ℕ} (hn : N ≤ n) :
    0 ≤ ratBinomialCoefficient p n := by
  induction n, hn using Nat.le_induction with
  | base => exact hN
  | succ n hNn ih =>
    rw [ratBinomialCoefficient]
    apply mul_nonneg _ ih
    apply div_nonneg _ (by positivity)
    have hc : (N : ℚ) ≤ n := by exact_mod_cast hNn
    linarith

/-- Past `p` every recurrence factor is nonnegative, so a nonpositive coefficient stays so. -/
theorem ratBinomialCoefficient_nonpos_of_le {p : ℚ} {N : ℕ} (hp : p ≤ N)
    (hN : ratBinomialCoefficient p N ≤ 0) {n : ℕ} (hn : N ≤ n) :
    ratBinomialCoefficient p n ≤ 0 := by
  induction n, hn using Nat.le_induction with
  | base => exact hN
  | succ n hNn ih =>
    rw [ratBinomialCoefficient]
    apply mul_nonpos_of_nonneg_of_nonpos _ ih
    apply div_nonneg _ (by positivity)
    have hc : (N : ℚ) ≤ n := by exact_mod_cast hNn
    linarith

/-- The actual real power is the sum of the identified rational series. -/
theorem hasSum_ratBinomial (p : ℚ) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) :
    HasSum (fun n ↦ (ratBinomialCoefficient p n : ℝ) * t ^ n) ((1 - t) ^ (p : ℝ)) := by
  have hmem : -t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht] using ht₁
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (p : ℝ))).hasSum_sub
    hmem
  convert h using 1
  · ext n
    simp only [sub_zero, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
      smul_eq_mul, ratBinomialCoefficient_eq]
    rw [neg_pow t n]
    ring

/-- A nonpositive tail makes the finite truncation an upper bound for the actual power. -/
theorem rpow_le_ratBinomial_sum {p : ℚ} {N : ℕ}
    (htail : ∀ n, N ≤ n → ratBinomialCoefficient p n ≤ 0) {t : ℝ} (ht : 0 ≤ t)
    (ht₁ : t < 1) :
    (1 - t) ^ (p : ℝ) ≤ ∑ n ∈ Finset.range N, (ratBinomialCoefficient p n : ℝ) * t ^ n := by
  have hs := (hasSum_ratBinomial p ht ht₁).tendsto_sum_nat
  apply le_of_tendsto hs
  filter_upwards [eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.range_mono hm)
  intro n _ hnN
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hnN)
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast htail n hn') (pow_nonneg ht n)

/-- A nonnegative tail makes the finite truncation a lower bound for the actual power. -/
theorem ratBinomial_sum_le_rpow {p : ℚ} {N : ℕ}
    (htail : ∀ n, N ≤ n → 0 ≤ ratBinomialCoefficient p n) {t : ℝ} (ht : 0 ≤ t)
    (ht₁ : t < 1) :
    ∑ n ∈ Finset.range N, (ratBinomialCoefficient p n : ℝ) * t ^ n ≤ (1 - t) ^ (p : ℝ) := by
  have hs := (hasSum_ratBinomial p ht ht₁).tendsto_sum_nat
  apply ge_of_tendsto hs
  filter_upwards [eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
  intro n _ hnN
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hnN)
  exact mul_nonneg (by exact_mod_cast htail n hn') (pow_nonneg ht n)

end PartialBalayage.Maximal.Square
