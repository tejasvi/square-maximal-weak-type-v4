/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.RoundedSeries
public import PartialBalayage.Maximal.Square.BetaBinomial

/-!
# Positive binomial series of negative powers

For `p ≥ 0` the coefficients of `(1 - t)^(-p)` are nonnegative, so every finite truncation,
also with the downward-rounded coefficients, is a lower bound on `[0, 1)`.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

theorem exactRising_eq_choose (p : ℚ) (n : ℕ) :
    (exactRising p n : ℝ) = (-1 : ℝ) ^ n * Ring.choose (-(p : ℝ)) n := by
  induction n with
  | zero => simp [exactRising]
  | succ n ih =>
    simp only [exactRising, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, ih, real_choose_succ, pow_succ]
    ring

theorem exactRising_nonneg {p : ℚ} (hp : 0 ≤ p) (n : ℕ) : 0 ≤ exactRising p n := by
  induction n with
  | zero => simp [exactRising]
  | succ n ih => exact mul_nonneg (div_nonneg (by positivity) (by positivity)) ih

/-- The negative power equals its convergent binomial series. -/
theorem hasSum_exactRising (p : ℚ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n ↦ (exactRising p n : ℝ) * t ^ n) ((1 - t) ^ (-(p : ℝ))) := by
  have hmem : -t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs] using ht
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-(p : ℝ)))).hasSum_sub hmem
  convert h using 1
  · ext n
    simp only [sub_zero, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
      smul_eq_mul, exactRising_eq_choose]
    rw [neg_pow t n]
    ring

/-- Every finite truncation with nonnegative coefficients below the exact ones is a lower bound. -/
theorem sum_le_rpow_of_le_exactRising {p : ℚ} (hp : 0 ≤ p) {c : ℕ → ℚ} (hc : ∀ n, c n ≤ exactRising p n) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n) ≤ (1 - t) ^ (-(p : ℝ)) := by
  have htabs : |t| < 1 := by simpa only [abs_of_nonneg ht] using ht₁
  have hs := (hasSum_exactRising p htabs).tendsto_sum_nat
  have hle : (∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n) ≤
      ∑ n ∈ Finset.range N, (exactRising p n : ℝ) * t ^ n := by
    apply Finset.sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc n) (pow_nonneg ht n)
  refine hle.trans (ge_of_tendsto hs ?_)
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
  intro n _ _
  exact mul_nonneg (by exact_mod_cast exactRising_nonneg hp n) (pow_nonneg ht n)

/-- The rounded coefficients give lower bounds of the negative power on `[0, 1)`. -/
theorem roundedRising_sum_le_rpow (P : ℕ) {p : ℚ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 ≤ t)
    (ht₁ : t < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * t ^ n) ≤ (1 - t) ^ (-(p : ℝ)) :=
  sum_le_rpow_of_le_exactRising hp (roundedRising_le P hp) ht ht₁ N

/-- The scaled form: `(a - q)^(-p) ≥ ∑ c n q^n a^(-p-n)` for `0 ≤ q < a`. -/
theorem sum_le_sub_rpow (P : ℕ) {p : ℚ} (hp : 0 ≤ p) {a q : ℝ} (hq : 0 ≤ q) (hqa : q < a)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * q ^ n * a ^ (-(p : ℝ) - n)) ≤
      (a - q) ^ (-(p : ℝ)) := by
  have ha : 0 < a := hq.trans_lt hqa
  have h := roundedRising_sum_le_rpow P hp (div_nonneg hq ha.le) ((div_lt_one ha).mpr hqa) N
  have he : (a - q) ^ (-(p : ℝ)) = a ^ (-(p : ℝ)) * (1 - q / a) ^ (-(p : ℝ)) := by
    rw [← Real.mul_rpow ha.le (by rw [sub_nonneg, div_le_one ha]; exact hqa.le)]
    congr 1
    field_simp
  rw [he]
  calc
    _ = a ^ (-(p : ℝ)) * ∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * (q / a) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [div_pow, Real.rpow_sub ha, Real.rpow_natCast]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha.le _)

end PartialBalayage.Maximal.Square
