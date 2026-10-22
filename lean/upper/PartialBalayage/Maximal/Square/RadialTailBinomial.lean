/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20). -/
module

public import PartialBalayage.Maximal.Square.BetaBinomial

/-!
# Genuine positive binomial lower bounds for the incoming radial tail

The rational rising-factorial recurrence is the actual analytic expansion
of the power with exponent minus 87/40. Both its nonnegative argument
and its symmetric pair have nonnegative tails, so every finite truncation is
a proved lower bound on the actual three-term incoming-tail integrand.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- Actual rising-factorial coefficients for the incoming power kernel. -/
def radialTailBinomialCoefficient : ℕ → ℚ
  | 0 => 1
  | n + 1 => ((n : ℚ) + 87 / 40) / (n + 1) * radialTailBinomialCoefficient n

theorem radialTailBinomialCoefficient_eq (n : ℕ) :
    (radialTailBinomialCoefficient n : ℝ) =
      (-1 : ℝ) ^ n * Ring.choose (-87 / 40 : ℝ) n := by
  induction n with
  | zero => simp [radialTailBinomialCoefficient]
  | succ n ih =>
    simp only [radialTailBinomialCoefficient, Rat.cast_mul, Rat.cast_div, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, ih, real_choose_succ, pow_succ]
    ring

theorem radialTailBinomialCoefficient_nonneg (n : ℕ) :
    0 ≤ radialTailBinomialCoefficient n := by
  induction n with
  | zero => norm_num [radialTailBinomialCoefficient]
  | succ n ih =>
    rw [radialTailBinomialCoefficient]
    exact mul_nonneg (by positivity) ih

/-- The actual singular power equals the genuinely convergent binomial series. -/
theorem hasSum_radialTailBinomial {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n ↦ (radialTailBinomialCoefficient n : ℝ) * t ^ n)
      ((1 - t) ^ (-87 / 40 : ℝ)) := by
  have hmem : -t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs] using ht
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-87 / 40 : ℝ))).hasSum_sub
    hmem
  convert h using 1
  · ext n
    simp only [sub_zero, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
      smul_eq_mul, radialTailBinomialCoefficient_eq]
    rw [neg_pow t n]
    ring

/-- At a nonnegative argument every finite truncation lies below the actual power. -/
theorem radialTailBinomial_sum_le_rpow {t : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, (radialTailBinomialCoefficient n : ℝ) * t ^ n) ≤
      (1 - t) ^ (-87 / 40 : ℝ) := by
  have htabs : |t| < 1 := by simpa only [abs_of_nonneg ht] using ht₁
  have hs := (hasSum_radialTailBinomial htabs).tendsto_sum_nat
  apply ge_of_tendsto hs
  filter_upwards [eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
  intro n _ _
  exact mul_nonneg (by exact_mod_cast radialTailBinomialCoefficient_nonneg n)
    (pow_nonneg ht n)

theorem add_pow_neg_nonneg (t : ℝ) (n : ℕ) : 0 ≤ t ^ n + (-t) ^ n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow]
    exact add_nonneg (he.pow_nonneg t) (he.pow_nonneg t)
  · rw [ho.neg_pow]
    simp

/-- The two actual symmetric powers have a nonnegative even-coefficient tail. -/
theorem hasSum_radialTailBinomial_symmetric {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n ↦ (radialTailBinomialCoefficient n : ℝ) * (t ^ n + (-t) ^ n))
      ((1 - t) ^ (-87 / 40 : ℝ) + (1 + t) ^ (-87 / 40 : ℝ)) := by
  have hn : |-t| < 1 := by simpa only [abs_neg] using ht
  simpa only [mul_add, sub_neg_eq_add] using
    (hasSum_radialTailBinomial ht).add (hasSum_radialTailBinomial hn)

/-- Every symmetric finite truncation lies below the actual pair of singular powers. -/
theorem radialTailBinomial_symmetric_sum_le_rpow {t : ℝ} (ht : |t| < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (radialTailBinomialCoefficient n : ℝ) * (t ^ n + (-t) ^ n)) ≤
      (1 - t) ^ (-87 / 40 : ℝ) + (1 + t) ^ (-87 / 40 : ℝ) := by
  apply ge_of_tendsto (hasSum_radialTailBinomial_symmetric ht).tendsto_sum_nat
  filter_upwards [eventually_ge_atTop N] with m hm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
  intro n _ _
  exact mul_nonneg (by exact_mod_cast radialTailBinomialCoefficient_nonneg n)
    (add_pow_neg_nonneg t n)

/-- The entire actual three-term incoming kernel dominates each finite rational truncation. -/
theorem radialTailBinomial_combined_sum_le {r d : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1)
    (hd : |d| < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (radialTailBinomialCoefficient n : ℝ) * (2 * r ^ n + d ^ n + (-d) ^ n)) ≤
      2 * (1 - r) ^ (-87 / 40 : ℝ) +
        (1 - d) ^ (-87 / 40 : ℝ) + (1 + d) ^ (-87 / 40 : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range N,
        (2 * ((radialTailBinomialCoefficient n : ℝ) * r ^ n) +
          (radialTailBinomialCoefficient n : ℝ) * (d ^ n + (-d) ^ n)) := by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = 2 * (∑ n ∈ Finset.range N, (radialTailBinomialCoefficient n : ℝ) * r ^ n) +
        ∑ n ∈ Finset.range N,
          (radialTailBinomialCoefficient n : ℝ) * (d ^ n + (-d) ^ n) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have h := add_le_add
        (mul_le_mul_of_nonneg_left (radialTailBinomial_sum_le_rpow hr hr₁ N)
          (by norm_num : (0 : ℝ) ≤ 2))
        (radialTailBinomial_symmetric_sum_le_rpow hd N)
      simpa only [add_assoc] using h

end PartialBalayage.Maximal.Square
