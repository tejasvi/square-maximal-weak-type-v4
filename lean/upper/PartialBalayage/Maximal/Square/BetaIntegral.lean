/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the fifth-root half-interval bound is replaced by two-sided bounds for the integral of t^(u-1) (1-t)^(v-1) over [0, 1/2] with rational u, v; the Beta(6/5,6/5) definitions are kept. -/
module

public import PartialBalayage.Maximal.Square.BetaBinomial

/-!
# Exact finite bounds for half-interval beta integrals

Each genuine finite binomial bound is integrated term by term using
convergent ordinary real power integrals. The original `Beta(6/5,6/5)`
integrand and its symmetry are kept for the generic real beta integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual integrand defining `Beta(6/5,6/5)`. -/
def squareBetaIntegrand (t : ℝ) : ℝ := t ^ (1 / 5 : ℝ) * (1 - t) ^ (1 / 5 : ℝ)

/-- The actual convergent real beta integral `Beta(6/5,6/5)`. -/
def squareBetaIntegral : ℝ := ∫ t in (0 : ℝ)..1, squareBetaIntegrand t

theorem continuous_squareBetaIntegrand : Continuous squareBetaIntegrand := by
  unfold squareBetaIntegrand
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).mul
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).comp
      (continuous_const.sub continuous_id))

theorem squareBetaIntegrand_sub (t : ℝ) :
    squareBetaIntegrand (1 - t) = squareBetaIntegrand t := by
  simp only [squareBetaIntegrand, sub_sub_cancel, mul_comm]

/-- The actual beta integral is strictly positive. -/
theorem squareBetaIntegral_pos : 0 < squareBetaIntegral := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    continuous_squareBetaIntegrand.continuousOn
  · intro t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    unfold squareBetaIntegrand
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _)

/-- The exact rational sum obtained by integrating the first `N` binomial terms of
`(1-t)^p` against `t^(u-1)` over `[0, 1/2]`, divided by `(1/2)^u`. -/
def halfBetaBinomialSum (p u : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, ratBinomialCoefficient p n / ((2 : ℚ) ^ n * (n + u))

/-- The actual half-interval beta integrand is integrable for a positive first parameter. -/
theorem intervalIntegrable_halfBetaIntegrand {u : ℝ} (hu : 0 < u) (p : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ (u - 1) * (1 - t) ^ p) volume 0 (1 / 2) := by
  apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < u - 1)).mul_continuousOn
  apply ContinuousOn.rpow_const (by fun_prop)
  intro t ht
  left
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
  exact (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne'

/-- Every actual binomial monomial is integrable on the half interval. -/
theorem intervalIntegrable_halfBetaMonomial {u : ℝ} (hu : 0 < u) (c : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ c * (t ^ (u - 1) * t ^ n)) volume 0 (1 / 2) :=
  ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < u - 1)).mul_continuousOn
    (continuous_pow n).continuousOn).const_mul c

/-- The true half-interval monomial integral has its exact rational factor. -/
theorem integral_halfBetaMonomial {u : ℚ} (hu : 0 < u) (c : ℚ) (n : ℕ) :
    (∫ t in (0 : ℝ)..(1 / 2), (c : ℝ) * (t ^ ((u : ℝ) - 1) * t ^ n)) =
      (1 / 2 : ℝ) ^ (u : ℝ) * ((c / ((2 : ℚ) ^ n * (n + u)) : ℚ) : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hnu : (0 : ℝ) < (n : ℝ) + u := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [intervalIntegral.integral_const_mul]
  have hi : (∫ t in (0 : ℝ)..(1 / 2), t ^ ((u : ℝ) - 1) * t ^ n) =
      (1 / 2 : ℝ) ^ ((n : ℝ) + u) / ((n : ℝ) + u) := by
    calc
      _ = ∫ t in (0 : ℝ)..(1 / 2), t ^ ((n : ℝ) + ((u : ℝ) - 1)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        change t ^ ((u : ℝ) - 1) * t ^ n = t ^ ((n : ℝ) + ((u : ℝ) - 1))
        rw [Real.rpow_add ht.1, Real.rpow_natCast]
        exact mul_comm _ _
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < (n : ℝ) + ((u : ℝ) - 1)))]
        have he : (n : ℝ) + ((u : ℝ) - 1) + 1 = (n : ℝ) + u := by ring
        rw [he, Real.zero_rpow hnu.ne', sub_zero]
  rw [hi, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_natCast]
  push_cast
  rw [div_pow, one_pow]
  have h₂ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hn : (n : ℝ) + u ≠ 0 := hnu.ne'
  field_simp

/-- The finite sum of half-interval monomial integrals is the exact rational sum. -/
theorem integral_halfBetaBinomial_sum {u : ℚ} (hu : 0 < u) (p : ℚ) (N : ℕ) :
    (∫ t in (0 : ℝ)..(1 / 2), ∑ n ∈ Finset.range N,
        (ratBinomialCoefficient p n : ℝ) * (t ^ ((u : ℝ) - 1) * t ^ n)) =
      (1 / 2 : ℝ) ^ (u : ℝ) * (halfBetaBinomialSum p u N : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  rw [intervalIntegral.integral_finsetSum
    (fun n _ ↦ intervalIntegrable_halfBetaMonomial hu' _ n)]
  simp_rw [integral_halfBetaMonomial hu]
  simp only [halfBetaBinomialSum, Rat.cast_sum, Finset.mul_sum]

theorem intervalIntegrable_halfBetaBinomial_sum {u : ℝ} (hu : 0 < u) (c : ℕ → ℝ) (N : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ ∑ n ∈ Finset.range N, c n * (t ^ (u - 1) * t ^ n))
      volume 0 (1 / 2) := by
  have he : (∑ n ∈ Finset.range N, fun t : ℝ ↦ c n * (t ^ (u - 1) * t ^ n)) =
      (fun t : ℝ ↦ ∑ n ∈ Finset.range N, c n * (t ^ (u - 1) * t ^ n)) := by
    ext t
    simp only [Finset.sum_apply]
  rw [← he]
  exact IntervalIntegrable.sum (Finset.range N)
    (fun n _ ↦ intervalIntegrable_halfBetaMonomial hu (c n) n)

/-- A nonpositive binomial tail gives an exact rational upper bound for the half integral. -/
theorem integral_halfBeta_le {u v : ℚ} (hu : 0 < u) {N : ℕ}
    (htail : ∀ n, N ≤ n → ratBinomialCoefficient (v - 1) n ≤ 0) :
    (∫ t in (0 : ℝ)..(1 / 2), t ^ ((u : ℝ) - 1) * (1 - t) ^ ((v : ℝ) - 1)) ≤
      (1 / 2 : ℝ) ^ (u : ℝ) * (halfBetaBinomialSum (v - 1) u N : ℝ) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  rw [← integral_halfBetaBinomial_sum hu]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (intervalIntegrable_halfBetaIntegrand hu' _)
    (intervalIntegrable_halfBetaBinomial_sum hu' _ N)
  intro t ht
  have hb := rpow_le_ratBinomial_sum htail ht.1 (by linarith [ht.2])
  rw [Rat.cast_sub, Rat.cast_one] at hb
  have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1 ((u : ℝ) - 1))
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- A nonnegative binomial tail gives an exact rational lower bound for the half integral. -/
theorem integral_halfBeta_ge {u v : ℚ} (hu : 0 < u) {N : ℕ}
    (htail : ∀ n, N ≤ n → 0 ≤ ratBinomialCoefficient (v - 1) n) :
    (1 / 2 : ℝ) ^ (u : ℝ) * (halfBetaBinomialSum (v - 1) u N : ℝ) ≤
      ∫ t in (0 : ℝ)..(1 / 2), t ^ ((u : ℝ) - 1) * (1 - t) ^ ((v : ℝ) - 1) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  rw [← integral_halfBetaBinomial_sum hu]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (intervalIntegrable_halfBetaBinomial_sum hu' _ N)
    (intervalIntegrable_halfBetaIntegrand hu' _)
  intro t ht
  have hb := ratBinomial_sum_le_rpow htail ht.1 (by linarith [ht.2])
  rw [Rat.cast_sub, Rat.cast_one] at hb
  have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1 ((u : ℝ) - 1))
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

end PartialBalayage.Maximal.Square
