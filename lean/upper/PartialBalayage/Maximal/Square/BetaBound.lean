/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: kernel-checked bounds for our beta integrals, a lower bound for B(33/40,47/20) and an upper bound for B(33/40,33/40), from forty-term binomial sums and 40th/20th-root enclosures. -/
module

public import PartialBalayage.Maximal.Square.BetaIntegral
public import PartialBalayage.Maximal.Square.RealBetaIntegral

/-!
# Kernel-checked numerical bounds for the actual beta integrals

Reflection splits each beta integral into two half-interval integrals, and the
Gamma recurrence moves `B(33/40,33/40)` to `B(73/40,73/40)`. The forty-term rational
inequalities and the root-power inequalities are checked by Lean's kernel; the
analytic series and integration proofs identify their results with the original
real integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- Reflection splits the actual beta integral into two half-interval integrals. -/
theorem realBetaIntegral_eq_half_add_half {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    realBetaIntegral u v = (∫ t in (0 : ℝ)..(1 / 2), realBetaIntegrand u v t) +
      ∫ t in (0 : ℝ)..(1 / 2), realBetaIntegrand v u t := by
  have hi := intervalIntegrable_realBetaIntegrand hu hv
  have h₀ : IntervalIntegrable (realBetaIntegrand u v) volume (0 : ℝ) (1 / 2) := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have h₁ : IntervalIntegrable (realBetaIntegrand u v) volume (1 / 2 : ℝ) 1 := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hr : ∀ t, realBetaIntegrand u v (1 - t) = realBetaIntegrand v u t := by
    intro t
    simp only [realBetaIntegrand, sub_sub_cancel, mul_comm]
  have hs := intervalIntegral.integral_comp_sub_left (realBetaIntegrand u v) 1
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
  simp only [hr] at hs
  norm_num only at hs
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₀ h₁
  unfold realBetaIntegral
  linarith

/-- The actual Gamma recurrence moves both parameters of `B(33/40,33/40)` up by one. -/
theorem realBetaIntegral_33_40_eq :
    realBetaIntegral (33 / 40) (33 / 40) =
      (212 / 33 : ℝ) * realBetaIntegral (73 / 40) (73 / 40) := by
  rw [realBetaIntegral_eq_Gamma_mul_div (by norm_num) (by norm_num),
    realBetaIntegral_eq_Gamma_mul_div (by norm_num) (by norm_num)]
  have h₁ : Real.Gamma (73 / 40) = 33 / 40 * Real.Gamma (33 / 40) := by
    rw [show (73 / 40 : ℝ) = 33 / 40 + 1 by norm_num]
    exact Real.Gamma_add_one (by norm_num)
  have h₂ : Real.Gamma (53 / 20) = 33 / 20 * Real.Gamma (33 / 20) := by
    rw [show (53 / 20 : ℝ) = 33 / 20 + 1 by norm_num]
    exact Real.Gamma_add_one (by norm_num)
  have h₃ : Real.Gamma (73 / 20) = 53 / 20 * Real.Gamma (53 / 20) := by
    rw [show (73 / 20 : ℝ) = 53 / 20 + 1 by norm_num]
    exact Real.Gamma_add_one (by norm_num)
  rw [show (33 / 40 : ℝ) + 33 / 40 = 33 / 20 by norm_num,
    show (73 / 40 : ℝ) + 73 / 40 = 73 / 20 by norm_num, h₁, h₃, h₂]
  have hg : Real.Gamma (33 / 20) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp
  ring

/-- The binomial tail of `(1-t)^(27/20)` beyond forty terms is nonnegative. -/
theorem ratBinomialCoefficient_tail_27_20 :
    ∀ n, 40 ≤ n → 0 ≤ ratBinomialCoefficient (47 / 20 - 1) n :=
  fun _ hn ↦ ratBinomialCoefficient_nonneg_of_le (by norm_num) (by decide +kernel) hn

/-- The binomial tail of `(1-t)^(-7/40)` beyond forty terms is nonnegative. -/
theorem ratBinomialCoefficient_tail_neg_7_40 :
    ∀ n, 40 ≤ n → 0 ≤ ratBinomialCoefficient (33 / 40 - 1) n :=
  fun _ hn ↦ ratBinomialCoefficient_nonneg_of_le (by norm_num) (by decide +kernel) hn

/-- The binomial tail of `(1-t)^(33/40)` beyond forty terms is nonpositive. -/
theorem ratBinomialCoefficient_tail_33_40 :
    ∀ n, 40 ≤ n → ratBinomialCoefficient (73 / 40 - 1) n ≤ 0 :=
  fun _ hn ↦ ratBinomialCoefficient_nonpos_of_le (by norm_num) (by decide +kernel) hn

set_option maxRecDepth 4096 in
/-- The forty-term rational sum for `t^(-7/40) (1-t)^(27/20)` on `[0,1/2]`. -/
theorem halfBetaBinomialSum_27_20_ge :
    (1730387715370881 / 2000000000000000 : ℚ) ≤
      halfBetaBinomialSum (47 / 20 - 1) (33 / 40) 40 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The forty-term rational sum for `t^(27/20) (1-t)^(-7/40)` on `[0,1/2]`. -/
theorem halfBetaBinomialSum_neg_7_40_ge :
    (920454151487123 / 2000000000000000 : ℚ) ≤
      halfBetaBinomialSum (33 / 40 - 1) (47 / 20) 40 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The forty-term rational sum for `t^(33/40) (1-t)^(33/40)` on `[0,1/2]`. -/
theorem halfBetaBinomialSum_33_40_le :
    halfBetaBinomialSum (73 / 40 - 1) (73 / 40) 40 ≤
      3962467933606701 / 10000000000000000 := by
  decide +kernel

/-- A kernel-checked lower bound for the actual power `(1/2)^(33/40)`. -/
theorem half_rpow_33_40_ge :
    (88200344125479 / 156250000000000 : ℝ) ≤ (1 / 2 : ℝ) ^ (33 / 40 : ℝ) := by
  have he : IsPowerEnclosureDeg 40 (1 / 2) 33 (88200344125479 / 156250000000000) 1 := by
    refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
    decide +kernel
  have hp := (he.rpow_bounds (by norm_num) (by norm_num)).1
  have hc : ((33 : ℤ) : ℝ) / ((40 : ℕ) : ℝ) = 33 / 40 := by norm_num
  rw [hc] at hp
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hp

/-- A kernel-checked lower bound for the actual power `(1/2)^(47/20)`. -/
theorem half_rpow_47_20_ge :
    (490365061185469 / 2500000000000000 : ℝ) ≤ (1 / 2 : ℝ) ^ (47 / 20 : ℝ) := by
  have he : IsPowerEnclosureDeg 20 (1 / 2) 47 (490365061185469 / 2500000000000000) 1 := by
    refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
    decide +kernel
  have hp := (he.rpow_bounds (by norm_num) (by norm_num)).1
  have hc : ((47 : ℤ) : ℝ) / ((20 : ℕ) : ℝ) = 47 / 20 := by norm_num
  rw [hc] at hp
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hp

/-- A kernel-checked upper bound for the actual power `(1/2)^(73/40)`. -/
theorem half_rpow_73_40_le :
    (1 / 2 : ℝ) ^ (73 / 40 : ℝ) ≤ 2822411012015329 / 10000000000000000 := by
  have he : IsPowerEnclosureDeg 40 (1 / 2) 73 0 (2822411012015329 / 10000000000000000) := by
    refine ⟨le_rfl, by norm_num, ?_, by norm_num⟩
    decide +kernel
  have hp := (he.rpow_bounds (by norm_num) (by norm_num)).2
  have hc : ((73 : ℤ) : ℝ) / ((40 : ℕ) : ℝ) = 73 / 40 := by norm_num
  rw [hc] at hp
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hp

/-- The original convergent integral `B(33/40,47/20)` has a genuine rational lower bound. -/
theorem realBetaIntegral_33_40_47_20_ge :
    (5786582455543623 / 10000000000000000 : ℝ) ≤ realBetaIntegral (33 / 40) (47 / 20) := by
  rw [realBetaIntegral_eq_half_add_half (by norm_num) (by norm_num)]
  have hA := integral_halfBeta_ge (u := 33 / 40) (v := 47 / 20) (by norm_num)
    ratBinomialCoefficient_tail_27_20
  have hB := integral_halfBeta_ge (u := 47 / 20) (v := 33 / 40) (by norm_num)
    ratBinomialCoefficient_tail_neg_7_40
  simp only [Rat.cast_div, Rat.cast_ofNat] at hA hB
  simp only [realBetaIntegrand]
  have hsA : (1730387715370881 / 2000000000000000 : ℝ) ≤
      (halfBetaBinomialSum (47 / 20 - 1) (33 / 40) 40 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using Rat.cast_le (K := ℝ).mpr
      halfBetaBinomialSum_27_20_ge
  have hsB : (920454151487123 / 2000000000000000 : ℝ) ≤
      (halfBetaBinomialSum (33 / 40 - 1) (47 / 20) 40 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using Rat.cast_le (K := ℝ).mpr
      halfBetaBinomialSum_neg_7_40_ge
  have h₁ := mul_le_mul half_rpow_33_40_ge hsA (by norm_num)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
  have h₂ := mul_le_mul half_rpow_47_20_ge hsB (by norm_num)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
  linarith

/-- The original convergent integral `B(33/40,33/40)` has a genuine rational upper bound. -/
theorem realBetaIntegral_33_40_33_40_le :
    realBetaIntegral (33 / 40) (33 / 40) ≤ 14369376870791915 / 10000000000000000 := by
  rw [realBetaIntegral_33_40_eq, realBetaIntegral_eq_half_add_half (by norm_num) (by norm_num)]
  have hC := integral_halfBeta_le (u := 73 / 40) (v := 73 / 40) (by norm_num)
    ratBinomialCoefficient_tail_33_40
  simp only [Rat.cast_div, Rat.cast_ofNat] at hC
  simp only [realBetaIntegrand]
  have hsC : (halfBetaBinomialSum (73 / 40 - 1) (73 / 40) 40 : ℝ) ≤
      3962467933606701 / 10000000000000000 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using Rat.cast_le (K := ℝ).mpr
      halfBetaBinomialSum_33_40_le
  have h₁ : (1 / 2 : ℝ) ^ (73 / 40 : ℝ) * (halfBetaBinomialSum (73 / 40 - 1) (73 / 40) 40 : ℝ) ≤
      2822411012015329 / 10000000000000000 * (3962467933606701 / 10000000000000000) := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (73 / 40 : ℝ) * (3962467933606701 / 10000000000000000) :=
        mul_le_mul_of_nonneg_left hsC (Real.rpow_nonneg (by norm_num) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right half_rpow_73_40_le (by norm_num)
  linarith

end PartialBalayage.Maximal.Square
