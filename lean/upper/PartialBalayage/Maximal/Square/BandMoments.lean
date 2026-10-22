/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandSeries

/-!
# Elementary moments of the exterior profile

On `[v, R]` the profile is `Ψ(q) = q^(-α) - R^(-α)`, so its moments against `q^n` and
`(R - q)^n` are elementary in `R^(1-α)`, `v^(1-α)` and `R^(-α)`; the moments of the profile
slope `q^(-1-α)` are elementary in `R^(-α)` and `v^(-α)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

theorem bandPsi_eq_on {q : ℝ} (hq : 0 < q) (hqR : q ≤ Rs) :
    bandPsi q = q ^ (-α) - Rs ^ (-α) := by
  unfold bandPsi
  exact max_eq_left (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hq hqR (by norm_num)))

theorem integral_rpow_shift {v : ℝ} (hv : 0 < v) (hvR : v ≤ Rs) (r : ℝ) (hr : r ≠ -1) :
    (∫ q in v..Rs, q ^ r) = (Rs ^ (r + 1) - v ^ (r + 1)) / (r + 1) := by
  apply integral_rpow
  right
  refine ⟨hr, ?_⟩
  rw [uIcc_of_le hvR]
  intro h
  exact absurd h.1 (not_le.mpr hv)

/-- The power moment of the profile. -/
theorem integral_bandPsi_mul_pow {v : ℝ} (hv : 0 < v) (hvR : v ≤ Rs) (n : ℕ) :
    (∫ q in v..Rs, bandPsi q * q ^ n) =
      (Rs ^ ((n : ℝ) + 1 - α) - v ^ ((n : ℝ) + 1 - α)) / ((n : ℝ) + 1 - α) -
        Rs ^ (-α) * ((Rs ^ (n + 1) - v ^ (n + 1)) / ((n : ℝ) + 1)) := by
  have hcongr : (∫ q in v..Rs, bandPsi q * q ^ n) =
      ∫ q in v..Rs, (q ^ ((n : ℝ) - α) - Rs ^ (-α) * q ^ n) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hvR] at hq
    have hq0 : 0 < q := hv.trans_le hq.1
    simp only
    rw [bandPsi_eq_on hq0 hq.2, sub_mul, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    ring_nf
  rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_pow,
    integral_rpow_shift hv hvR]
  · ring_nf
  · intro h
    have : ((n : ℝ) - α) + 1 = 0 := by linarith
    have hn : (n : ℝ) = 47 / 40 - 1 - 1 + 1 := by linarith
    have h2 : (40 : ℝ) * n = 7 := by linarith
    have h3 : (40 * n : ℕ) = 7 := by exact_mod_cast h2
    omega
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro q hq; left; rw [uIcc_of_le hvR] at hq; exact (hv.trans_le hq.1).ne'
  · exact (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _

/-- The power moment of the profile slope. -/
theorem integral_slope_mul_pow {v : ℝ} (hv : 0 < v) (hvR : v ≤ Rs) (n : ℕ) :
    (∫ q in v..Rs, q ^ (-1 - α) * q ^ n) =
      (Rs ^ ((n : ℝ) - α) - v ^ ((n : ℝ) - α)) / ((n : ℝ) - α) := by
  have hcongr : (∫ q in v..Rs, q ^ (-1 - α) * q ^ n) = ∫ q in v..Rs, q ^ ((n : ℝ) - 1 - α) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hvR] at hq
    have hq0 : 0 < q := hv.trans_le hq.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hq0]
    ring_nf
  rw [hcongr, integral_rpow_shift hv hvR]
  · ring_nf
  · intro h
    have h2 : (40 : ℝ) * n = 47 := by linarith
    have h3 : (40 * n : ℕ) = 47 := by exact_mod_cast h2
    omega

/-- Binomial expansion of the reflected moments. -/
theorem integral_mul_sub_pow {F : ℝ → ℝ} {v : ℝ} (hvR : v ≤ Rs) (hF : ContinuousOn F (Icc v Rs))
    (n : ℕ) :
    (∫ q in v..Rs, F q * (Rs - q) ^ n) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Rs ^ (n - j) * (-1) ^ j *
        ∫ q in v..Rs, F q * q ^ j := by
  have hexp : ∀ q : ℝ, (Rs - q) ^ n = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * Rs ^ (n - j) * (-1) ^ j * q ^ j := by
    intro q
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [neg_pow]
    ring
  simp_rw [hexp, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring
  · intro j _
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hvR]
    exact hF.mul (continuousOn_const.mul (continuousOn_id.pow j))

end PartialBalayage.Maximal.Square

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

theorem integral_rpow_between {v c : ℝ} (hv : 0 < v) (hvc : v ≤ c) (r : ℝ) (hr : r ≠ -1) :
    (∫ q in v..c, q ^ r) = (c ^ (r + 1) - v ^ (r + 1)) / (r + 1) := by
  apply integral_rpow
  right
  refine ⟨hr, ?_⟩
  rw [uIcc_of_le hvc]
  intro h
  exact absurd h.1 (not_le.mpr hv)

/-- The power moment of the profile on `[v, c]`, `c ≤ R`. -/
theorem integral_bandPsi_mul_pow_between {v c : ℝ} (hv : 0 < v) (hvc : v ≤ c) (hcR : c ≤ Rs) (n : ℕ) :
    (∫ q in v..c, bandPsi q * q ^ n) =
      (c ^ ((n : ℝ) + 1 - α) - v ^ ((n : ℝ) + 1 - α)) / ((n : ℝ) + 1 - α) -
        Rs ^ (-α) * ((c ^ (n + 1) - v ^ (n + 1)) / ((n : ℝ) + 1)) := by
  have hcongr : (∫ q in v..c, bandPsi q * q ^ n) =
      ∫ q in v..c, (q ^ ((n : ℝ) - α) - Rs ^ (-α) * q ^ n) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hvc] at hq
    have hq0 : 0 < q := hv.trans_le hq.1
    simp only
    rw [bandPsi_eq_on hq0 (hq.2.trans hcR), sub_mul, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    ring_nf
  rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_pow,
    integral_rpow_between hv hvc]
  · ring_nf
  · intro h
    have h2 : (40 : ℝ) * n = 7 := by linarith
    have h3 : (40 * n : ℕ) = 7 := by exact_mod_cast h2
    omega
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro q hq; left; rw [uIcc_of_le hvc] at hq; exact (hv.trans_le hq.1).ne'
  · exact (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _

/-- The power moment of the profile slope on `[v, c]`. -/
theorem integral_slope_mul_pow_between {v c : ℝ} (hv : 0 < v) (hvc : v ≤ c) (n : ℕ) :
    (∫ q in v..c, q ^ (-1 - α) * q ^ n) =
      (c ^ ((n : ℝ) - α) - v ^ ((n : ℝ) - α)) / ((n : ℝ) - α) := by
  have hcongr : (∫ q in v..c, q ^ (-1 - α) * q ^ n) = ∫ q in v..c, q ^ ((n : ℝ) - 1 - α) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hvc] at hq
    have hq0 : 0 < q := hv.trans_le hq.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hq0]
    ring_nf
  rw [hcongr, integral_rpow_between hv hvc]
  · ring_nf
  · intro h
    have h2 : (40 : ℝ) * n = 47 := by linarith
    have h3 : (40 * n : ℕ) = 47 := by exact_mod_cast h2
    omega

end PartialBalayage.Maximal.Square
