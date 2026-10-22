/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Constants.Radial
public import CenteredMaximal.Ball.CenterLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Center boundaries for radial harmonic tangents

A radial harmonic tangent times `r^n` tends to zero at the center in every positive dimension.
This removes the singular inner boundary in integration by parts against bounded Laplacians.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open PartialBalayage.Constants

namespace PartialBalayage

/-- The radial harmonic tangent written in ordinary-radius coordinates. -/
def harmonicRadialTangent (n : ℕ) (a q d r : ℝ) : ℝ :=
  q + a * d * harmonicCoordinate ((n : ℝ) / 2) (r ^ 2 / a)

/-- Derivative of a harmonic tangent in ordinary-radius coordinates. -/
theorem hasDerivAt_harmonicRadialTangent (n : ℕ) {a r : ℝ} (ha : 0 < a)
    (hr : 0 < r) (q d : ℝ) :
    HasDerivAt (harmonicRadialTangent n a q d)
      (2 * d * r * (r ^ 2 / a) ^ (-(n : ℝ) / 2)) r := by
  have h := ((hasDerivAt_harmonicCoordinate (β := (n : ℝ) / 2)
    (div_pos (pow_pos hr 2) ha)).comp r
    ((hasDerivAt_pow 2 r).div_const a)).const_mul (a * d)
  convert h.const_add q using 1
  · rfl
  · norm_num only [Nat.add_one_sub_one, pow_one]
    field_simp

/-- The ordinary-radius inward flux of the harmonic tangent is constant. -/
theorem harmonicRadialTangent_deriv_mul_pow (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (d : ℝ) :
    (2 * d * r * (r ^ 2 / a) ^ (-(n : ℝ) / 2)) * r ^ (n - 1) =
      2 * d * a ^ ((n : ℝ) / 2) := by
  have hpow : (r ^ 2) ^ ((n : ℝ) / 2) = r ^ n := by
    rw [← Real.rpow_two r, ← Real.rpow_mul hr.le]
    norm_num only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
  have hpred : r ^ (n - 1) * r = r ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [neg_div, Real.rpow_neg (div_pos (pow_pos hr 2) ha).le,
    Real.div_rpow (sq_nonneg r) ha.le, hpow]
  field_simp
  rw [← hpred]
  ring

/-- The harmonic-coordinate singularity is smaller than the shrinking ball volume. -/
theorem harmonicCoordinate_sq_mul_pow_tendsto_zero (n : ℕ) (hn : 1 ≤ n)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ ↦ harmonicCoordinate ((n : ℝ) / 2) (r ^ 2 / a) * r ^ n)
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp2 : Tendsto (fun r : ℝ ↦ r ^ 2) (𝓝[>] 0) (𝓝 0) := by simpa using hid.pow 2
  by_cases hn2 : n = 2
  · subst n
    have hlog : Tendsto (fun r : ℝ ↦ Real.log r * r ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.rpow_two] using
        tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2)
    have hlim := (hlog.const_mul 2).sub (hp2.const_mul (Real.log a))
    simp only [mul_zero, sub_zero] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num, harmonicCoordinate,
      ite_true]
    rw [Real.log_div hr2 ha.ne', Real.log_pow]
    ring
  · have hβ : (n : ℝ) / 2 ≠ 1 := by
      intro h
      apply hn2
      exact_mod_cast (show (n : ℝ) = 2 by linarith)
    have hn0 : n ≠ 0 := by omega
    have hpn : Tendsto (fun r : ℝ ↦ r ^ n) (𝓝[>] 0) (𝓝 0) := by
      simpa [hn0] using hid.pow n
    have hlim := ((hp2.const_mul (a ^ ((n : ℝ) / 2 - 1))).sub hpn).div_const
      (1 - (n : ℝ) / 2)
    simp only [mul_zero, sub_zero, zero_div] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hpow : (r ^ 2) ^ (1 - (n : ℝ) / 2) = r ^ ((2 : ℝ) - n) := by
      rw [← Real.rpow_two r, ← Real.rpow_mul hr.le]
      congr 1
      ring
    have hprod : r ^ ((2 : ℝ) - n) * r ^ n = r ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr,
        show (2 : ℝ) - n + n = 2 by ring, Real.rpow_two]
    have hc : (r ^ 2 / a) ^ (1 - (n : ℝ) / 2) * r ^ n =
        a ^ ((n : ℝ) / 2 - 1) * r ^ 2 := by
      rw [Real.div_rpow (sq_nonneg r) ha.le, hpow, div_mul_eq_mul_div, hprod,
        div_eq_mul_inv, ← Real.rpow_neg ha.le]
      have he : -(1 - (n : ℝ) / 2) = (n : ℝ) / 2 - 1 := by ring
      rw [he]
      ring
    rw [harmonicCoordinate, ite_eq_right hβ]
    symm
    calc
      _ = ((r ^ 2 / a) ^ (1 - (n : ℝ) / 2) * r ^ n - r ^ n) /
          (1 - (n : ℝ) / 2) := by ring
      _ = _ := by rw [hc]

/-- Multiplication by the ball-volume factor removes every harmonic tangent's center singularity. -/
theorem harmonicRadialTangent_mul_pow_tendsto_zero (n : ℕ) (hn : 1 ≤ n)
    {a : ℝ} (ha : 0 < a) (q d : ℝ) :
    Tendsto (fun r ↦ harmonicRadialTangent n a q d r * r ^ n) (𝓝[>] 0) (𝓝 0) := by
  have hn0 : n ≠ 0 := by omega
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpn : Tendsto (fun r : ℝ ↦ r ^ n) (𝓝[>] 0) (𝓝 0) := by
    simpa [hn0] using hid.pow n
  have hlim := (hpn.const_mul q).add
    ((harmonicCoordinate_sq_mul_pow_tendsto_zero n hn ha).const_mul (a * d))
  simp only [mul_zero, add_zero] at hlim
  convert hlim using 1
  funext r
  unfold harmonicRadialTangent
  ring

/-- A profile whose volume-weighted center limit vanishes has no inner ball boundary term. -/
theorem tendsto_profile_mul_integral_ball_zero (n : ℕ) [NeZero n] (ψ : ℝ → ℝ)
    (hψ : Tendsto (fun r : ℝ ↦ ψ r * r ^ n) (𝓝[>] 0) (𝓝 0))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ ↦ ψ r * ∫ y in Metric.ball x r, g y) (𝓝[>] 0) (𝓝 0) := by
  let V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  have hlim : Tendsto (fun r : ℝ ↦ (B * V) * ‖ψ r * r ^ n‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using hψ.norm.const_mul (B * V)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hbound := CenteredMaximal.Ball.norm_integral_ball_le_const_mul_pow n g x B hB hr.le
  calc
    ‖ψ r * ∫ y in Metric.ball x r, g y‖ =
        ‖ψ r‖ * ‖∫ y in Metric.ball x r, g y‖ := norm_mul _ _
    _ ≤ ‖ψ r‖ * ((B * V) * r ^ n) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (B * V) * ‖ψ r * r ^ n‖ := by
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le _)]
      ring

end PartialBalayage
