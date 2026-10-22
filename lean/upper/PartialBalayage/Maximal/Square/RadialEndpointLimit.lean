/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialLocalSecondDifference
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Genuine radial endpoint cancellations

Actual differentiability at the origin and actual quadratic second
differences control the singular endpoint factors in ordinary integration
by parts. All limits are proved along the positive half-line.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- A true zero first-order remainder cancels every power less singular than t⁻¹. -/
theorem tendsto_rpow_mul_of_hasDerivAt_zero {f : ℝ → ℝ} {f' p : ℝ}
    (hf : HasDerivAt f f' 0) (hf₀ : f 0 = 0) (hp : -1 < p) :
    Tendsto (fun t : ℝ ↦ t ^ p * f t) (𝓝[>] 0) (𝓝 0) := by
  have hp₁ : 0 < p + 1 := by linarith
  have hc : ContinuousAt (fun t : ℝ ↦ t ^ (p + 1)) 0 :=
    (Real.continuous_rpow_const hp₁.le).continuousAt
  have hpow : Tendsto (fun t : ℝ ↦ t ^ (p + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp₁.ne'] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : ℝ ↦ f t / t) (𝓝[>] 0) (𝓝 f') := by
    simpa only [zero_add, hf₀, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hf.tendsto_slope_zero_right
  have h := hpow.mul hs
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  rw [Real.rpow_add htpos, Real.rpow_one]
  field_simp

/-- The actual symmetric negative-power difference cancels every order below two. -/
theorem tendsto_rpow_mul_shifted_secondDifference {α r : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ t ^ (-α) *
      ((r + t) ^ (-α) + (r - t) ^ (-α) - 2 * r ^ (-α)))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_quadratic_shifted_negative_power hα0 hr
  have hp : 0 < 2 - α := by linarith
  have hc : ContinuousAt (fun t : ℝ ↦ t ^ (2 - α)) 0 :=
    (Real.continuous_rpow_const hp.le).continuousAt
  have hpow : Tendsto (fun t : ℝ ↦ |C| * t ^ (2 - α)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne', mul_zero] using
      (hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul |C|
  apply squeeze_zero_norm' _ hpow
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < r / 2 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const (by positivity)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htr
  have htpos : 0 < t := ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
  calc
    _ ≤ t ^ (-α) * (C * t ^ 2) :=
      mul_le_mul_of_nonneg_left (hC t ⟨htpos, htr.le⟩)
        (Real.rpow_nonneg htpos.le _)
    _ = C * (t ^ (-α) * t ^ 2) := by ring
    _ ≤ |C| * (t ^ (-α) * t ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self C)
        (mul_nonneg (Real.rpow_nonneg htpos.le _) (sq_nonneg t))
    _ = |C| * t ^ (2 - α) := by
      rw [← Real.rpow_two, ← Real.rpow_add htpos]
      congr 2
      ring

end PartialBalayage.Maximal.Square
