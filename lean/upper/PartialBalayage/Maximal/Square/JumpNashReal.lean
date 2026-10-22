/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpNash

/-!
# Real quantitative bounds from the genuine jump Nash inequality

The actual extended-integral averaging estimate becomes an ordinary quantitative
norm bound for integrable states. Its mass coefficient tends to zero with the
averaging scale; this gives domain-independent obstacle bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem realLp_enorm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : Lp ℝ 2 μ) : ‖v‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg v)]

set_option maxHeartbeats 600000 in
/-- The genuine averaging inequality with ordinary real norms and mass. -/
theorem stableJump_nash_averaging_real {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ)) :
    jumpAveragingWeight α R * R ^ 2 * ‖stableJumpValue α U‖ ^ 2 ≤
      2 * R * stableJumpForm α U U + 2 * jumpAveragingWeight α R *
        (∫ x : E, ‖stableJumpValue α U x‖) ^ 2 := by
  have hw := (jumpAveragingWeight_pos hα0 hα2 hR).le
  have hE : 0 ≤ stableJumpForm α U U := by rw [stableJumpForm_self]; positivity
  have he : stableJumpForm α U U =
      ‖stableJumpData α U 0‖ ^ 2 + ‖stableJumpData α U 1‖ ^ 2 := by
    rw [stableJumpForm_self, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have h := stableJump_nash_averaging hα0 hα2 hR U
  have hl : ENNReal.ofReal (jumpAveragingWeight α R) * ENNReal.ofReal R ^ (2 : ℕ) *
        ‖stableJumpValue α U‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (jumpAveragingWeight α R * R ^ 2 * ‖stableJumpValue α U‖ ^ 2) := by
    rw [realLp_enorm_sq, ← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul hw,
      ← ENNReal.ofReal_mul (mul_nonneg hw (sq_nonneg R))]
  have hm : (∫⁻ x : E, ‖stableJumpValue α U x‖ₑ) ^ (2 : ℕ) =
      ENNReal.ofReal ((∫ x : E, ‖stableJumpValue α U x‖) ^ 2) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hu,
      ← ENNReal.ofReal_pow (integral_nonneg (fun _ ↦ norm_nonneg _))]
  have hterm (a b : ℝ) (ha : 0 ≤ a) :
      (2 : ℝ≥0∞) * ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (2 * a * b) := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) ha)]
  have hr : 2 * ENNReal.ofReal R * (‖stableJumpData α U 0‖ₑ ^ (2 : ℕ) +
        ‖stableJumpData α U 1‖ₑ ^ (2 : ℕ)) +
      2 * ENNReal.ofReal (jumpAveragingWeight α R) *
        (∫⁻ x : E, ‖stableJumpValue α U x‖ₑ) ^ (2 : ℕ) =
      ENNReal.ofReal (2 * R * stableJumpForm α U U + 2 * jumpAveragingWeight α R *
        (∫ x : E, ‖stableJumpValue α U x‖) ^ 2) := by
    rw [realLp_enorm_sq, realLp_enorm_sq,
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← he, hm,
      hterm R _ hR.le, hterm (jumpAveragingWeight α R) _ hw,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hl, hr, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

/-- The full singular energy and actual mass control the actual state norm. -/
theorem stableJump_norm_sq_le_mass_energy {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ)) :
    ‖stableJumpValue α U‖ ^ 2 ≤
      (2 / R ^ 2) * (∫ x : E, ‖stableJumpValue α U x‖) ^ 2 +
        (2 / (jumpAveragingWeight α R * R)) * stableJumpForm α U U := by
  have hw := jumpAveragingWeight_pos hα0 hα2 hR
  have h := stableJump_nash_averaging_real hα0 hα2 hR U hu
  have hd : ‖stableJumpValue α U‖ ^ 2 ≤
      (2 * R * stableJumpForm α U U + 2 * jumpAveragingWeight α R *
        (∫ x : E, ‖stableJumpValue α U x‖) ^ 2) / (jumpAveragingWeight α R * R ^ 2) :=
    (le_div_iff₀ (mul_pos hw (sq_pos_of_pos hR))).mpr (by convert h using 1; ring)
  refine hd.trans_eq ?_
  field_simp
  ring

/-- The actual norm interpolation has mass coefficient arbitrarily small for large scales. -/
theorem stableJump_norm_le_mass_energy {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ)) :
    ‖stableJumpValue α U‖ ≤
      Real.sqrt (2 / R ^ 2) * (∫ x : E, ‖stableJumpValue α U x‖) +
        Real.sqrt (2 / (jumpAveragingWeight α R * R)) * Real.sqrt (stableJumpForm α U U) := by
  have hw := jumpAveragingWeight_pos hα0 hα2 hR
  have hE : 0 ≤ stableJumpForm α U U := by rw [stableJumpForm_self]; positivity
  have hM : 0 ≤ ∫ x : E, ‖stableJumpValue α U x‖ :=
    integral_nonneg (fun _ ↦ norm_nonneg _)
  have hs := stableJump_norm_sq_le_mass_energy hα0 hα2 hR U hu
  have hA := Real.sq_sqrt (by positivity : 0 ≤ 2 / R ^ 2)
  have hD := Real.sq_sqrt (by positivity : 0 ≤ 2 / (jumpAveragingWeight α R * R))
  have hEE := Real.sq_sqrt hE
  have hp : 0 ≤ Real.sqrt (2 / R ^ 2) * (∫ x : E, ‖stableJumpValue α U x‖) := by positivity
  have hq : 0 ≤ Real.sqrt (2 / (jumpAveragingWeight α R * R)) *
      Real.sqrt (stableJumpForm α U U) := by positivity
  nlinarith [mul_nonneg hp hq, norm_nonneg (stableJumpValue α U)]

end PartialBalayage.Maximal.Square
