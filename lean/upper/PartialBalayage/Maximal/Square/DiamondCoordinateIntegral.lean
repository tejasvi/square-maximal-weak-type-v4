/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RadialLocalSecondDifference

/-!
# Genuine coordinate integrals of the diamond power

Each coordinate profile is bounded when its other coordinate is positive. The actual
small-jump second difference agrees with a smooth positive shifted power. Its local
quadratic estimate proves convergence despite the real cusp at the crossing axis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped NNReal

namespace PartialBalayage.Maximal.Square

/-- The actual coordinate profile of the homogeneous diamond power. -/
def diamondCoordinateProfile (α u v s : ℝ) : ℝ := (|u + s| + v) ^ (-α)

/-- The genuine unnormalized coordinate generator integral. -/
def diamondCoordinateIntegral (α u v : ℝ) : ℝ :=
  stableGeneratorIntegral α (diamondCoordinateProfile α u v)

/-- The actual sum of the two coordinate contributions. -/
def diamondPairedGenerator (α u v : ℝ) : ℝ :=
  diamondCoordinateIntegral α u v + diamondCoordinateIntegral α v u

/-- The true coordinate profile is globally bounded away from its other coordinate's axis. -/
theorem norm_diamondCoordinateProfile_le {α v : ℝ} (hα : 0 ≤ α) (hv : 0 < v)
    (u s : ℝ) : ‖diamondCoordinateProfile α u v s‖ ≤ v ^ (-α) := by
  have hp : 0 ≤ |u + s| + v := by positivity
  rw [diamondCoordinateProfile, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp _)]
  exact Real.rpow_le_rpow_of_nonpos hv (by linarith [abs_nonneg (u + s)])
    (neg_nonpos.mpr hα)

/-- Actual sufficiently small coordinate jumps coincide with the smooth radial second difference. -/
theorem diamondCoordinateProfile_secondDifference_small {α u v t : ℝ}
    (hu : 0 < u) (ht : 0 ≤ t) (htu : t ≤ u) :
    stableSecondDifference (diamondCoordinateProfile α u v) t =
      (u + v + t) ^ (-α) + (u + v - t) ^ (-α) - 2 * (u + v) ^ (-α) := by
  have hup : 0 ≤ u + t := by linarith
  have hun : 0 ≤ u + -t := by linarith
  simp only [stableSecondDifference, diamondCoordinateProfile, abs_of_nonneg hup,
    abs_of_nonneg hun, add_zero, abs_of_pos hu, smul_eq_mul]
  congr 2 <;> congr 1 <;> ring

/-- The actual coordinate stable integral converges at every strict positive quadrant point. -/
theorem integrableOn_diamondCoordinateSecondDifference {α u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) *
      stableSecondDifference (diamondCoordinateProfile α u v) t) (Ioi 0) := by
  obtain ⟨C, hC⟩ := exists_quadratic_shifted_negative_power hα0 (add_pos hu hv)
  let ρ := min u ((u + v) / 2)
  have hρ : 0 < ρ := lt_min hu (by positivity)
  apply integrable_stable_weighted_difference hα0 hα2 hρ
    (stableSecondDifference (diamondCoordinateProfile α u v)) (by
      apply continuous_stableSecondDifference
        (hφ := (show Continuous (diamondCoordinateProfile α u v) from ?_))
          |>.aestronglyMeasurable
      unfold diamondCoordinateProfile
      apply Continuous.rpow_const
        ((continuous_abs.comp (continuous_const.add continuous_id)).add continuous_const)
      intro t
      left
      apply ne_of_gt
      change 0 < |u + t| + v
      linarith [abs_nonneg (u + t)])
  · intro t ht
    rw [diamondCoordinateProfile_secondDifference_small hu ht.1.le
      (ht.2.trans (min_le_left _ _))]
    exact hC t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  · intro t _
    exact norm_stableSecondDifference_le_four
      (fun s ↦ norm_diamondCoordinateProfile_le hα0.le hv u s) t

/-- The genuine symmetric coordinate difference has the explicit positive-quadrant form. -/
theorem diamondCoordinateProfile_secondDifference_pos {α u v t : ℝ}
    (hu : 0 < u) (ht : 0 < t) :
    stableSecondDifference (diamondCoordinateProfile α u v) t =
      (u + v + t) ^ (-α) + (|u - t| + v) ^ (-α) - 2 * (u + v) ^ (-α) := by
  simp only [stableSecondDifference, diamondCoordinateProfile, add_zero,
    abs_of_pos hu, abs_of_pos (add_pos hu ht), smul_eq_mul, ← sub_eq_add_neg]
  congr 2
  congr 1
  ring

/-- The actual coordinate sum equals the genuinely convergent paired integral. -/
theorem diamondPairedGenerator_eq_integral {α u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hu : 0 < u) (hv : 0 < v) :
    diamondPairedGenerator α u v = ∫ t in Ioi 0, t ^ (-1 - α) *
      (2 * (u + v + t) ^ (-α) + (|u - t| + v) ^ (-α) +
        (u + |v - t|) ^ (-α) - 4 * (u + v) ^ (-α)) := by
  unfold diamondPairedGenerator diamondCoordinateIntegral stableGeneratorIntegral
  simp only [smul_eq_mul]
  rw [← integral_add (integrableOn_diamondCoordinateSecondDifference hα0 hα2 hu hv)
    (integrableOn_diamondCoordinateSecondDifference hα0 hα2 hv hu)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [diamondCoordinateProfile_secondDifference_pos hu ht,
    diamondCoordinateProfile_secondDifference_pos hv ht,
    add_comm v u, add_comm (|v - t|) u]
  ring

end PartialBalayage.Maximal.Square
