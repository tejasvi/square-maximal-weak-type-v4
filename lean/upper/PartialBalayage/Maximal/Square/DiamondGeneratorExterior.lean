/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5. -/
module

public import PartialBalayage.Maximal.Square.DiamondCoordinateProfiles
public import PartialBalayage.Maximal.Square.DiamondGeneratorBasic

/-!
# Genuine strict exterior coordinate integrability

The truncated radial profile vanishes for sufficiently small jumps in the strict exterior.
Its positive transverse coordinate bounds every remaining jump, giving the actual integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem diamondCoordinateTruncatedProfile_eq_zero_of_radius_le {α R u v s : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hr : R ≤ |u + s| + v) :
    diamondCoordinateTruncatedProfile α R u v s = 0 := by
  have hp := Real.rpow_le_rpow_of_nonpos hR hr (neg_nonpos.mpr hα)
  exact max_eq_right (sub_nonpos.mpr hp)

private theorem norm_diamondCoordinateTruncatedProfile_le {α R v : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hv : 0 < v) (u s : ℝ) :
    ‖diamondCoordinateTruncatedProfile α R u v s‖ ≤ v ^ (-α) := by
  have hpow : 0 ≤ diamondCoordinateProfile α u v s := Real.rpow_nonneg (by positivity) _
  have hm : diamondCoordinateTruncatedProfile α R u v s ≤ diamondCoordinateProfile α u v s :=
    max_le (sub_le_self _ (Real.rpow_nonneg hR.le _)) hpow
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have hp := norm_diamondCoordinateProfile_le hα hv u s
  rw [Real.norm_eq_abs, abs_of_nonneg hpow] at hp
  exact hm.trans hp

private theorem diamondCoordinateTruncatedSecondDifference_eq_zero_exterior
    {α R u v t : ℝ} (hα : 0 ≤ α) (hR : 0 < R) (hu : 0 ≤ u)
    (ht : 0 ≤ t) (htr : t ≤ u + v - R) :
    stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t = 0 := by
  have hp : R ≤ |u + t| + v := by linarith [le_abs_self (u + t)]
  have hn : R ≤ |u + -t| + v := by linarith [le_abs_self (u + -t)]
  have h₀ : R ≤ |u + 0| + v := by simpa only [add_zero, abs_of_nonneg hu] using
    (show R ≤ u + v by linarith)
  simp only [stableSecondDifference,
    diamondCoordinateTruncatedProfile_eq_zero_of_radius_le hα hR hp,
    diamondCoordinateTruncatedProfile_eq_zero_of_radius_le hα hR hn,
    diamondCoordinateTruncatedProfile_eq_zero_of_radius_le hα hR h₀,
    add_zero, smul_zero, sub_self]

/-- The original exterior scalar coordinate integral converges without a source certificate. -/
theorem integrableOn_diamondCoordinateTruncatedSecondDifference_exterior {α R u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (hu : 0 ≤ u) (hv : 0 < v)
    (hr : R < u + v) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) *
      stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t) (Ioi 0) := by
  apply integrable_stable_weighted_difference (M₂ := 0) (M₀ := v ^ (-α))
    hα0 hα2 (sub_pos.mpr hr) (stableSecondDifference (diamondCoordinateTruncatedProfile α R u v))
  · apply (continuous_stableSecondDifference ?_).aestronglyMeasurable
    unfold diamondCoordinateTruncatedProfile diamondCoordinateProfile
    apply (Continuous.sub ?_ continuous_const).max continuous_const
    apply Continuous.rpow_const
      ((continuous_abs.comp (continuous_const.add continuous_id)).add continuous_const)
    intro t
    left
    exact ne_of_gt (by change 0 < |u + t| + v; positivity)
  · intro t ht
    rw [diamondCoordinateTruncatedSecondDifference_eq_zero_exterior hα0.le hR hu ht.1.le ht.2]
    simp only [norm_zero, zero_mul, le_refl]
  · intro t _
    exact norm_stableSecondDifference_le_four
      (norm_diamondCoordinateTruncatedProfile_le hα0.le hR hv u) t

/-- The original Euclidean radial coordinate integral exists off the axes and support boundary. -/
theorem integrableOn_coordinateDiamondSecondDifference {x : E} (hx₀ : x 0 ≠ 0)
    (hx₁ : x 1 ≠ 0) (hr : diamondRadius (x 0) (x 1) ≠ supportRadius) (i : Fin 2) :
    IntegrableOn (fun t ↦ t ^ (-1 - (47 / 40 : ℝ)) * stableSecondDifference
      (coordinateLine (diamondTruncatedPower (47 / 40) supportRadius) x i) t) (Ioi 0) := by
  have hu : 0 < |x i| := by fin_cases i <;> exact abs_pos.mpr (by assumption)
  have hv : 0 < |x (1 - i)| := by fin_cases i <;> exact abs_pos.mpr (by assumption)
  have he : |x i| + |x (1 - i)| = diamondRadius (x 0) (x 1) := by
    fin_cases i
    · rfl
    · change |x 1| + |x 0| = |x 0| + |x 1|
      ring
  have hi : IntegrableOn (fun t ↦ t ^ (-1 - (47 / 40 : ℝ)) * stableSecondDifference
      (diamondCoordinateTruncatedProfile (47 / 40) supportRadius |x i| |x (1 - i)|) t)
        (Ioi 0) := by
    rcases hr.lt_or_gt with hlt | hgt
    · exact integrableOn_diamondCoordinateTruncatedSecondDifference (by norm_num) (by norm_num)
        supportRadius_pos hu hv (by simpa only [he] using hlt)
    · exact integrableOn_diamondCoordinateTruncatedSecondDifference_exterior
        (by norm_num) (by norm_num) supportRadius_pos hu.le hv (by simpa only [he] using hgt)
  apply hi.congr
  filter_upwards with t
  rw [coordinateSecondDifference_diamondTruncatedPower]

end PartialBalayage.Maximal.Square
