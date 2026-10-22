/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondTruncationTail

/-!
# The actual Euclidean coordinate profiles of the diamond kernel

These identities identify the real coordinate generator's original Euclidean lines with
the genuine scalar profiles, including reflection across either coordinate axis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem coordinateLine_diamondTruncatedPower_zero (α R : ℝ) (x : E) :
    coordinateLine (diamondTruncatedPower α R) x 0 =
      diamondCoordinateTruncatedProfile α R (x 0) |x 1| := by
  funext t
  simp [coordinateLine, diamondTruncatedPower, diamondPower, diamondRadius,
    diamondCoordinateTruncatedProfile, diamondCoordinateProfile, EuclideanSpace.basisFun_apply]

theorem coordinateLine_diamondTruncatedPower_one (α R : ℝ) (x : E) :
    coordinateLine (diamondTruncatedPower α R) x 1 =
      diamondCoordinateTruncatedProfile α R (x 1) |x 0| := by
  funext t
  simp only [coordinateLine, diamondTruncatedPower, diamondPower, diamondRadius,
    diamondCoordinateTruncatedProfile, diamondCoordinateProfile, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.basisFun_apply]
  norm_num
  rw [add_comm |x 0|]

/-- Actual reflection preserves the original symmetric coordinate second difference. -/
theorem diamondCoordinateTruncatedSecondDifference_reflection (α R u v t : ℝ) :
    stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      stableSecondDifference (diamondCoordinateTruncatedProfile α R |u| v) t := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · have he₁ : -u + t = -(u + -t) := by ring
    have he₂ : -u + -t = -(u + t) := by ring
    have he₀ : -u + 0 = -(u + 0) := by ring
    simp only [stableSecondDifference, diamondCoordinateTruncatedProfile,
      diamondCoordinateProfile, abs_of_neg (lt_of_not_ge hu), smul_eq_mul]
    rw [he₁, he₂, he₀, abs_neg, abs_neg, abs_neg]
    ring

/-- The genuine physical coordinate difference uses absolute coordinates on both axes. -/
theorem coordinateSecondDifference_diamondTruncatedPower (α R : ℝ) (x : E)
    (i : Fin 2) (t : ℝ) :
    stableSecondDifference (coordinateLine (diamondTruncatedPower α R) x i) t =
      stableSecondDifference (diamondCoordinateTruncatedProfile α R |x i| |x (1 - i)|) t := by
  fin_cases i
  · change stableSecondDifference (coordinateLine (diamondTruncatedPower α R) x 0) t =
      stableSecondDifference (diamondCoordinateTruncatedProfile α R |x 0| |x 1|) t
    rw [coordinateLine_diamondTruncatedPower_zero,
      diamondCoordinateTruncatedSecondDifference_reflection]
  · change stableSecondDifference (coordinateLine (diamondTruncatedPower α R) x 1) t =
      stableSecondDifference (diamondCoordinateTruncatedProfile α R |x 1| |x 0|) t
    rw [coordinateLine_diamondTruncatedPower_one,
      diamondCoordinateTruncatedSecondDifference_reflection]

end PartialBalayage.Maximal.Square
