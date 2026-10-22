/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 (weight t^(-87/40); beta parameters 33/40 and 47/20). -/
module

public import PartialBalayage.Maximal.Square.DiagonalBetaPrimitives

/-!
# Genuine diagonal density and positive-beta integrals

The actual coordinate stable integral at the diagonal has its explicit
crossing formula. The positive beta densities have their true convergent
integrals and exact half-interval symmetry.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

/-- The actual diagonal second difference across the coordinate-axis crossing. -/
def diagonalDifference (t : ℝ) : ℝ :=
  (1 + t) ^ (-47 / 40 : ℝ) +
    (if t ≤ 1 / 2 then (1 - t) ^ (-47 / 40 : ℝ) else t ^ (-47 / 40 : ℝ)) - 2

/-- The genuine weighted diagonal singular integrand. -/
def diagonalWeightedDifference (t : ℝ) : ℝ := t ^ (-87 / 40 : ℝ) * diagonalDifference t

theorem diagonalSecondDifference_eq {t : ℝ} (ht : 0 < t) :
    stableSecondDifference (diamondCoordinateProfile (47 / 40) (1 / 2) (1 / 2)) t =
      diagonalDifference t := by
  rw [diamondCoordinateProfile_secondDifference_pos (by norm_num) ht]
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring, Real.one_rpow, mul_one,
    show -(47 / 40 : ℝ) = -47 / 40 by ring]
  unfold diagonalDifference
  split_ifs with h
  · rw [abs_of_nonneg (by linarith : 0 ≤ (1 / 2 : ℝ) - t),
      show (1 / 2 : ℝ) - t + 1 / 2 = 1 - t by ring,
      show -(47 / 40 : ℝ) = -47 / 40 by ring]
  · rw [abs_of_neg (by linarith : (1 / 2 : ℝ) - t < 0),
      show -((1 / 2 : ℝ) - t) + 1 / 2 = t by ring,
      show -(47 / 40 : ℝ) = -47 / 40 by ring]

theorem integrableOn_diagonalWeightedDifference :
    IntegrableOn diagonalWeightedDifference (Ioi 0) := by
  have hi := integrableOn_diamondCoordinateSecondDifference
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num : (47 / 40 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro t ht
  change t ^ (-1 - (47 / 40 : ℝ)) *
    stableSecondDifference (diamondCoordinateProfile (47 / 40) (1 / 2) (1 / 2)) t =
      diagonalWeightedDifference t
  rw [diagonalSecondDifference_eq ht,
    show (-1 : ℝ) - 47 / 40 = -87 / 40 by ring]
  rfl

theorem diamondPairedGenerator_diagonal_eq_integral :
    diamondPairedGenerator (47 / 40) (1 / 2) (1 / 2) =
      2 * ∫ t in Ioi (0 : ℝ), diagonalWeightedDifference t := by
  unfold diamondPairedGenerator
  rw [show diamondCoordinateIntegral (47 / 40) (1 / 2) (1 / 2) +
      diamondCoordinateIntegral (47 / 40) (1 / 2) (1 / 2) =
        2 * diamondCoordinateIntegral (47 / 40) (1 / 2) (1 / 2) by ring]
  congr 1
  unfold diamondCoordinateIntegral stableGeneratorIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change t ^ (-1 - (47 / 40 : ℝ)) *
    stableSecondDifference (diamondCoordinateProfile (47 / 40) (1 / 2) (1 / 2)) t =
      diagonalWeightedDifference t
  rw [diagonalSecondDifference_eq ht,
    show (-1 : ℝ) - 47 / 40 = -87 / 40 by ring]
  rfl

theorem integrableOn_diagonalPlusBetaDensity :
    IntegrableOn diagonalPlusBetaDensity (Ioi 0) := by
  have hi := integrableOn_betaPrime (by norm_num : (0 : ℝ) < 33 / 40)
    (by norm_num : (0 : ℝ) < 47 / 20)
  unfold diagonalPlusBetaDensity
  simpa only [show (33 / 40 : ℝ) - 1 = -7 / 40 by ring,
    show -((33 / 40 : ℝ) + 47 / 20) = -127 / 40 by ring] using hi

theorem integral_diagonalPlusBetaDensity :
    (∫ t in Ioi (0 : ℝ), diagonalPlusBetaDensity t) = realBetaIntegral (33 / 40) (47 / 20) := by
  simpa only [diagonalPlusBetaDensity, show (33 / 40 : ℝ) - 1 = -7 / 40 by ring,
    show -((33 / 40 : ℝ) + 47 / 20) = -127 / 40 by ring] using
      integral_betaPrime (33 / 40 : ℝ) (47 / 20 : ℝ)

theorem intervalIntegrable_diagonalMinusBetaDensity :
    IntervalIntegrable diagonalMinusBetaDensity volume 0 1 := by
  have hi := intervalIntegrable_realBetaIntegrand (by norm_num : (0 : ℝ) < 33 / 40)
    (by norm_num : (0 : ℝ) < 33 / 40)
  unfold realBetaIntegrand at hi
  unfold diagonalMinusBetaDensity
  simpa only [show (33 / 40 : ℝ) - 1 = -7 / 40 by ring] using hi

theorem diagonalMinusBetaDensity_sub (t : ℝ) :
    diagonalMinusBetaDensity (1 - t) = diagonalMinusBetaDensity t := by
  simp only [diagonalMinusBetaDensity, sub_sub_cancel, mul_comm]

/-- The actual half-interval negative-power beta density has half the true beta mass. -/
theorem integral_diagonalMinusBetaDensity_half :
    (∫ t in (0 : ℝ)..(1 / 2), diagonalMinusBetaDensity t) =
      realBetaIntegral (33 / 40) (33 / 40) / 2 := by
  have hi := intervalIntegrable_diagonalMinusBetaDensity
  have h₀ : IntervalIntegrable diagonalMinusBetaDensity volume (0 : ℝ) (1 / 2) := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have h₁ : IntervalIntegrable diagonalMinusBetaDensity volume (1 / 2 : ℝ) 1 := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hs := intervalIntegral.integral_comp_sub_left diagonalMinusBetaDensity 1
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
  simp only [diagonalMinusBetaDensity_sub] at hs
  norm_num only at hs
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₀ h₁
  have he : realBetaIntegral (33 / 40) (33 / 40) =
      ∫ t in (0 : ℝ)..1, diagonalMinusBetaDensity t := by
    simp only [realBetaIntegral, realBetaIntegrand, diagonalMinusBetaDensity,
      show (33 / 40 : ℝ) - 1 = -7 / 40 by ring]
  rw [he]
  linarith

end PartialBalayage.Maximal.Square
