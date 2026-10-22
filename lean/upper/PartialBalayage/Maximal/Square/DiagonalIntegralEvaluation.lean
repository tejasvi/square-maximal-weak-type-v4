/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5; the diagonal integral is 87/7 B(33/40,47/20) - 1404/329 B(33/40,33/40) and the constant is defined by it. -/
module

public import PartialBalayage.Maximal.Square.DiagonalIntegralBoundary
public import PartialBalayage.Maximal.Square.DiagonalIntegralDensity
public import PartialBalayage.Maximal.Square.DiagonalBetaNormalization
public import PartialBalayage.Maximal.Square.DiamondGeneratorHomogeneity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact actual diagonal source evaluation

Ordinary fundamental theorems of calculus apply to the two actual smooth
primitive pieces. The genuine origin and infinity limits cancel, and the
positive-beta identities yield the exact intrinsic radial source constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- The genuine diagonal integral is the exact combination of convergent positive beta integrals. -/
theorem integral_diagonalWeightedDifference_eq_positiveBeta :
    (∫ t in Ioi (0 : ℝ), diagonalWeightedDifference t) =
      (87 / 7 : ℝ) * realBetaIntegral (33 / 40) (47 / 20) -
        (1404 / 329 : ℝ) * realBetaIntegral (33 / 40) (33 / 40) := by
  have hj₀ : IntervalIntegrable diagonalWeightedDifference volume (0 : ℝ) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (integrableOn_diagonalWeightedDifference.mono_set Ioc_subset_Ioi_self)
  have hp₀ : IntervalIntegrable diagonalPlusBetaDensity volume (0 : ℝ) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (integrableOn_diagonalPlusBetaDensity.mono_set Ioc_subset_Ioi_self)
  have hm₀ : IntervalIntegrable diagonalMinusBetaDensity volume (0 : ℝ) (1 / 2) := by
    apply intervalIntegrable_diagonalMinusBetaDensity.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hj₁ : IntegrableOn diagonalWeightedDifference (Ioi (1 / 2 : ℝ)) :=
    integrableOn_diagonalWeightedDifference.mono_set (Ioi_subset_Ioi (by norm_num))
  have hp₁ : IntegrableOn diagonalPlusBetaDensity (Ioi (1 / 2 : ℝ)) :=
    integrableOn_diagonalPlusBetaDensity.mono_set (Ioi_subset_Ioi (by norm_num))
  have hnearInt : IntervalIntegrable (fun t ↦ diagonalWeightedDifference t -
      (87 / 7 : ℝ) * diagonalPlusBetaDensity t + (2808 / 329 : ℝ) * diagonalMinusBetaDensity t)
        volume (0 : ℝ) (1 / 2) :=
    (hj₀.sub (hp₀.const_mul (87 / 7 : ℝ))).add (hm₀.const_mul (2808 / 329 : ℝ))
  have hnearDeriv : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt diagonalNearBoundary
      (diagonalWeightedDifference t - (87 / 7 : ℝ) * diagonalPlusBetaDensity t +
        (2808 / 329 : ℝ) * diagonalMinusBetaDensity t) t := by
    intro t ht
    have hd := hasDerivAt_diagonalNearBoundary ht.1 (by linarith [ht.2])
    simpa only [diagonalWeightedDifference, diagonalDifference, ite_eq_left ht.2.le,
      diagonalNearDifference] using hd
  have hnearHalf : Tendsto diagonalNearBoundary (𝓝[<] (1 / 2 : ℝ))
      (𝓝 (diagonalNearBoundary (1 / 2))) :=
    (hasDerivAt_diagonalNearBoundary (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnear := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1 / 2) hnearDeriv hnearInt
      tendsto_diagonalNearBoundary_zero hnearHalf
  rw [intervalIntegral.integral_add (hj₀.sub (hp₀.const_mul (87 / 7 : ℝ)))
      (hm₀.const_mul (2808 / 329 : ℝ)),
    intervalIntegral.integral_sub hj₀ (hp₀.const_mul (87 / 7 : ℝ)), sub_zero] at hnear
  simp only [intervalIntegral.integral_const_mul] at hnear
  have hfarInt : IntegrableOn (fun t ↦ diagonalWeightedDifference t -
      (87 / 7 : ℝ) * diagonalPlusBetaDensity t) (Ioi (1 / 2 : ℝ)) :=
    hj₁.sub (hp₁.const_mul (87 / 7 : ℝ))
  have hfarDeriv : ∀ t ∈ Ioi (1 / 2 : ℝ), HasDerivAt diagonalFarBoundary
      (diagonalWeightedDifference t - (87 / 7 : ℝ) * diagonalPlusBetaDensity t) t := by
    intro t ht
    have htt : (1 / 2 : ℝ) < t := ht
    have hd := hasDerivAt_diagonalFarBoundary (by linarith : 0 < t)
    simpa only [diagonalWeightedDifference, diagonalDifference,
      ite_eq_right (not_le.mpr htt), diagonalFarDifference] using hd
  have hfarCont : ContinuousWithinAt diagonalFarBoundary (Ici (1 / 2 : ℝ)) (1 / 2) :=
    (hasDerivAt_diagonalFarBoundary
      (by norm_num : (0 : ℝ) < 1 / 2)).continuousAt.continuousWithinAt
  have hfar := integral_Ioi_of_hasDerivAt_of_tendsto
    hfarCont hfarDeriv hfarInt tendsto_diagonalFarBoundary_atTop
  rw [integral_sub hj₁ (hp₁.const_mul (87 / 7 : ℝ)), integral_const_mul, zero_sub] at hfar
  have hjSplit := intervalIntegral.integral_interval_add_Ioi
    integrableOn_diagonalWeightedDifference hj₁
  have hpSplit := intervalIntegral.integral_interval_add_Ioi
    integrableOn_diagonalPlusBetaDensity hp₁
  rw [integral_diagonalPlusBetaDensity] at hpSplit
  rw [integral_diagonalMinusBetaDensity_half, diagonalNearBoundary_half_eq_far] at hnear
  linarith

/-- The actual paired coordinate generator at the fixed diagonal has the intrinsic constant. -/
theorem diamondPairedGenerator_diagonal_eq_intrinsic :
    diamondPairedGenerator (47 / 40) (1 / 2) (1 / 2) = squareIntrinsicConstant := by
  rw [diamondPairedGenerator_diagonal_eq_integral,
    integral_diagonalWeightedDifference_eq_positiveBeta]
  exact diagonal_positiveBeta_normalization

/-- The actual homogeneous paired generator has its exact radial source at every positive point. -/
theorem diamondPairedGenerator_eq_intrinsic {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    diamondPairedGenerator (47 / 40) u v =
      (u + v) ^ (-47 / 20 : ℝ) * squareIntrinsicConstant := by
  rw [diamondPairedGenerator_eq_diagonal
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num : (47 / 40 : ℝ) < 2) hu hv,
      diamondPairedGenerator_diagonal_eq_intrinsic]
  congr 2
  ring

end PartialBalayage.Maximal.Square
