/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 and spline scale 32 instead of 16; compact support of the correction comes from the box lemma in Kernel via Integrability. -/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCoefficients
public import PartialBalayage.Maximal.Square.SplineGeneratorScaling
public import PartialBalayage.Maximal.Square.KernelGeneratorSymmetry
public import PartialBalayage.Maximal.Square.Data.GeneratorScaleData
public import PartialBalayage.Maximal.Square.Integrability
public import PartialBalayage.Maximal.Square.GeneratorAlgebra

/-!
# The actual tensor spline correction's stable source

The finite signed tensor sum has its genuine physical-space generator, with
its exact normalization and scale. Compact C² self-adjointness then gives its
unconditional distributional source identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

-- Elaborating membership in the index box can reduce `List.range 141`, deeper than the
-- default recursion limit.
set_option maxRecDepth 20000

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- One actual two-dimensional tensor entry, with its physical mesh scale. -/
def tensorSpline (p : ℤ × ℤ) (x : E) : ℝ :=
  cubicSpline (32 * x 0 - p.1) * cubicSpline (32 * x 1 - p.2)

theorem tensorSpline_contDiff (p : ℤ × ℤ) : ContDiff ℝ 2 (tensorSpline p) := by
  have hcoord (i : Fin 2) : ContDiff ℝ 2 (fun x : E ↦ x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).contDiff
  exact (contDiff_two_cubicSpline.comp
    (contDiff_const.mul (hcoord 0) |>.sub contDiff_const)).mul
    (contDiff_two_cubicSpline.comp
      (contDiff_const.mul (hcoord 1) |>.sub contDiff_const))

theorem tensorSpline_hasCompactSupport (p : ℤ × ℤ) : HasCompactSupport (tensorSpline p) := by
  let R : ℝ := (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 4) / 32
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R)
  intro x hx
  have hu : |32 * x 0 - (p.1 : ℝ)| < 2 := by
    by_contra h
    apply hx
    unfold tensorSpline
    rw [cubicSpline_eq_zero_of_two_le_abs (le_of_not_gt h), zero_mul]
  have hv : |32 * x 1 - (p.2 : ℝ)| < 2 := by
    by_contra h
    apply hx
    unfold tensorSpline
    rw [cubicSpline_eq_zero_of_two_le_abs (le_of_not_gt h), mul_zero]
  have hau : |32 * x 0| ≤ |32 * x 0 - (p.1 : ℝ)| + |(p.1 : ℝ)| := by
    simpa only [sub_add_cancel] using abs_add_le (32 * x 0 - (p.1 : ℝ)) (p.1 : ℝ)
  have hav : |32 * x 1| ≤ |32 * x 1 - (p.2 : ℝ)| + |(p.2 : ℝ)| := by
    simpa only [sub_add_cancel] using abs_add_le (32 * x 1 - (p.2 : ℝ)) (p.2 : ℝ)
  norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)] at hau hav
  apply mem_closedBall_zero_iff.mpr
  have hn := norm_le_diamondRadius x
  unfold diamondRadius at hn
  dsimp [R]
  linarith

/-- Finite additivity uses the genuine singular-integral integrability of each entry. -/
theorem coordinateStableGenerator_finsetSum {ι : Type*} (s : Finset ι)
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (F : ι → E → ℝ)
    (hF : ∀ j ∈ s, ContDiff ℝ 2 (F j)) (hs : ∀ j ∈ s, HasCompactSupport (F j)) (x : E) :
    coordinateStableGenerator α (fun y ↦ ∑ j ∈ s, F j y) x =
      ∑ j ∈ s, coordinateStableGenerator α (F j) x := by
  have he (i : Fin 2) :
      stableGeneratorIntegral α (coordinateLine (fun y ↦ ∑ j ∈ s, F j y) x i) =
        ∑ j ∈ s, stableGeneratorIntegral α (coordinateLine (F j) x i) := by
    unfold stableGeneratorIntegral
    calc
      _ = ∫ t in Ioi 0, ∑ j ∈ s,
          t ^ (-1 - α) • stableSecondDifference (coordinateLine (F j) x i) t := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [stableSecondDifference, coordinateLine, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := integral_finsetSum s fun j hj ↦
        integrableOn_coordinateStableSecondDifference hα0 hα2 (hF j hj) (hs j hj) x i
  unfold coordinateStableGenerator
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Each actual tensor has the exact stable generator in both coordinate directions. -/
theorem coordinateStableGenerator_tensorSpline (p : ℤ × ℤ) (x : E) :
    coordinateStableGenerator (47 / 40 : ℝ) (tensorSpline p) x =
      stableNormalization (47 / 40 : ℝ) * splineGeneratorFactor *
        (cubicSpline (32 * x 1 - p.2) * splineGeneratorPower (32 * x 0 - p.1) +
          cubicSpline (32 * x 0 - p.1) * splineGeneratorPower (32 * x 1 - p.2)) := by
  have h0 : coordinateLine (tensorSpline p) x 0 = fun t : ℝ ↦
      cubicSpline (32 * x 1 - p.2) * cubicSpline ((32 * x 0 - p.1) + 32 * t) := by
    funext t
    simp only [coordinateLine, tensorSpline, PiLp.add_apply, PiLp.smul_apply,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
    simp only [ite_true, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0),
      mul_one, mul_zero, add_zero, smul_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  have h1 : coordinateLine (tensorSpline p) x 1 = fun t : ℝ ↦
      cubicSpline (32 * x 0 - p.1) * cubicSpline ((32 * x 1 - p.2) + 32 * t) := by
    funext t
    simp only [coordinateLine, tensorSpline, PiLp.add_apply, PiLp.smul_apply,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
    simp only [ite_true, ite_eq_right (by decide : ¬ (0 : Fin 2) = 1),
      mul_one, mul_zero, add_zero, smul_eq_mul]
    congr 1
    congr 1
    ring
  unfold coordinateStableGenerator
  rw [Fin.sum_univ_two, h0, h1, stableGeneratorIntegral_const_mul,
    stableGeneratorIntegral_const_mul, stableGeneratorIntegral_cubicSpline_thirtyTwo,
    stableGeneratorIntegral_cubicSpline_thirtyTwo]
  unfold splineGeneratorFactor
  ring

/-- The actual signed correction is a genuine compact C² Euclidean function. -/
theorem contDiff_splineCorrection :
    ContDiff ℝ 2 (fun x : E ↦ splineCorrection (x 0) (x 1)) := by
  have he : (fun x : E ↦ splineCorrection (x 0) (x 1)) =
      fun x ↦ ∑ p ∈ splineCoefficientBox, (splineCoefficient p.1 p.2 : ℝ) * tensorSpline p x := by
    funext x
    exact splineCorrection_eq_coefficientBox _ _
  rw [he]
  exact ContDiff.sum fun p hp ↦ contDiff_const.mul (tensorSpline_contDiff p)

/-- The physical correction source equals the exact coefficient potential and scale. -/
theorem coordinateStableGenerator_splineCorrection (x : E) :
    coordinateStableGenerator (47 / 40 : ℝ) (fun y : E ↦ splineCorrection (y 0) (y 1)) x =
      stableNormalization (47 / 40 : ℝ) * splineGeneratorFactor *
        splineGeneratorCorrectionPower (32 * x 0) (32 * x 1) := by
  have he : (fun y : E ↦ splineCorrection (y 0) (y 1)) =
      fun y ↦ ∑ p ∈ splineCoefficientBox, (splineCoefficient p.1 p.2 : ℝ) * tensorSpline p y := by
    funext y
    exact splineCorrection_eq_coefficientBox _ _
  rw [he, coordinateStableGenerator_finsetSum splineCoefficientBox (by norm_num) (by norm_num)
    (fun p y ↦ (splineCoefficient p.1 p.2 : ℝ) * tensorSpline p y)
    (fun p hp ↦ contDiff_const.mul (tensorSpline_contDiff p))
    (fun p hp ↦ (tensorSpline_hasCompactSupport p).mul_left)]
  simp_rw [coordinateStableGenerator_const_mul, coordinateStableGenerator_tensorSpline]
  unfold splineGeneratorCorrectionPower
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The actual correction density pairs integrably with every compact C² test. -/
theorem integrable_compact_test_mul_splineGeneratorCorrection {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    Integrable (fun x ↦ φ x * (stableNormalization (47 / 40 : ℝ) * splineGeneratorFactor *
      splineGeneratorCorrectionPower (32 * x 0) (32 * x 1))) volume := by
  apply (integrable_kernel_mul_coordinateStableGenerator_compactC2
    (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num : (47 / 40 : ℝ) < 2)
    (hφ.continuous.integrable_of_hasCompactSupport hs)
    contDiff_splineCorrection hasCompactSupport_splineCorrection).congr
  filter_upwards with x
  rw [coordinateStableGenerator_splineCorrection]

/-- The true distributional correction source has no smoothness or pairing certificate. -/
theorem integral_splineCorrection_coordinateStableGenerator {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, splineCorrection (x 0) (x 1) * coordinateStableGenerator (47 / 40 : ℝ) φ x) =
      ∫ x, φ x * (stableNormalization (47 / 40 : ℝ) * splineGeneratorFactor *
        splineGeneratorCorrectionPower (32 * x 0) (32 * x 1)) := by
  rw [integral_coordinateStableGenerator_compactC2_symmetry (by norm_num) (by norm_num)
    contDiff_splineCorrection hasCompactSupport_splineCorrection hφ hs]
  apply integral_congr_ae
  filter_upwards with x
  rw [coordinateStableGenerator_splineCorrection]

end PartialBalayage.Maximal.Square
