/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5; the compact support of the spline part comes
from the box lemma `splineCorrection_eq_zero_of_box` (support in `closedBall 0 (9/2)`). -/
module

public import PartialBalayage.Maximal.Square.Kernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Genuine integrability of the anisotropic square kernel

The diamond singularity is dominated by the Euclidean power of order 47/40 in
dimension two. Its exact compact support and the actual continuous spline correction
then give whole-plane Lebesgue integrability, without a certificate hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The Euclidean norm is bounded by the actual diamond radius. -/
theorem norm_le_diamondRadius (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ diamondRadius (x 0) (x 1) := by
  have hs := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two] at hs
  have hx := abs_nonneg (x 0)
  have hy := abs_nonneg (x 1)
  have hxy : 0 ≤ |x 0| * |x 1| := mul_nonneg hx hy
  have hnx := norm_nonneg x
  have hsqx := sq_abs (x 0)
  have hsqy := sq_abs (x 1)
  unfold diamondRadius
  nlinarith

/-- Exact diamond support implies a genuine compact Euclidean support. -/
theorem support_radialBase_subset_closedBall :
    Function.support (fun x : EuclideanSpace ℝ (Fin 2) ↦ radialBase (x 0) (x 1)) ⊆
      Metric.closedBall 0 supportRadius := by
  intro x hx
  have hr : diamondRadius (x 0) (x 1) < supportRadius := by
    by_contra h
    exact hx (radialBase_eq_zero_of_supportRadius_le (le_of_not_gt h))
  exact mem_closedBall_zero_iff.mpr ((norm_le_diamondRadius x).trans hr.le)

/-- The actual spline correction has compact Euclidean support. -/
theorem hasCompactSupport_splineCorrection :
    HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 2) ↦ splineCorrection (x 0) (x 1)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (9 / 2))
  intro x hx
  have hr : diamondRadius (x 0) (x 1) < 9 / 2 := by
    by_contra h
    apply hx
    apply splineCorrection_eq_zero_of_box
    unfold diamondRadius at h
    by_contra h'
    push Not at h'
    linarith [h'.1, h'.2]
  exact mem_closedBall_zero_iff.mpr ((norm_le_diamondRadius x).trans hr.le)

/-- The actual singular radial base is measurable on the whole plane. -/
theorem measurable_radialBase :
    Measurable (fun x : EuclideanSpace ℝ (Fin 2) ↦ radialBase (x 0) (x 1)) := by
  unfold radialBase diamondRadius
  fun_prop

/-- The exact radial singularity has the subcritical Euclidean decay bound. -/
theorem radialBase_norm_le_euclidean_rpow (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    ‖radialBase (x 0) (x 1)‖ ≤ radialCoefficient * ‖x‖ ^ (-(47 / 40 : ℝ)) := by
  have hr : 0 ≤ diamondRadius (x 0) (x 1) := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp := Real.rpow_le_rpow_of_nonpos hn (norm_le_diamondRadius x)
    (by norm_num : -(47 / 40 : ℝ) ≤ 0)
  have hbase : max ((diamondRadius (x 0) (x 1)) ^ (-(47 / 40 : ℝ)) -
      supportRadius ^ (-(47 / 40 : ℝ))) 0 ≤
        (diamondRadius (x 0) (x 1)) ^ (-(47 / 40 : ℝ)) := by
    apply max_le
    · exact sub_le_self _ (Real.rpow_nonneg supportRadius_pos.le _)
    · exact Real.rpow_nonneg hr _
  rw [Real.norm_eq_abs, abs_of_nonneg (radialBase_nonneg _ _)]
  unfold radialBase
  exact mul_le_mul_of_nonneg_left (hbase.trans hp) radialCoefficient_pos.le

/-- The singular radial base is genuinely locally integrable at its origin. -/
theorem locallyIntegrable_radialBase :
    LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin 2) ↦ radialBase (x 0) (x 1)) := by
  exact locallyIntegrable_of_norm_le_rpow (α := (47 / 40 : ℝ)) (C := radialCoefficient)
    (hdim := by norm_num) (hα := by norm_num)
    (h_decay := by
      filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin 2))] with x hx
      exact radialBase_norm_le_euclidean_rpow x hx)
    measurable_radialBase.aestronglyMeasurable

/-- Compact support upgrades the actual radial base to whole-plane integrability. -/
theorem integrable_radialBase :
    Integrable (fun x : EuclideanSpace ℝ (Fin 2) ↦ radialBase (x 0) (x 1)) := by
  apply (integrableOn_iff_integrable_of_support_subset
    support_radialBase_subset_closedBall).mp
  exact locallyIntegrable_radialBase.integrableOn_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) supportRadius)

/-- The genuine finite signed spline correction is integrable. -/
theorem integrable_splineCorrection :
    Integrable (fun x : EuclideanSpace ℝ (Fin 2) ↦ splineCorrection (x 0) (x 1)) :=
  continuous_splineCorrection.integrable_of_hasCompactSupport hasCompactSupport_splineCorrection

/-- The point value chosen at the origin leaves the actual kernel unchanged almost everywhere. -/
theorem euclideanKernel_ae_eq : euclideanKernel =ᵐ[volume]
    (fun x : EuclideanSpace ℝ (Fin 2) ↦ radialBase (x 0) (x 1) +
      splineCorrection (x 0) (x 1)) := by
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin 2))] with x hx
  have hnot : ¬ (x 0 = 0 ∧ x 1 = 0) := by
    rintro ⟨h₀, h₁⟩
    apply hx
    ext i
    fin_cases i <;> simp [h₀, h₁]
  exact ite_eq_right hnot

/-- The concrete frozen square comparison kernel is Lebesgue integrable. -/
theorem integrable_euclideanKernel : Integrable euclideanKernel :=
  (integrable_radialBase.add integrable_splineCorrection).congr euclideanKernel_ae_eq.symm

end PartialBalayage.Maximal.Square
