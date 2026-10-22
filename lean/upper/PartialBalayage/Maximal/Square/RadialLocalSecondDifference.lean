/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondAngularKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Actual local power and second-difference bounds

A genuine local Lipschitz first derivative suffices for the small-jump quadratic estimate.
Negative powers have explicit Lipschitz constants on every half-line bounded away from zero.
These facts control the true diamond singular integrals without globally smoothing their axes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped NNReal

namespace PartialBalayage.Maximal.Square

/-- The genuine negative-power Lipschitz constant away from the origin. -/
def negativePowerLipConst (p δ : ℝ) (hp : p ≤ 0) (hδ : 0 < δ) : ℝ≥0 :=
  ⟨(-p) * δ ^ (p - 1), mul_nonneg (neg_nonneg.mpr hp) (Real.rpow_nonneg hδ.le _)⟩

theorem lipschitzOnWith_rpow_nonpos_Ici {p δ : ℝ} (hp : p ≤ 0) (hδ : 0 < δ) :
    LipschitzOnWith (negativePowerLipConst p δ hp hδ) (fun x : ℝ ↦ x ^ p) (Ici δ) := by
  apply (convex_Ici δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x ↦ p * x ^ (p - 1))
  · intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hδ.trans_le hx)))).hasDerivWithinAt
  · intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, norm_mul, Real.norm_eq_abs,
      abs_of_nonpos hp, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans hx) _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδ hx (by linarith : p - 1 ≤ 0))
        (neg_nonneg.mpr hp)

/-- Actual derivatives and a local Lipschitz bound give the true quadratic cancellation. -/
theorem norm_stableSecondDifference_le_quadratic_on {φ φ' : ℝ → ℝ} {r t : ℝ}
    {K : ℝ≥0} (hφ : ∀ s ∈ Icc (-r) r, HasDerivAt φ (φ' s) s)
    (hφ' : LipschitzOnWith K φ' (Icc (-r) r)) (ht : 0 ≤ t) (htr : t ≤ r) :
    ‖stableSecondDifference φ t‖ ≤ 2 * (K : ℝ) * t ^ 2 := by
  have hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt (stableSecondDifference φ)
      (φ' s - φ' (-s)) (Icc 0 t) s := by
    intro s hs
    have hsr : s ∈ Icc (-r) r := ⟨by linarith [hs.1], hs.2.trans htr⟩
    have hnr : -s ∈ Icc (-r) r := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hneg := (hφ (-s) hnr).scomp s (hasDerivAt_id s).neg
    have hadd := ((hφ s hsr).add hneg).sub_const ((2 : ℝ) • φ 0)
    change HasDerivWithinAt (fun s ↦ φ s + φ (-s) - (2 : ℝ) • φ 0)
      (φ' s - φ' (-s)) (Icc 0 t) s
    simpa only [Pi.add_apply, Function.comp_apply, neg_smul, one_smul, sub_eq_add_neg] using
      hadd.hasDerivWithinAt
  have hb : ∀ s ∈ Ico 0 t, ‖φ' s - φ' (-s)‖ ≤ 2 * (K : ℝ) * t := by
    intro s hs
    have hsr : s ∈ Icc (-r) r := ⟨by linarith [hs.1], hs.2.le.trans htr⟩
    have hnr : -s ∈ Icc (-r) r := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := hφ'.dist_le_mul s hsr (-s) hnr
    rw [dist_eq_norm, dist_eq_norm] at h
    simp only [Real.norm_eq_abs] at h ⊢
    rw [abs_of_nonneg (by linarith [hs.1] : 0 ≤ s - -s)] at h
    nlinarith [K.coe_nonneg, hs.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa only [stableSecondDifference_zero, sub_zero, pow_two, mul_assoc] using h

/-- A genuine shifted negative power has its explicit local derivative Lipschitz bound. -/
theorem shifted_negative_power_derivative_lipschitz {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun s : ℝ ↦ -α * (r + s) ^ (-1 - α)) (Icc (-(r / 2)) (r / 2)) := by
  let L := negativePowerLipConst (-1 - α) (r / 2) (by linarith) (by positivity)
  let K : ℝ≥0 := ⟨α * (L : ℝ), mul_nonneg hα.le L.coe_nonneg⟩
  refine ⟨K, LipschitzOnWith.of_dist_le_mul (fun x hx y hy ↦ ?_)⟩
  have hxy := (lipschitzOnWith_rpow_nonpos_Ici (by linarith : -1 - α ≤ 0)
    (by positivity : 0 < r / 2)).dist_le_mul (r + x)
      (by change r / 2 ≤ r + x; linarith [hx.1])
      (r + y) (by change r / 2 ≤ r + y; linarith [hy.1])
  rw [dist_eq_norm, dist_eq_norm] at hxy ⊢
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hα)]
  simp only [neg_neg, Real.norm_eq_abs]
  change α * |(r + x) ^ (-1 - α) - (r + y) ^ (-1 - α)| ≤
    (α * (L : ℝ)) * |x - y|
  simpa only [add_sub_add_left_eq_sub, mul_assoc, Real.norm_eq_abs, L] using
    mul_le_mul_of_nonneg_left hxy hα.le

/-- The actual shifted power has quadratic small-jump cancellation on a positive neighborhood. -/
theorem exists_quadratic_shifted_negative_power {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    ∃ C : ℝ, ∀ t ∈ Ioc 0 (r / 2),
      ‖(r + t) ^ (-α) + (r - t) ^ (-α) - 2 * r ^ (-α)‖ ≤ C * t ^ 2 := by
  obtain ⟨K, hK⟩ := shifted_negative_power_derivative_lipschitz hα hr
  refine ⟨2 * (K : ℝ), fun t ht ↦ ?_⟩
  have hd : ∀ s ∈ Icc (-(r / 2)) (r / 2),
      HasDerivAt (fun s : ℝ ↦ (r + s) ^ (-α)) (-α * (r + s) ^ (-1 - α)) s := by
    intro s hs
    have hp : r + s ≠ 0 := ne_of_gt (by linarith [hs.1])
    convert ((hasDerivAt_id s).const_add r).rpow_const (p := -α) (Or.inl hp) using 1 <;>
      simp only [id_eq, one_mul, show -α - 1 = -1 - α by ring]
  have h := norm_stableSecondDifference_le_quadratic_on hd hK ht.1.le ht.2
  simpa only [stableSecondDifference, smul_eq_mul, add_zero, ← sub_eq_add_neg] using h

end PartialBalayage.Maximal.Square
