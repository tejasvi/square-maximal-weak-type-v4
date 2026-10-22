/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondTruncationTail

/-!
# Actual quadratic cancellation and axis-strip errors

Away from the radial origin, the smooth second difference has a uniform quadratic bound.
The genuine axis cusp contributes only when the jump crosses its actual width-`t` strip.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped NNReal

namespace PartialBalayage.Maximal.Square

private theorem shifted_negative_power_derivative_lipschitz_uniform {α δ r : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hr : δ ≤ r) :
    LipschitzOnWith
      ⟨α * (negativePowerLipConst (-1 - α) (δ / 2) (by linarith) (by positivity) : ℝ),
        mul_nonneg hα.le (by positivity)⟩
      (fun s : ℝ ↦ -α * (r + s) ^ (-1 - α)) (Icc (-(δ / 2)) (δ / 2)) := by
  let L := negativePowerLipConst (-1 - α) (δ / 2) (by linarith) (by positivity)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := (lipschitzOnWith_rpow_nonpos_Ici (by linarith : -1 - α ≤ 0)
    (by positivity : 0 < δ / 2)).dist_le_mul (r + x)
      (by change δ / 2 ≤ r + x; linarith [hx.1]) (r + y)
        (by change δ / 2 ≤ r + y; linarith [hy.1])
  rw [dist_eq_norm, dist_eq_norm] at h ⊢
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hα)]
  simp only [neg_neg, Real.norm_eq_abs]
  change α * |(r + x) ^ (-1 - α) - (r + y) ^ (-1 - α)| ≤
    (α * (L : ℝ)) * |x - y|
  simpa only [add_sub_add_left_eq_sub, mul_assoc, Real.norm_eq_abs, L] using
    mul_le_mul_of_nonneg_left h hα.le

/-- A true shifted negative power has one common quadratic bound away from the origin. -/
theorem norm_shifted_negative_power_secondDifference_uniform {α δ r t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hr : δ ≤ r) (ht : 0 ≤ t) (hdt : t ≤ δ / 2) :
    ‖(r + t) ^ (-α) + (r - t) ^ (-α) - 2 * r ^ (-α)‖ ≤
      (2 * α * (negativePowerLipConst (-1 - α) (δ / 2)
        (by linarith) (by positivity) : ℝ)) * t ^ 2 := by
  have hd : ∀ s ∈ Icc (-(δ / 2)) (δ / 2),
      HasDerivAt (fun s : ℝ ↦ (r + s) ^ (-α)) (-α * (r + s) ^ (-1 - α)) s := by
    intro s hs
    have hp : r + s ≠ 0 := ne_of_gt (by linarith [hs.1])
    convert ((hasDerivAt_id s).const_add r).rpow_const (p := -α) (Or.inl hp) using 1 <;>
      simp only [id_eq, one_mul, show -α - 1 = -1 - α by ring]
  have h := norm_stableSecondDifference_le_quadratic_on hd
    (shifted_negative_power_derivative_lipschitz_uniform hα hδ hr) ht hdt
  change ‖stableSecondDifference (fun s : ℝ ↦ (r + s) ^ (-α)) t‖ ≤
    2 * (α * (negativePowerLipConst (-1 - α) (δ / 2)
      (by linarith) (by positivity) : ℝ)) * t ^ 2 at h
  simpa only [stableSecondDifference, smul_eq_mul, add_zero, ← sub_eq_add_neg, mul_assoc]
    using h

private theorem norm_diamond_axis_error_le {α δ u v t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hu : 0 ≤ u) (hr : δ ≤ u + v)
    (_ht : 0 ≤ t) (hdt : t ≤ δ / 2) :
    ‖(|u - t| + v) ^ (-α) - (u + v - t) ^ (-α)‖ ≤
      if u < t then 2 * (negativePowerLipConst (-α) (δ / 2)
        (by linarith) (by positivity) : ℝ) * t else 0 := by
  by_cases hut : u < t
  · rw [ite_eq_left hut, abs_of_neg (sub_neg.mpr hut)]
    have h := (lipschitzOnWith_rpow_nonpos_Ici (by linarith : -α ≤ 0)
      (by positivity : 0 < δ / 2)).dist_le_mul (-(u - t) + v)
        (by change δ / 2 ≤ -(u - t) + v; linarith) (u + v - t)
          (by change δ / 2 ≤ u + v - t; linarith)
    rw [dist_eq_norm, dist_eq_norm] at h
    have he : -(u - t) + v - (u + v - t) = 2 * (t - u) := by ring
    rw [he] at h
    simp only [Real.norm_eq_abs] at h ⊢
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (t - u))] at h
    exact h.trans (by nlinarith [(negativePowerLipConst (-α) (δ / 2)
      (by linarith) (by positivity)).coe_nonneg])
  · rw [ite_eq_right hut, abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hut))]
    have he : u - t + v = u + v - t := by ring
    rw [he, sub_self, norm_zero]

/-- The actual coordinate cusp contributes only inside the genuine axis-crossing strip. -/
theorem norm_diamondCoordinateSecondDifference_strip_le {α δ u v t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hu : 0 ≤ u) (hr : δ ≤ u + v)
    (ht : 0 ≤ t) (hdt : t ≤ δ / 2) :
    ‖stableSecondDifference (diamondCoordinateProfile α u v) t‖ ≤
      (2 * α * (negativePowerLipConst (-1 - α) (δ / 2)
        (by linarith) (by positivity) : ℝ)) * t ^ 2 +
          if u < t then 2 * (negativePowerLipConst (-α) (δ / 2)
            (by linarith) (by positivity) : ℝ) * t else 0 := by
  have hs := norm_shifted_negative_power_secondDifference_uniform hα hδ hr ht hdt
  have he := norm_diamond_axis_error_le hα hδ hu hr ht hdt
  have hid : stableSecondDifference (diamondCoordinateProfile α u v) t =
      ((u + v + t) ^ (-α) + (u + v - t) ^ (-α) - 2 * (u + v) ^ (-α)) +
        ((|u - t| + v) ^ (-α) - (u + v - t) ^ (-α)) := by
    simp only [stableSecondDifference, diamondCoordinateProfile, smul_eq_mul, add_zero,
      abs_of_nonneg hu, abs_of_nonneg (add_nonneg hu ht), ← sub_eq_add_neg]
    have hbase : u + t + v = u + v + t := by ring
    rw [hbase]
    ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hs he)

private theorem lipschitzOnWith_truncatedPower {α δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (R : ℝ) :
    LipschitzOnWith (negativePowerLipConst (-α) (δ / 2) (by linarith) (by positivity))
      (fun q : ℝ ↦ max (q ^ (-α) - R ^ (-α)) 0) (Ici (δ / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := (lipschitzOnWith_rpow_nonpos_Ici (by linarith : -α ≤ 0)
    (by positivity : 0 < δ / 2)).dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at h ⊢
  have hm := abs_max_sub_max_le_abs (x ^ (-α) - R ^ (-α)) (y ^ (-α) - R ^ (-α)) 0
  rw [sub_sub_sub_cancel_right] at hm
  exact hm.trans h

private theorem abs_diamond_backward_radius_sub {u v t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    |(|u - t| + v) - (u + v)| ≤ t := by
  have h := abs_abs_sub_abs_le_abs_sub (u - t) u
  rw [abs_of_nonneg hu, show u - t - u = -t by ring, abs_neg, abs_of_nonneg ht] at h
  simpa only [add_sub_add_right_eq_sub] using h

/-- The actual truncated profile remains locally Lipschitz even across its boundary. -/
theorem norm_diamondTruncatedSecondDifference_le_linear {α δ R u v t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hu : 0 ≤ u) (hr : δ ≤ u + v)
    (ht : 0 ≤ t) (hdt : t ≤ δ / 2) :
    ‖stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t‖ ≤
      2 * (negativePowerLipConst (-α) (δ / 2) (by linarith) (by positivity) : ℝ) * t := by
  have hl := lipschitzOnWith_truncatedPower hα hδ R
  have hp : δ / 2 ≤ u + v + t := by linarith
  have hn : δ / 2 ≤ |u - t| + v := by linarith [le_abs_self (u - t)]
  have hc : δ / 2 ≤ u + v := by linarith
  have hplus := hl.dist_le_mul (u + v + t) hp (u + v) hc
  have hminus := hl.dist_le_mul (|u - t| + v) hn (u + v) hc
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hplus
  simp only [Real.norm_eq_abs] at hplus
  rw [abs_of_nonneg ht] at hplus
  rw [dist_eq_norm, dist_eq_norm] at hminus
  simp only [Real.norm_eq_abs] at hminus
  have hb := abs_diamond_backward_radius_sub (v := v) hu ht
  have hb' := hminus.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have he : stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      (max ((u + v + t) ^ (-α) - R ^ (-α)) 0 -
        max ((u + v) ^ (-α) - R ^ (-α)) 0) +
      (max ((|u - t| + v) ^ (-α) - R ^ (-α)) 0 -
        max ((u + v) ^ (-α) - R ^ (-α)) 0) := by
    simp only [stableSecondDifference, diamondCoordinateTruncatedProfile,
      diamondCoordinateProfile, smul_eq_mul, add_zero, abs_of_nonneg hu,
      abs_of_nonneg (add_nonneg hu ht), ← sub_eq_add_neg]
    rw [show u + t + v = u + v + t by ring]
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hplus hb').trans_eq (by ring))

private theorem truncatedPower_eq_sub {α R q : ℝ} (hα : 0 < α)
    (hq : 0 < q) (hR : q ≤ R) :
    max (q ^ (-α) - R ^ (-α)) 0 = q ^ (-α) - R ^ (-α) := by
  exact max_eq_left (sub_nonneg.mpr
    (Real.rpow_le_rpow_of_nonpos hq hR (neg_nonpos.mpr hα.le)))

private theorem truncatedPower_eq_zero {α R q : ℝ} (hα : 0 < α)
    (hR : 0 < R) (hq : R ≤ q) : max (q ^ (-α) - R ^ (-α)) 0 = 0 := by
  exact max_eq_right (sub_nonpos.mpr
    (Real.rpow_le_rpow_of_nonpos hR hq (neg_nonpos.mpr hα.le)))

private theorem diamondTruncatedSecondDifference_eq_boundary_far {α δ R u v t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hR : 0 < R) (hu : 0 ≤ u) (hr : δ ≤ u + v)
    (ht : 0 ≤ t) (hdt : t ≤ δ / 2) (hf : ¬|R - (u + v)| < t) :
    stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      if u + v ≤ R then stableSecondDifference (diamondCoordinateProfile α u v) t else 0 := by
  have hback : |u - t| ≤ u + t := by
    simpa only [abs_of_nonneg hu, abs_of_nonneg ht] using abs_sub u t
  have hp : 0 < u + v + t := by linarith
  have hn : 0 < |u - t| + v := by linarith [le_abs_self (u - t)]
  have hc : 0 < u + v := hδ.trans_le hr
  by_cases hb : u + v ≤ R
  · have hfar : t ≤ R - (u + v) := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hb), not_lt] at hf
    have hpf : u + v + t ≤ R := by linarith
    have hnf : |u - t| + v ≤ R := by linarith
    simp only [ite_eq_left hb, stableSecondDifference, diamondCoordinateTruncatedProfile,
      diamondCoordinateProfile, smul_eq_mul, add_zero, abs_of_nonneg hu,
      abs_of_nonneg (add_nonneg hu ht), ← sub_eq_add_neg]
    rw [show u + t + v = u + v + t by ring, truncatedPower_eq_sub hα hp hpf,
      truncatedPower_eq_sub hα hn hnf, truncatedPower_eq_sub hα hc hb]
    ring
  · have hfar : t ≤ u + v - R := by
      have hnR : R - (u + v) ≤ 0 := by linarith [not_le.mp hb]
      rw [abs_of_nonpos hnR, not_lt] at hf
      linarith
    have hpf : R ≤ u + v + t := by linarith [not_le.mp hb]
    have hnf : R ≤ |u - t| + v := by linarith [le_abs_self (u - t)]
    simp only [ite_eq_right hb, stableSecondDifference, diamondCoordinateTruncatedProfile,
      diamondCoordinateProfile, smul_eq_mul, add_zero, abs_of_nonneg hu,
      abs_of_nonneg (add_nonneg hu ht), ← sub_eq_add_neg]
    rw [show u + t + v = u + v + t by ring, truncatedPower_eq_zero hα hR hpf,
      truncatedPower_eq_zero hα hR hnf,
      truncatedPower_eq_zero hα hR (le_of_lt (not_le.mp hb))]
    ring

/-- The genuine small-jump error consists of a quadratic term and two actual thin strips. -/
theorem norm_diamondTruncatedSecondDifference_strips_le {α δ R u v t : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hR : 0 < R) (hu : 0 ≤ u) (hr : δ ≤ u + v)
    (ht : 0 ≤ t) (hdt : t ≤ δ / 2) :
    ‖stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t‖ ≤
      (2 * α * (negativePowerLipConst (-1 - α) (δ / 2)
        (by linarith) (by positivity) : ℝ)) * t ^ 2 +
      (if u < t then 2 * (negativePowerLipConst (-α) (δ / 2)
        (by linarith) (by positivity) : ℝ) * t else 0) +
      (if |R - (u + v)| < t then 2 * (negativePowerLipConst (-α) (δ / 2)
        (by linarith) (by positivity) : ℝ) * t else 0) := by
  have hq := norm_diamondCoordinateSecondDifference_strip_le hα hδ hu hr ht hdt
  by_cases hb : |R - (u + v)| < t
  · rw [ite_eq_left hb]
    apply (norm_diamondTruncatedSecondDifference_le_linear hα hδ hu hr ht hdt).trans
    have hbase : 0 ≤ (2 * α * (negativePowerLipConst (-1 - α) (δ / 2)
        (by linarith) (by positivity) : ℝ)) * t ^ 2 := by positivity
    have haxis : 0 ≤ if u < t then 2 * (negativePowerLipConst (-α) (δ / 2)
        (by linarith) (by positivity) : ℝ) * t else 0 := by split_ifs <;> positivity
    linarith
  · rw [ite_eq_right hb,
      diamondTruncatedSecondDifference_eq_boundary_far hα hδ hR hu hr ht hdt hb, add_zero]
    by_cases hinside : u + v ≤ R
    · rw [ite_eq_left hinside]
      exact hq
    · rw [ite_eq_right hinside, norm_zero]
      split_ifs <;> positivity

end PartialBalayage.Maximal.Square
