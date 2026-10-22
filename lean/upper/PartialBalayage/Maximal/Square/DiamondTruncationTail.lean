/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondGeneratorHomogeneity

/-!
# The genuine truncation tails of the diamond power

The positive-part truncation has an exact actual exterior correction. In a strict interior
quadrant, its forward and backward jump corrections begin on explicit genuine half-lines.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

/-- The actual positive-part coordinate profile used by the truncated radial kernel. -/
def diamondCoordinateTruncatedProfile (α R u v s : ℝ) : ℝ :=
  max (diamondCoordinateProfile α u v s - R ^ (-α)) 0

/-- The actual bounded exterior correction to the homogeneous radial power. -/
def diamondExteriorPowerCorrection (α R q : ℝ) : ℝ := max (R ^ (-α) - q ^ (-α)) 0

theorem max_sub_eq_add_reverse_max (z c : ℝ) :
    max (z - c) 0 = z - c + max (c - z) 0 := by
  by_cases h : c ≤ z
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

theorem diamondExteriorPowerCorrection_eq {α R q : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hq : 0 < q) :
    diamondExteriorPowerCorrection α R q = if R < q then R ^ (-α) - q ^ (-α) else 0 := by
  unfold diamondExteriorPowerCorrection
  by_cases hRq : R < q
  · rw [ite_eq_left hRq, max_eq_left]
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR hRq.le (neg_nonpos.mpr hα))
  · rw [ite_eq_right hRq, max_eq_right]
    exact sub_nonpos.mpr (Real.rpow_le_rpow_of_nonpos hq (le_of_not_gt hRq)
      (neg_nonpos.mpr hα))

theorem diamondCoordinateTruncatedProfile_eq_correction (α R u v s : ℝ) :
    diamondCoordinateTruncatedProfile α R u v s =
      diamondCoordinateProfile α u v s - R ^ (-α) +
        diamondExteriorPowerCorrection α R (|u + s| + v) :=
  max_sub_eq_add_reverse_max _ _

theorem diamondCoordinateTruncatedProfile_secondDifference {α R u v t : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) (hr : u + v < R) :
    stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      stableSecondDifference (diamondCoordinateProfile α u v) t +
        diamondExteriorPowerCorrection α R (|u + t| + v) +
          diamondExteriorPowerCorrection α R (|u - t| + v) := by
  have hz : diamondExteriorPowerCorrection α R (|u + 0| + v) = 0 := by
    simp only [add_zero, abs_of_pos hu]
    rw [diamondExteriorPowerCorrection_eq hα hR (add_pos hu hv), ite_eq_right hr.not_gt]
  simp only [stableSecondDifference, diamondCoordinateTruncatedProfile_eq_correction,
    smul_eq_mul, hz, ← sub_eq_add_neg]
  ring

theorem diamond_backward_exterior_iff {R u v t : ℝ} (hu : 0 < u) (_hv : 0 < v)
    (hr : u + v < R) (ht : 0 < t) :
    R < |u - t| + v ↔ R + u - v < t := by
  by_cases htu : t ≤ u
  · rw [abs_of_nonneg (sub_nonneg.mpr htu)]
    constructor <;> intro h <;> linarith
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge htu))]
    constructor <;> intro h <;> linarith

/-- The original interior correction begins exactly at the true forward and backward tails. -/
theorem diamondCoordinateTruncatedProfile_secondDifference_tails {α R u v t : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) (hr : u + v < R)
    (ht : 0 < t) :
    stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      stableSecondDifference (diamondCoordinateProfile α u v) t +
        (if R - (u + v) < t then R ^ (-α) - (u + v + t) ^ (-α) else 0) +
          (if R + u - v < t then R ^ (-α) - (t - u + v) ^ (-α) else 0) := by
  rw [diamondCoordinateTruncatedProfile_secondDifference hα hR hu hv hr,
    diamondExteriorPowerCorrection_eq hα hR (by positivity : 0 < |u + t| + v),
    diamondExteriorPowerCorrection_eq hα hR (by positivity : 0 < |u - t| + v),
    abs_of_pos (add_pos hu ht)]
  simp only [diamond_backward_exterior_iff hu hv hr ht]
  have he₁ : u + t + v = u + v + t := by ring
  have he₂ : (R < u + v + t) ↔ R - (u + v) < t := by
    constructor <;> intro h <;> linarith
  rw [he₁]
  simp only [he₂]
  by_cases hb : R + u - v < t
  · have htu : u < t := by linarith
    simp only [ite_eq_left hb]
    rw [abs_of_neg (sub_neg.mpr htu)]
    have he : -(u - t) + v = t - u + v := by ring
    rw [he]
  · simp only [ite_eq_right hb]

/-- The actual exterior correction weighted by the original jump density. -/
def diamondTailWeighted (α R c t : ℝ) : ℝ :=
  (Ioi (R - c)).indicator (fun t ↦ t ^ (-1 - α) *
    (R ^ (-α) - (t + c) ^ (-α))) t

/-- The original exterior jump correction is genuinely integrable. -/
theorem integrable_diamondTailWeighted {α R c : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hc : c < R) :
    Integrable (diamondTailWeighted α R c) := by
  apply IntegrableOn.integrable_indicator (s := Ioi (R - c))
    (f := fun t ↦ t ^ (-1 - α) * (R ^ (-α) - (t + c) ^ (-α))) ?_ measurableSet_Ioi
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - α < -1)
    (sub_pos.mpr hc)).const_mul (R ^ (-α))
  apply hi.mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change R - c < t at ht
  have ht0 : 0 < t := (sub_pos.mpr hc).trans ht
  have hbase : 0 < t + c := by linarith
  have hdiff : 0 ≤ R ^ (-α) - (t + c) ^ (-α) := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR (by linarith) (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) hdiff)]
  exact (mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.rpow_nonneg hbase.le _)) (Real.rpow_nonneg ht0.le _)).trans_eq
      (mul_comm _ _)

theorem integral_Ioi_shift_right_from (f : ℝ → ℝ) (c u : ℝ) :
    (∫ t in Ioi c, f (t + u)) = ∫ q in Ioi (c + u), f q := by
  rw [← integral_Ioi_shift_right _ c, ← integral_Ioi_shift_right _ (c + u)]
  simp only [add_assoc]

/-- Actual translation gives the geometric incoming-tail variable, with no formal substitution. -/
theorem integral_Ioi_diamondTailWeighted {R c : ℝ} (hc : c < R) (α : ℝ) :
    (∫ t in Ioi 0, diamondTailWeighted α R c t) =
      ∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q - c) ^ (-1 - α) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ ?_)]
  · unfold diamondTailWeighted
    rw [integral_indicator measurableSet_Ioi]
    have he : (fun t : ℝ ↦ t ^ (-1 - α) * (R ^ (-α) - (t + c) ^ (-α))) =
        fun t ↦ (R ^ (-α) - (t + c) ^ (-α)) * ((t + c) - c) ^ (-1 - α) := by
      funext t
      simp only [add_sub_cancel_right]
      ring
    rw [he]
    simpa only [sub_add_cancel] using integral_Ioi_shift_right_from
      (fun q ↦ (R ^ (-α) - q ^ (-α)) * (q - c) ^ (-1 - α)) (R - c) c
  · apply indicator_of_notMem
    change ¬R - c < t
    change ¬0 < t at ht
    linarith [not_lt.mp ht]

/-- The genuine shifted incoming tail is integrable on its radial half-line. -/
theorem integrableOn_diamondShiftedTail {α R c : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hc : c < R) :
    IntegrableOn (fun q ↦ (R ^ (-α) - q ^ (-α)) * (q - c) ^ (-1 - α)) (Ioi R) := by
  have hi : IntegrableOn (fun q : ℝ ↦ (q - c) ^ (-1 - α)) (Ioi R) := by
    simpa only [sub_eq_add_neg] using integrableOn_add_rpow_Ioi_of_lt
      (by linarith : -1 - α < -1) (by linarith : -(-c) < R)
  apply (hi.const_mul (R ^ (-α))).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  change R < q at hq
  have hqc : 0 < q - c := by linarith
  have hdiff : 0 ≤ R ^ (-α) - q ^ (-α) :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR hq.le (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdiff (Real.rpow_nonneg hqc.le _))]
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (hR.le.trans hq.le) _))
    (Real.rpow_nonneg hqc.le _)

theorem diamondCoordinateTruncatedProfile_weighted_tails {α R u v t : ℝ}
    (hα : 0 ≤ α) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) (hr : u + v < R)
    (ht : 0 < t) :
    t ^ (-1 - α) * stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t =
      t ^ (-1 - α) * stableSecondDifference (diamondCoordinateProfile α u v) t +
        diamondTailWeighted α R (u + v) t + diamondTailWeighted α R (v - u) t := by
  rw [diamondCoordinateTruncatedProfile_secondDifference_tails hα hR hu hv hr ht]
  simp only [diamondTailWeighted, indicator_apply, mem_Ioi]
  have he₁ : R - (v - u) = R + u - v := by ring
  have he₂ : t + (v - u) = t - u + v := by ring
  have he₃ : t + (u + v) = u + v + t := by ring
  rw [he₁, he₂, he₃]
  split_ifs <;> ring

/-- The original truncated coordinate integral genuinely converges at strict interior points. -/
theorem integrableOn_diamondCoordinateTruncatedSecondDifference {α R u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < R) :
    IntegrableOn (fun t ↦ t ^ (-1 - α) *
      stableSecondDifference (diamondCoordinateTruncatedProfile α R u v) t) (Ioi 0) := by
  have h₀ := integrableOn_diamondCoordinateSecondDifference hα0 hα2 hu hv
  have h₁ := (integrable_diamondTailWeighted hα0 hR hr).integrableOn (s := Ioi 0)
  have h₂ := (integrable_diamondTailWeighted hα0 hR
    (by linarith : v - u < R)).integrableOn (s := Ioi 0)
  apply ((h₀.add h₁).add h₂).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (diamondCoordinateTruncatedProfile_weighted_tails hα0.le hR hu hv hr ht).symm

/-- The true interior coordinate generator has its homogeneous part and genuine incoming tails. -/
theorem stableGeneratorIntegral_diamondCoordinateTruncatedProfile {α R u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < R) :
    stableGeneratorIntegral α (diamondCoordinateTruncatedProfile α R u v) =
      diamondCoordinateIntegral α u v +
        (∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q - (u + v)) ^ (-1 - α)) +
          ∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q - (v - u)) ^ (-1 - α) := by
  have h₀ := integrableOn_diamondCoordinateSecondDifference hα0 hα2 hu hv
  have h₁ := (integrable_diamondTailWeighted hα0 hR hr).integrableOn (s := Ioi 0)
  have hc : v - u < R := by linarith
  have h₂ := (integrable_diamondTailWeighted hα0 hR hc).integrableOn (s := Ioi 0)
  have he₁ := integral_add (h₀.add h₁) h₂
  have he₂ := integral_add h₀ h₁
  simp only [Pi.add_apply] at he₁ he₂
  unfold stableGeneratorIntegral
  simp only [smul_eq_mul]
  calc
    _ = ∫ t in Ioi 0, t ^ (-1 - α) *
        stableSecondDifference (diamondCoordinateProfile α u v) t +
          diamondTailWeighted α R (u + v) t + diamondTailWeighted α R (v - u) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact diamondCoordinateTruncatedProfile_weighted_tails hα0.le hR hu hv hr ht
    _ = _ := by
      rw [he₁, he₂, integral_Ioi_diamondTailWeighted hr, integral_Ioi_diamondTailWeighted hc]
      rfl

/-- The exact radial incoming tail is the sum of three genuinely integrable shifted tails. -/
theorem radialIncomingTail_eq_integral_sum {α R r d : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hr : r < R) (hd : |d| < R) :
    radialIncomingTail α R r d =
      2 * (∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q - r) ^ (-1 - α)) +
        (∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q - d) ^ (-1 - α)) +
          ∫ q in Ioi R, (R ^ (-α) - q ^ (-α)) * (q + d) ^ (-1 - α) := by
  have hd₁ : d < R := (le_abs_self d).trans_lt hd
  have hd₂ : -d < R := (neg_le_abs d).trans_lt hd
  have h₀ := (integrableOn_diamondShiftedTail hα hR hr).const_mul (2 : ℝ)
  have h₁ := integrableOn_diamondShiftedTail hα hR hd₁
  have h₂ : IntegrableOn (fun q ↦ (R ^ (-α) - q ^ (-α)) * (q + d) ^ (-1 - α))
      (Ioi R) := by simpa only [sub_neg_eq_add] using integrableOn_diamondShiftedTail hα hR hd₂
  have he₁ := integral_add (h₀.add h₁) h₂
  have he₂ := integral_add h₀ h₁
  simp only [Pi.add_apply] at he₁ he₂
  unfold radialIncomingTail
  have he : (fun q : ℝ ↦ (R ^ (-α) - q ^ (-α)) *
      (2 * (q - r) ^ (-1 - α) + (q - d) ^ (-1 - α) + (q + d) ^ (-1 - α))) =
      fun q ↦ (2 * ((R ^ (-α) - q ^ (-α)) * (q - r) ^ (-1 - α)) +
        (R ^ (-α) - q ^ (-α)) * (q - d) ^ (-1 - α)) +
          (R ^ (-α) - q ^ (-α)) * (q + d) ^ (-1 - α) := by funext q; ring
  rw [he, he₁, he₂, integral_const_mul]

/-- The genuine truncated paired coordinate generator has exactly the original radial tail. -/
theorem stableGeneratorIntegral_diamondTruncated_pair {α R u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < R) :
    stableGeneratorIntegral α (diamondCoordinateTruncatedProfile α R u v) +
      stableGeneratorIntegral α (diamondCoordinateTruncatedProfile α R v u) =
        diamondPairedGenerator α u v + radialIncomingTail α R (u + v) (u - v) := by
  have hr' : v + u < R := by linarith
  have hd : |u - v| < R := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [stableGeneratorIntegral_diamondCoordinateTruncatedProfile hα0 hα2 hR hu hv hr,
    stableGeneratorIntegral_diamondCoordinateTruncatedProfile hα0 hα2 hR hv hu hr',
    radialIncomingTail_eq_integral_sum hα0 hR hr hd, diamondPairedGenerator,
    add_comm v u]
  have he : (fun q : ℝ ↦ (R ^ (-α) - q ^ (-α)) * (q - (v - u)) ^ (-1 - α)) =
      fun q ↦ (R ^ (-α) - q ^ (-α)) * (q + (u - v)) ^ (-1 - α) := by
    funext q
    congr 2
    ring
  rw [he]
  ring

end PartialBalayage.Maximal.Square
