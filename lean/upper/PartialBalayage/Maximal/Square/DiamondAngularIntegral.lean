/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondAngularDerivative

/-!
# Genuine angular constancy of the diamond generator

The actual coordinate singular integrals converge in each open quadrant. Differentiation
under their paired integral is justified by a common integrable local Lipschitz bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PartialBalayage.Linear
open scoped NNReal Topology

namespace PartialBalayage.Maximal.Square

/-- The genuine crossed-axis tail, extended by zero to the complete jump line. -/
def diamondAngularTail (α u v : ℝ) (t : ℝ) : ℝ :=
  (Ioi u).indicator (fun t ↦ t ^ (-1 - α) * (t - u + v) ^ (-1 - α)) t

theorem integrable_diamondAngularTail {α u v : ℝ}
    (hα : 0 < α) (hu : 0 < u) (hv : 0 < v) :
    Integrable (diamondAngularTail α u v) := by
  apply IntegrableOn.integrable_indicator
    (s := Ioi u) (f := fun t ↦ t ^ (-1 - α) * (t - u + v) ^ (-1 - α))
      ?_ measurableSet_Ioi
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - α < -1) hu).const_mul
    (v ^ (-1 - α))
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change u < t at ht
  have ht0 : 0 < t := hu.trans ht
  have hb : 0 < t - u + v := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hb.le _))]
  have h := Real.rpow_le_rpow_of_nonpos hv (by linarith : v ≤ t - u + v)
    (by linarith : -1 - α ≤ 0)
  exact (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht0.le _)).trans_eq (mul_comm _ _)

theorem integral_Ioi_diamondAngularTail {α u v : ℝ} (hu : 0 < u) :
    (∫ t in Ioi 0, diamondAngularTail α u v t) =
      ∫ t in Ioi u, t ^ (-1 - α) * (t - u + v) ^ (-1 - α) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ ?_)]
  · exact integral_indicator measurableSet_Ioi
  · apply indicator_of_notMem
    change ¬u < t
    change ¬0 < t at ht
    linarith [not_lt.mp ht]

theorem diamondAngularDerivative_eq_tails (α r a t : ℝ) :
    diamondAngularDerivative α r a t = 2 * α *
      (diamondAngularTail α a (r - a) t - diamondAngularTail α (r - a) a t) := by
  simp only [diamondAngularDerivative, diamondAngularTail, indicator_apply, mem_Ioi]
  split_ifs <;> ring

/-- The actual derivative tails are integrable and have exactly cancelling integrals. -/
theorem integral_diamondAngularDerivative_eq_zero {α r a : ℝ}
    (hα : 0 < α) (ha0 : 0 < a) (har : a < r) :
    (∫ t in Ioi 0, diamondAngularDerivative α r a t) = 0 := by
  have hv : 0 < r - a := sub_pos.mpr har
  simp_rw [diamondAngularDerivative_eq_tails]
  rw [integral_const_mul, integral_sub
    (integrable_diamondAngularTail hα ha0 hv).integrableOn
    (integrable_diamondAngularTail hα hv ha0).integrableOn,
    integral_Ioi_diamondAngularTail ha0, integral_Ioi_diamondAngularTail hv,
    diamond_crossed_axis_cancellation, mul_zero]

theorem diamondAngularIntegrand_eq_coordinate_sum {α r a t : ℝ}
    (ha0 : 0 < a) (har : a < r) (ht : 0 < t) :
    diamondAngularIntegrand α r a t =
      t ^ (-1 - α) * stableSecondDifference (diamondCoordinateProfile α a (r - a)) t +
        t ^ (-1 - α) * stableSecondDifference
          (diamondCoordinateProfile α (r - a) a) t := by
  rw [diamondCoordinateProfile_secondDifference_pos ha0 ht,
    diamondCoordinateProfile_secondDifference_pos (sub_pos.mpr har) ht]
  unfold diamondAngularIntegrand diamondAngularBackward
  simp only [sub_add_cancel, add_sub_cancel]
  have he : |r - a - t| + r - (r - a) = a + |r - a - t| := by ring
  have he' : |a - t| + r - a = |a - t| + (r - a) := by ring
  rw [he, he']
  rw [add_comm (|r - a - t|) a]
  ring

theorem integrableOn_diamondAngularIntegrand {α r a : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (ha0 : 0 < a) (har : a < r) :
    IntegrableOn (diamondAngularIntegrand α r a) (Ioi 0) := by
  apply ((integrableOn_diamondCoordinateSecondDifference hα0 hα2 ha0 (sub_pos.mpr har)).add
    (integrableOn_diamondCoordinateSecondDifference hα0 hα2 (sub_pos.mpr har) ha0)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (diamondAngularIntegrand_eq_coordinate_sum ha0 har ht).symm

theorem integral_diamondAngularIntegrand {α r a : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (ha0 : 0 < a) (har : a < r) :
    (∫ t in Ioi 0, diamondAngularIntegrand α r a t) =
      diamondPairedGenerator α a (r - a) := by
  rw [diamondPairedGenerator_eq_integral hα0 hα2 ha0 (sub_pos.mpr har)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold diamondAngularIntegrand diamondAngularBackward
  dsimp only
  simp only [add_sub_cancel]
  have he₁ : |a - t| + r - a = |a - t| + (r - a) := by ring
  have he₂ : |r - a - t| + r - (r - a) = a + |r - a - t| := by ring
  rw [he₁, he₂]

/-- The true local angular Lipschitz majorant is integrable on the actual jump measure. -/
theorem integrableOn_diamondAngularLipBound {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ ↦ if δ < t then
      4 * (negativePowerLipConst (-α) δ (by linarith) hδ : ℝ) * t ^ (-1 - α) else 0)
        (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦
      4 * (negativePowerLipConst (-α) δ (by linarith) hδ : ℝ) * t ^ (-1 - α)) (Ioi δ) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - α < -1) hδ).const_mul _
  have h := IntegrableOn.integrable_indicator hi measurableSet_Ioi
  change IntegrableOn ((Ioi δ).indicator (fun t : ℝ ↦
    4 * (negativePowerLipConst (-α) δ (by linarith) hδ : ℝ) * t ^ (-1 - α))) (Ioi 0)
  exact h.integrableOn

/-- Differentiating the genuine integral gives zero because its actual axis tails cancel. -/
theorem hasDerivAt_integral_diamondAngularIntegrand {α r a : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (ha0 : 0 < a) (har : a < r) :
    HasDerivAt (fun b ↦ ∫ t in Ioi 0, diamondAngularIntegrand α r b t) 0 a := by
  let δ := min a (r - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (lt_min ha0 (sub_pos.mpr har)) (by norm_num)
  have hδa : δ < a := by dsimp [δ]; nlinarith [min_le_left a (r - a)]
  have hδv : a < r - δ := by dsimp [δ]; nlinarith [min_le_right a (r - a)]
  have hm : ∀ b : ℝ, AEStronglyMeasurable (diamondAngularIntegrand α r b)
      (volume.restrict (Ioi 0)) := by
    intro b
    apply Measurable.aestronglyMeasurable
    unfold diamondAngularIntegrand diamondAngularBackward
    fun_prop
  have hDm : AEStronglyMeasurable (diamondAngularDerivative α r a)
      (volume.restrict (Ioi 0)) := by
    have hi := ((integrable_diamondAngularTail hα0 ha0 (sub_pos.mpr har)).sub
      (integrable_diamondAngularTail hα0 (sub_pos.mpr har) ha0)).const_mul (2 * α)
    have he : diamondAngularDerivative α r a = fun t ↦
        2 * α * (diamondAngularTail α a (r - a) t - diamondAngularTail α (r - a) a t) := by
      funext t
      exact diamondAngularDerivative_eq_tails α r a t
    rw [he]
    exact hi.integrableOn.aestronglyMeasurable
  have hd : ∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt
      (fun b ↦ diamondAngularIntegrand α r b t) (diamondAngularDerivative α r a t) a := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne a),
      ae_restrict_of_ae (volume.ae_ne (r - a))] with t hta htv
    exact hasDerivAt_diamondAngularIntegrand ha0 har hta.symm htv.symm
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun b t ↦ diamondAngularIntegrand α r b t)
    (F' := diamondAngularDerivative α r a)
    (bound := fun t ↦ if δ < t then
      4 * (negativePowerLipConst (-α) δ (by linarith) hδ : ℝ) * t ^ (-1 - α) else 0)
    (Icc_mem_nhds hδa hδv) (Eventually.of_forall hm)
    (integrableOn_diamondAngularIntegrand hα0 hα2 ha0 har)
    hDm
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact lipschitzOnWith_diamondAngularIntegrand hα0.le hδ ht)
    (integrableOn_diamondAngularLipBound hα0 hδ) hd
  rw [integral_diamondAngularDerivative_eq_zero hα0 ha0 har] at h
  exact h.2

/-- The true paired generator has vanishing ordinary angular derivative. -/
theorem hasDerivAt_diamondPairedGenerator_angular {α r a : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (ha0 : 0 < a) (har : a < r) :
    HasDerivAt (fun b ↦ diamondPairedGenerator α b (r - b)) 0 a := by
  apply (hasDerivAt_integral_diamondAngularIntegrand hα0 hα2 ha0 har).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha0 har] with b hb
  exact (integral_diamondAngularIntegrand hα0 hα2 hb.1 hb.2).symm

/-- The genuine two-coordinate generator is independent of the angular split of its radius. -/
theorem diamondPairedGenerator_angular_constant {α r u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hu0 : 0 < u) (hur : u < r)
    (hv0 : 0 < v) (hvr : v < r) :
    diamondPairedGenerator α u (r - u) = diamondPairedGenerator α v (r - v) := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 r).isPreconnected
    (fun a ha ↦ (hasDerivAt_diamondPairedGenerator_angular hα0 hα2 ha.1 ha.2
      ).differentiableAt.differentiableWithinAt)
    (fun a ha ↦ (hasDerivAt_diamondPairedGenerator_angular hα0 hα2 ha.1 ha.2).deriv)
    ⟨hu0, hur⟩ ⟨hv0, hvr⟩

end PartialBalayage.Maximal.Square
