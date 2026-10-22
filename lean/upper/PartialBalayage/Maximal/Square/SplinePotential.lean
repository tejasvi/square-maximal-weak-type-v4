/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineRegularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The genuine power potential of a spline hinge

The primitive is continuous through its singular point and differentiable elsewhere.
Splitting the actual interval integral at that point proves the hinge formula without
an arithmetic or integration certificate premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- A continuous signed power, expressed using two nonnegative truncated powers. -/
def signedRealPower (p z : ℝ) : ℝ := (max z 0) ^ p - (max (-z) 0) ^ p

theorem continuous_signedRealPower {p : ℝ} (hp : 0 ≤ p) :
    Continuous (signedRealPower p) := by
  unfold signedRealPower
  exact ((continuous_id.max continuous_const).rpow_const (fun _ ↦ Or.inr hp)).sub
    ((continuous_id.neg.max continuous_const).rpow_const (fun _ ↦ Or.inr hp))

/-- The actual primitive of `(s+c)|s-x|^(-1/5)`. -/
def splineHingePrimitive (x c s : ℝ) : ℝ :=
  (5 / 9 : ℝ) * |s - x| ^ (9 / 5 : ℝ) +
    (5 / 4 : ℝ) * (x + c) * signedRealPower (4 / 5) (s - x)

theorem continuous_splineHingePrimitive (x c : ℝ) :
    Continuous (splineHingePrimitive x c) := by
  unfold splineHingePrimitive
  have h₁ : Continuous (fun s : ℝ ↦ |s - x| ^ (9 / 5 : ℝ)) :=
    (continuous_id.sub continuous_const).abs.rpow_const (fun _ ↦ Or.inr (by norm_num))
  have h₂ : Continuous (fun s : ℝ ↦ signedRealPower (4 / 5) (s - x)) :=
    (continuous_signedRealPower (by norm_num : (0 : ℝ) ≤ 4 / 5)).comp
      (continuous_id.sub continuous_const)
  exact (continuous_const.mul h₁).add (continuous_const.mul h₂)

private theorem rpow_four_fifths {z : ℝ} (hz : 0 < z) :
    z ^ (4 / 5 : ℝ) = z * z ^ (-1 / 5 : ℝ) := by
  calc
    _ = z ^ ((1 : ℝ) + (-1 / 5)) := by norm_num
    _ = z ^ (1 : ℝ) * z ^ (-1 / 5 : ℝ) := Real.rpow_add hz _ _
    _ = _ := by rw [Real.rpow_one]

theorem hasDerivAt_splineHingePrimitive {x c s : ℝ} (hs : s ≠ x) :
    HasDerivAt (splineHingePrimitive x c) ((s + c) * |s - x| ^ (-1 / 5 : ℝ)) s := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · have hz : 0 < x - s := sub_pos.mpr hs
    have h₁ := (Real.hasDerivAt_rpow_const (p := (9 / 5 : ℝ)) (Or.inl hz.ne'))
      |>.comp_const_sub x s
    have h₂ := (Real.hasDerivAt_rpow_const (p := (4 / 5 : ℝ)) (Or.inl hz.ne'))
      |>.comp_const_sub x s
    have hd := (h₁.const_mul (5 / 9 : ℝ)).add
      (h₂.neg.const_mul ((5 / 4 : ℝ) * (x + c)))
    have heq : splineHingePrimitive x c =ᶠ[𝓝 s] fun t : ℝ ↦
        (5 / 9 : ℝ) * (x - t) ^ (9 / 5 : ℝ) +
          (5 / 4 : ℝ) * (x + c) * (-(x - t) ^ (4 / 5 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hs] with t ht
      simp only [splineHingePrimitive, signedRealPower,
        abs_of_neg (sub_neg.mpr ht), max_eq_right (sub_nonpos.mpr ht.le),
        Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0), zero_sub, neg_sub,
        max_eq_left (sub_nonneg.mpr ht.le)]
    have hh := hd.congr_of_eventuallyEq heq
    convert hh using 1
    rw [abs_of_neg (sub_neg.mpr hs), neg_sub]
    norm_num only [show (9 / 5 : ℝ) - 1 = 4 / 5 by norm_num,
      show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num]
    rw [rpow_four_fifths hz]
    ring_nf
  · have hz : 0 < s - x := sub_pos.mpr hs
    have h₁ := (Real.hasDerivAt_rpow_const (p := (9 / 5 : ℝ)) (Or.inl hz.ne'))
      |>.comp_sub_const s x
    have h₂ := (Real.hasDerivAt_rpow_const (p := (4 / 5 : ℝ)) (Or.inl hz.ne'))
      |>.comp_sub_const s x
    have hd := (h₁.const_mul (5 / 9 : ℝ)).add
      (h₂.const_mul ((5 / 4 : ℝ) * (x + c)))
    have heq : splineHingePrimitive x c =ᶠ[𝓝 s] fun t : ℝ ↦
        (5 / 9 : ℝ) * (t - x) ^ (9 / 5 : ℝ) +
          (5 / 4 : ℝ) * (x + c) * (t - x) ^ (4 / 5 : ℝ) := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      simp only [splineHingePrimitive, signedRealPower,
        abs_of_pos (sub_pos.mpr ht), max_eq_left (sub_nonneg.mpr ht.le),
        max_eq_right (by linarith : -(t - x) ≤ 0), Real.zero_rpow (by norm_num :
          (4 / 5 : ℝ) ≠ 0), sub_zero]
    have hh := hd.congr_of_eventuallyEq heq
    convert hh using 1
    rw [abs_of_pos hz]
    norm_num only [show (9 / 5 : ℝ) - 1 = 4 / 5 by norm_num,
      show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num]
    rw [rpow_four_fifths hz]
    ring_nf

/-- The genuine locally integrable absolute power, including its singular point. -/
theorem intervalIntegrable_abs_sub_rpow {p : ℝ} (hp : -1 < p) (x a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ |s - x| ^ p) volume a b := by
  have h : ∀ d : ℝ, IntervalIntegrable (fun s : ℝ ↦ |s - x| ^ p) volume x d := by
    intro d
    rcases le_total x d with hd | hd
    · have hi := (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := d - x))
        |>.comp_sub_right x
      have hi' : IntervalIntegrable (fun s : ℝ ↦ (s - x) ^ p) volume x d := by
        simpa only [zero_add, sub_add_cancel] using hi
      apply hi'.congr_uIoo
      intro s hs
      rw [uIoo_of_le hd] at hs
      dsimp only
      rw [abs_of_nonneg (by linarith [hs.1] : 0 ≤ s - x)]
    · have hi := (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := x - d))
        |>.comp_sub_left x
      have hi' : IntervalIntegrable (fun s : ℝ ↦ (x - s) ^ p) volume x d := by
        simpa only [sub_zero, sub_sub_cancel] using hi
      apply hi'.congr_uIoo
      intro s hs
      rw [uIoo_of_ge hd] at hs
      dsimp only
      rw [abs_of_nonpos (by linarith [hs.2] : s - x ≤ 0), neg_sub]
  exact (h a).symm.trans (h b)

/-- The singular hinge integral is its actual primitive difference. -/
theorem integral_splineHinge {x c a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (s + c) * |s - x| ^ (-1 / 5 : ℝ)) =
      splineHingePrimitive x c b - splineHingePrimitive x c a := by
  have hi (d e : ℝ) : IntervalIntegrable
      (fun s : ℝ ↦ (s + c) * |s - x| ^ (-1 / 5 : ℝ)) volume d e :=
    (intervalIntegrable_abs_sub_rpow (by norm_num : (-1 : ℝ) < -1 / 5) x d e)
      |>.continuousOn_mul (continuous_id.add continuous_const).continuousOn
  have hleft {d e : ℝ} (hde : d ≤ e) (he : e ≤ x) :
      (∫ s in d..e, (s + c) * |s - x| ^ (-1 / 5 : ℝ)) =
        splineHingePrimitive x c e - splineHingePrimitive x c d := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hde
      (continuous_splineHingePrimitive x c).continuousOn _ (hi d e)
    intro s hs
    exact hasDerivAt_splineHingePrimitive (by linarith [hs.2])
  have hright {d e : ℝ} (hde : d ≤ e) (hd : x ≤ d) :
      (∫ s in d..e, (s + c) * |s - x| ^ (-1 / 5 : ℝ)) =
        splineHingePrimitive x c e - splineHingePrimitive x c d := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hde
      (continuous_splineHingePrimitive x c).continuousOn _ (hi d e)
    intro s hs
    exact hasDerivAt_splineHingePrimitive (by linarith [hs.1])
  by_cases hx : x ≤ a
  · exact hright hab hx
  by_cases hx' : b ≤ x
  · exact hleft hab hx'
  have hax : a ≤ x := le_of_not_ge hx
  have hxb : x ≤ b := le_of_not_ge hx'
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a x) (hi x b),
    hleft hax le_rfl, hright hxb le_rfl]
  ring

end PartialBalayage.Maximal.Square
