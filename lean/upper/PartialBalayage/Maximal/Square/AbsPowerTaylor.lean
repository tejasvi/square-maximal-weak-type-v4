/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: power 73/40 instead of 9/5 (Taylor coefficients 73/40, 2409/3200, -5621/128000; far-knot constant 264187/20480000; boundary constant 33/40). -/
module

public import PartialBalayage.Maximal.Square.PowerBoundaryRemainder

/-!
# Genuine absolute-power approximations on certificate intervals

Reflection of the positive power supplies the actual signed coefficients on negative
intervals. Both the far-knot cubic bound and the boundary-knot linear bound apply to
the exact absolute power used by the spline generator.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The exact sign of a nonzero certificate center. -/
def powerCenterSign (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- The actual cubic Taylor polynomial of the absolute power at a nonzero center. -/
def absPowerTaylorThree (a x : ℝ) : ℝ :=
  |a| ^ (73 / 40 : ℝ) + (73 / 40 : ℝ) * powerCenterSign a * |a| ^ (33 / 40 : ℝ) * (x - a) +
    (2409 / 3200 : ℝ) * |a| ^ (-7 / 40 : ℝ) * (x - a) ^ (2 : ℕ) -
      (5621 / 128000 : ℝ) * powerCenterSign a * |a| ^ (-47 / 40 : ℝ) * (x - a) ^ (3 : ℕ)

/-- The actual linear Taylor polynomial, used when an interval touches the joining point. -/
def absPowerTaylorOne (a x : ℝ) : ℝ :=
  |a| ^ (73 / 40 : ℝ) + (73 / 40 : ℝ) * powerCenterSign a * |a| ^ (33 / 40 : ℝ) * (x - a)

theorem absPowerTaylorThree_of_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    absPowerTaylorThree a x = powerTaylorThree a x := by
  simp only [absPowerTaylorThree, powerTaylorThree, powerCenterSign, ite_eq_left ha,
    abs_of_pos ha, mul_one]

theorem absPowerTaylorThree_of_neg {a : ℝ} (ha : a < 0) (x : ℝ) :
    absPowerTaylorThree a x = powerTaylorThree (-a) (-x) := by
  simp only [absPowerTaylorThree, powerTaylorThree, powerCenterSign,
    ite_eq_right (not_lt_of_ge ha.le), abs_of_neg ha]
  ring

/-- The exact far-knot Taylor bound for the genuine absolute power. -/
theorem abs_absRpow_nine_fifths_sub_taylorThree_le {a δ x : ℝ}
    (hδ : 0 ≤ δ) (haδ : δ < |a|) (hx : |x - a| ≤ δ) :
    |(|x| ^ (73 / 40 : ℝ) - absPowerTaylorThree a x)| ≤
      (264187 / 20480000 : ℝ) * δ ^ (4 : ℕ) * (|a| - δ) ^ (-87 / 40 : ℝ) := by
  have ha₀ : a ≠ 0 := by
    intro h
    have hh := hδ.trans_lt haδ
    rw [h, abs_zero] at hh
    exact (lt_irrefl (0 : ℝ)) hh
  rcases lt_or_gt_of_ne ha₀ with ha | ha
  · have hxneg : x < 0 := by rw [abs_of_neg ha] at haδ; linarith [le_abs_self (x - a)]
    have hdist : |-x - (-a)| = |x - a| := by
      rw [show -x - (-a) = -(x - a) by ring, abs_neg]
    have hb := abs_rpow_nine_fifths_sub_taylorThree_le (a := -a) (x := -x) hδ
      (by simpa only [abs_of_neg ha] using haδ) (by simpa only [hdist] using hx)
    simpa only [abs_of_neg hxneg, absPowerTaylorThree_of_neg ha, abs_of_neg ha] using hb
  · have hxpos : 0 < x := by rw [abs_of_pos ha] at haδ; linarith [neg_abs_le (x - a)]
    have hb := abs_rpow_nine_fifths_sub_taylorThree_le hδ
      (by simpa only [abs_of_pos ha] using haδ) hx
    simpa only [abs_of_pos hxpos, absPowerTaylorThree_of_pos ha, abs_of_pos ha] using hb

/-- The exact boundary-knot Taylor bound, including the joining point itself. -/
theorem abs_absRpow_nine_fifths_sub_taylorOne_le {a x : ℝ}
    (ha : a ≠ 0) (hx : |x - a| ≤ |a|) :
    |(|x| ^ (73 / 40 : ℝ) - absPowerTaylorOne a x)| ≤
      (33 / 40 : ℝ) * |a| ^ (73 / 40 : ℝ) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hxnonpos : x ≤ 0 := by rw [abs_of_neg ha] at hx; linarith [le_abs_self (x - a)]
    have hxlo : 2 * a ≤ x := by rw [abs_of_neg ha] at hx; linarith [neg_abs_le (x - a)]
    have hb := abs_powerLinearRemainder_le (a := -a) (x := -x) (neg_pos.mpr ha)
      (neg_nonneg.mpr hxnonpos) (by linarith)
    have heq : powerLinearRemainder (-a) (-x) =
        |x| ^ (73 / 40 : ℝ) - absPowerTaylorOne a x := by
      simp only [powerLinearRemainder, absPowerTaylorOne, powerCenterSign,
        ite_eq_right (not_lt_of_ge ha.le), abs_of_nonpos hxnonpos, abs_of_neg ha]
      ring
    simpa only [heq, abs_of_neg ha] using hb
  · have hxnonneg : 0 ≤ x := by rw [abs_of_pos ha] at hx; linarith [neg_abs_le (x - a)]
    have hxhi : x ≤ 2 * a := by rw [abs_of_pos ha] at hx; linarith [le_abs_self (x - a)]
    have hb := abs_powerLinearRemainder_le ha hxnonneg hxhi
    simpa only [powerLinearRemainder, absPowerTaylorOne, powerCenterSign, ite_eq_left ha,
      abs_of_nonneg hxnonneg, abs_of_pos ha, mul_one] using hb

end PartialBalayage.Maximal.Square
