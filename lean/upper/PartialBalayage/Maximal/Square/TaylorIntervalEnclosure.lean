/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: power 73/40 instead of 9/5; the enclosures are 40th-power checks (IsPowerEnclosureDeg 40) with exponent numerators 73, 33, -7, -47, -87. -/
module

public import PartialBalayage.Maximal.Square.AbsPowerTaylor
public import PartialBalayage.Maximal.Square.RationalInterval

/-!
# Exact enclosures of genuine spline-generator Taylor coefficients

Four ordinary rational 40th-power checks enclose the actual cubic coefficients.
A fifth such check supplies the rigorous far-knot remainder. Intervals touching a
knot instead use the genuine linear approximation and its proved boundary error.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The exact sign used by the rational coefficient calculation. -/
def rationalCenterSign (a : ℚ) : ℚ := if 0 < a then 1 else -1

theorem rationalCenterSign_cast (a : ℚ) :
    (rationalCenterSign a : ℝ) = powerCenterSign (a : ℝ) := by
  unfold rationalCenterSign powerCenterSign
  split_ifs with h h' h'
  · norm_num
  · exact False.elim (h' (by exact_mod_cast h))
  · exact False.elim (h (by exact_mod_cast h'))
  · norm_num

/-- Actual cubic coefficients in powers of the displacement from the center. -/
def absPowerTaylorCoefficients (a : ℝ) : Fin 4 → ℝ :=
  ![|a| ^ (73 / 40 : ℝ), (73 / 40 : ℝ) * powerCenterSign a * |a| ^ (33 / 40 : ℝ),
    (2409 / 3200 : ℝ) * |a| ^ (-7 / 40 : ℝ),
    (-5621 / 128000 : ℝ) * powerCenterSign a * |a| ^ (-47 / 40 : ℝ)]

/-- Rational interval coefficients assembled from the four genuine powers. -/
def absPowerTaylorIntervals (a : ℚ) (P : Fin 4 → RationalInterval) :
    Fin 4 → RationalInterval :=
  ![P 0, (P 1).scale ((73 / 40) * rationalCenterSign a), (P 2).scale (2409 / 3200),
    (P 3).scale ((-5621 / 128000) * rationalCenterSign a)]

/-- The four exact integer numerators of the fractional exponents (denominator 40). -/
def absPowerTaylorExponents : Fin 4 → ℤ := ![73, 33, -7, -47]

theorem absPowerTaylorCoefficients_eval (a x : ℝ) :
    (∑ i : Fin 4, absPowerTaylorCoefficients a i * (x - a) ^ i.val) =
      absPowerTaylorThree a x := by
  simp only [Fin.sum_univ_succ, absPowerTaylorCoefficients, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num [absPowerTaylorThree]
  ring

/-- Ordinary 40th-power checks enclose every actual cubic Taylor coefficient. -/
theorem absPowerTaylorIntervals_contains (a : ℚ) (P : Fin 4 → RationalInterval)
    (hP : ∀ i, IsPowerEnclosureDeg 40 |a| (absPowerTaylorExponents i) (P i).lower (P i).upper) :
    ∀ i, (absPowerTaylorIntervals a P i).Contains
      (absPowerTaylorCoefficients (a : ℝ) i) := by
  have hp (i : Fin 4) := (hP i).rpow_bounds (by norm_num) (abs_nonneg a)
  have h₀ : (P 0).Contains (|(a : ℝ)| ^ (73 / 40 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 0
  have h₁ : (P 1).Contains (|(a : ℝ)| ^ (33 / 40 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 1
  have h₂ : (P 2).Contains (|(a : ℝ)| ^ (-7 / 40 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 2
  have h₃ : (P 3).Contains (|(a : ℝ)| ^ (-47 / 40 : ℝ)) := by
    simpa [absPowerTaylorExponents, RationalInterval.Contains] using hp 3
  intro i
  fin_cases i
  · simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients] using h₀
  · have hb := h₁.scale ((73 / 40) * rationalCenterSign a)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients,
      rationalCenterSign_cast] using hb
  · have hb := h₂.scale (2409 / 3200)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients] using hb
  · have hb := h₃.scale ((-5621 / 128000) * rationalCenterSign a)
    simpa [absPowerTaylorIntervals, absPowerTaylorCoefficients,
      rationalCenterSign_cast] using hb

/-- The far-knot error is bounded by a kernel-checked rational 40th-power enclosure. -/
theorem absPowerTaylorThree_error_le_rational {a δ : ℚ} {x : ℝ}
    (hδ : 0 ≤ δ) (haδ : δ < |a|) (hx : |x - (a : ℝ)| ≤ (δ : ℝ))
    (P : RationalInterval) (hP : IsPowerEnclosureDeg 40 (|a| - δ) (-87) P.lower P.upper) :
    |(|x| ^ (73 / 40 : ℝ) - absPowerTaylorThree (a : ℝ) x)| ≤
      ((264187 / 20480000 * δ ^ (4 : ℕ) * P.upper : ℚ) : ℝ) := by
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have haδ' : (δ : ℝ) < |(a : ℝ)| := by exact_mod_cast haδ
  have hp := hP.rpow_bounds (by norm_num) (by linarith : 0 ≤ |a| - δ)
  have hb := abs_absRpow_nine_fifths_sub_taylorThree_le hδ' haδ' hx
  apply hb.trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Rat.cast_sub, Rat.cast_abs, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using hp.2

/-- The boundary-knot error uses its true linear remainder, including the knot itself. -/
theorem absPowerTaylorOne_error_le_rational {a : ℚ} {x : ℝ} (ha : a ≠ 0)
    (hx : |x - (a : ℝ)| ≤ |(a : ℝ)|) (P : RationalInterval)
    (hP : IsPowerEnclosureDeg 40 |a| 73 P.lower P.upper) :
    |(|x| ^ (73 / 40 : ℝ) - absPowerTaylorOne (a : ℝ) x)| ≤
      ((33 / 40 * P.upper : ℚ) : ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb := abs_absRpow_nine_fifths_sub_taylorOne_le ha' hx
  have hp := hP.rpow_bounds (by norm_num) (abs_nonneg a)
  apply hb.trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Rat.cast_abs, Int.cast_ofNat, Nat.cast_ofNat] using hp.2

end PartialBalayage.Maximal.Square
