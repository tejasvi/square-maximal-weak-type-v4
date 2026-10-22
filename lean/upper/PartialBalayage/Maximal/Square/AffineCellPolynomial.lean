/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32 instead of 1/16. -/
module

public import PartialBalayage.Maximal.Square.CorrectionPolynomial
public import PartialBalayage.Maximal.Square.PolynomialEvaluation
public import PartialBalayage.Maximal.Square.TriangleGeometry
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Actual affine pullbacks of the signed spline correction

The rational polynomial computed on each certificate triangle evaluates to the actual
signed kernel correction. Its degree bound is mathematical, and does not rely on the
external arithmetic checker or on a stored precomputed polynomial equality.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace PartialBalayage.Maximal.Square

/-- The actual affine coordinate polynomial corresponding to three rational values. -/
def affinePlanePolynomial (a b c : ℚ) : MvPolynomial (Fin 2) ℚ :=
  C a + C (b - a) * X 0 + C (c - a) * X 1

/-- The actual first coordinate polynomial of a rational triangle. -/
def RationalTriangle.xPolynomial (T : RationalTriangle) : MvPolynomial (Fin 2) ℚ :=
  affinePlanePolynomial T.v₀.1 T.v₁.1 T.v₂.1

/-- The actual second coordinate polynomial of a rational triangle. -/
def RationalTriangle.yPolynomial (T : RationalTriangle) : MvPolynomial (Fin 2) ℚ :=
  affinePlanePolynomial T.v₀.2 T.v₁.2 T.v₂.2

theorem affinePlanePolynomial_eval (a b c : ℚ) (x y : ℝ) :
    (affinePlanePolynomial a b c).eval₂ (Rat.castHom ℝ) ![x, y] =
      (a : ℝ) + ((b : ℝ) - a) * x + ((c : ℝ) - a) * y := by
  simp only [affinePlanePolynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    Rat.coe_castHom, Rat.cast_sub, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

theorem affinePlanePolynomial_totalDegree (a b c : ℚ) :
    (affinePlanePolynomial a b c).totalDegree ≤ 1 := by
  have h₀ := totalDegree_mul (C (b - a) : MvPolynomial (Fin 2) ℚ) (X 0)
  have h₁ := totalDegree_mul (C (c - a) : MvPolynomial (Fin 2) ℚ) (X 1)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h₀ h₁
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (by simp only [totalDegree_C]; omega) h₀)) h₁)

theorem RationalTriangle.xPolynomial_eval (T : RationalTriangle) (x y : ℝ) :
    T.xPolynomial.eval₂ (Rat.castHom ℝ) ![x, y] = (T.point x y).1 :=
  affinePlanePolynomial_eval _ _ _ _ _

theorem RationalTriangle.yPolynomial_eval (T : RationalTriangle) (x y : ℝ) :
    T.yPolynomial.eval₂ (Rat.castHom ℝ) ![x, y] = (T.point x y).2 :=
  affinePlanePolynomial_eval _ _ _ _ _

/-- The actual signed bicubic cell polynomial after the actual affine triangle substitution. -/
def correctionPullbackPolynomial (k l : ℤ) (T : RationalTriangle) :
    MvPolynomial (Fin 2) ℚ :=
  ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
    C (correctionCellCoefficient k l a b) * (T.xPolynomial ^ a * T.yPolynomial ^ b)

/-- The computed pullback evaluates to the genuine real bicubic polynomial. -/
theorem correctionPullbackPolynomial_eval (k l : ℤ) (T : RationalTriangle) (x y : ℝ) :
    (correctionPullbackPolynomial k l T).eval₂ (Rat.castHom ℝ) ![x, y] =
      bicubicPolynomial (correctionCellCoefficient k l) (T.point x y).1 (T.point x y).2 := by
  simp only [correctionPullbackPolynomial, bicubicPolynomial, eval₂_sum, eval₂_mul,
    eval₂_C, eval₂_pow, Rat.coe_castHom, T.xPolynomial_eval, T.yPolynomial_eval]

/-- Affine substitution preserves the exact total-degree-six bound. -/
theorem correctionPullbackPolynomial_totalDegree (k l : ℤ) (T : RationalTriangle) :
    (correctionPullbackPolynomial k l T).totalDegree ≤ 6 := by
  have hx := affinePlanePolynomial_totalDegree T.v₀.1 T.v₁.1 T.v₂.1
  have hy := affinePlanePolynomial_totalDegree T.v₀.2 T.v₁.2 T.v₂.2
  unfold correctionPullbackPolynomial
  apply totalDegree_finsetSum_le
  intro a ha
  apply totalDegree_finsetSum_le
  intro b hb
  have ha' : a ≤ 3 := by have h := Finset.mem_range.mp ha; omega
  have hb' : b ≤ 3 := by have h := Finset.mem_range.mp hb; omega
  have hp₀ := totalDegree_pow T.xPolynomial a
  have hp₁ := totalDegree_pow T.yPolynomial b
  have hp := totalDegree_mul (T.xPolynomial ^ a) (T.yPolynomial ^ b)
  have hc := totalDegree_mul (C (correctionCellCoefficient k l a b))
    (T.xPolynomial ^ a * T.yPolynomial ^ b)
  simp only [totalDegree_C, zero_add] at hc
  have hx' : T.xPolynomial.totalDegree ≤ 1 := hx
  have hy' : T.yPolynomial.totalDegree ≤ 1 := hy
  have hp₀' := hp₀.trans (Nat.mul_le_mul_left a hx')
  have hp₁' := hp₁.trans (Nat.mul_le_mul_left b hy')
  exact hc.trans (hp.trans (by nlinarith))

/-- The actual affine pullback evaluates to the actual signed correction on its cell. -/
theorem correctionPullbackPolynomial_eval_spline (k l : ℤ) (T : RationalTriangle) (x y : ℝ)
    (hx₀ : 0 ≤ (T.point x y).1) (hx₁ : (T.point x y).1 ≤ 1)
    (hy₀ : 0 ≤ (T.point x y).2) (hy₁ : (T.point x y).2 ≤ 1) :
    (correctionPullbackPolynomial k l T).eval₂ (Rat.castHom ℝ) ![x, y] =
      splineCorrection (((k : ℝ) + (T.point x y).1) / 32)
        (((l : ℝ) + (T.point x y).2) / 32) := by
  rw [correctionPullbackPolynomial_eval, splineCorrection_eq_cellPolynomial k l hx₀ hx₁ hy₀ hy₁]

end PartialBalayage.Maximal.Square
