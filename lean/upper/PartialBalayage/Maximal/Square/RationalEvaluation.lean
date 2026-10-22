/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32 instead of 1/16. -/
module

public import PartialBalayage.Maximal.Square.MajorizationLeaf

/-!
# Rational evaluation of the genuine lower polynomial

These generic identities eliminate multivariate polynomial operations before any literal
coefficient arithmetic is evaluated. They are ordinary equalities of rational expressions.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace PartialBalayage.Maximal.Square

/-- The actual affine triangle map with rational, rather than real, parameters. -/
def RationalTriangle.rationalPoint (T : RationalTriangle) (z : Fin 2 → ℚ) : ℚ × ℚ :=
  (T.v₀.1 + (T.v₁.1 - T.v₀.1) * z 0 + (T.v₂.1 - T.v₀.1) * z 1,
    T.v₀.2 + (T.v₁.2 - T.v₀.2) * z 0 + (T.v₂.2 - T.v₀.2) * z 1)

theorem affinePlanePolynomial_eval_rat (a b c : ℚ) (z : Fin 2 → ℚ) :
    (affinePlanePolynomial a b c).eval z = a + (b - a) * z 0 + (c - a) * z 1 := by
  simp only [affinePlanePolynomial, eval_add, eval_mul, eval_C, eval_X]

theorem RationalTriangle.xPolynomial_eval_rat (T : RationalTriangle) (z : Fin 2 → ℚ) :
    T.xPolynomial.eval z = (T.rationalPoint z).1 :=
  affinePlanePolynomial_eval_rat _ _ _ _

theorem RationalTriangle.yPolynomial_eval_rat (T : RationalTriangle) (z : Fin 2 → ℚ) :
    T.yPolynomial.eval z = (T.rationalPoint z).2 :=
  affinePlanePolynomial_eval_rat _ _ _ _

/-- The actual lower polynomial evaluates to its finite rational bicubic expression. -/
theorem lowerPullbackPolynomial_eval_rat (k l : ℤ) (T : RationalTriangle)
    (q height slope target : ℚ) (z : Fin 2 → ℚ) :
    (lowerPullbackPolynomial k l T q height slope target).eval z =
      (∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        correctionCellCoefficient k l a b *
          ((T.rationalPoint z).1 ^ a * (T.rationalPoint z).2 ^ b)) +
      (height + slope * (q - (k + l) / 32) - target) -
        (slope / 32) * ((T.rationalPoint z).1 + (T.rationalPoint z).2) := by
  simp only [lowerPullbackPolynomial, correctionPullbackPolynomial, eval_sub, eval_add,
    eval_mul, eval_sum, eval_C, eval_pow, T.xPolynomial_eval_rat, T.yPolynomial_eval_rat]

end PartialBalayage.Maximal.Square
