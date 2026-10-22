/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.PolynomialEvaluation
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Sound rational array normalization of actual plane polynomials

A finite rational monomial array is an actual multivariate polynomial. Equality of
rational evaluations implies genuine polynomial equality, so a ring-checked normalization
also identifies every actual coefficient used in the Bernstein majorization theorem.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace PartialBalayage.Maximal.Square

theorem triangleExponent_injective : Function.Injective triangleExponent := by
  intro p q h
  apply Prod.ext
  · have h₀ := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
    simpa only [triangleExponent_zero] using h₀
  · have h₁ := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
    simpa only [triangleExponent_one] using h₁

theorem planeMonomial_eq (a b : ℕ) (c : ℚ) :
    (C c * X (0 : Fin 2) ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℚ) =
      monomial (triangleExponent (a, b)) c := by
  rw [C_mul_X_pow_eq_monomial, ← monomial_add_single]
  rfl

/-- A literal triangular monomial array regarded as an actual rational polynomial. -/
def planeArrayPolynomial (c : ℕ × ℕ → ℚ) : MvPolynomial (Fin 2) ℚ :=
  ∑ p ∈ triangleIndices, C (c p) * X 0 ^ p.1 * X 1 ^ p.2

theorem planeArrayPolynomial_eval (c : ℕ × ℕ → ℚ) (z : Fin 2 → ℚ) :
    (planeArrayPolynomial c).eval z =
      ∑ p ∈ triangleIndices, c p * (z 0 ^ p.1 * z 1 ^ p.2) := by
  simp only [planeArrayPolynomial, eval_sum, eval_mul, eval_C, eval_pow, eval_X, mul_assoc]

/-- Every entry in the literal array is the genuine coefficient of its actual polynomial. -/
theorem planeArrayPolynomial_coefficient (c : ℕ × ℕ → ℚ) {p : ℕ × ℕ}
    (hp : p ∈ triangleIndices) :
    planePolynomialCoefficients (planeArrayPolynomial c) p = c p := by
  simp only [planePolynomialCoefficients, planeArrayPolynomial, planeMonomial_eq,
    coeff_sum, coeff_monomial, triangleExponent_injective.eq_iff]
  simp only [Finset.sum_ite_eq', hp, ↓reduceIte]

/-- The actual Bernstein coefficients equal the transparent finite-array calculation. -/
theorem planeArrayPolynomial_bernsteinCoefficient (c : ℕ × ℕ → ℚ) (a b : ℕ) :
    triangleBernsteinCoefficient (planePolynomialCoefficients (planeArrayPolynomial c)) a b =
      triangleBernsteinCoefficient c a b := by
  unfold triangleBernsteinCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  rw [planeArrayPolynomial_coefficient c hp]

/-- A rational evaluation check establishes actual multivariate polynomial equality. -/
theorem planePolynomial_eq_array_of_eval (P : MvPolynomial (Fin 2) ℚ)
    (c : ℕ × ℕ → ℚ)
    (h : ∀ z : Fin 2 → ℚ, P.eval z =
      ∑ p ∈ triangleIndices, c p * (z 0 ^ p.1 * z 1 ^ p.2)) :
    P = planeArrayPolynomial c := by
  apply MvPolynomial.funext
  intro z
  rw [h z, planeArrayPolynomial_eval]

/-- Ring-checked normalization identifies the actual coefficients in the leaf theorem. -/
theorem planePolynomialCoefficients_eq_array_of_eval (P : MvPolynomial (Fin 2) ℚ)
    (c : ℕ × ℕ → ℚ)
    (h : ∀ z : Fin 2 → ℚ, P.eval z =
      ∑ p ∈ triangleIndices, c p * (z 0 ^ p.1 * z 1 ^ p.2))
    {p : ℕ × ℕ} (hp : p ∈ triangleIndices) : planePolynomialCoefficients P p = c p := by
  rw [planePolynomial_eq_array_of_eval P c h]
  exact planeArrayPolynomial_coefficient c hp

end PartialBalayage.Maximal.Square
