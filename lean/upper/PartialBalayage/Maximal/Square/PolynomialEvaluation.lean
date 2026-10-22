/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Bernstein
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Genuine evaluation and Bernstein checks for rational plane polynomials

An arbitrary rational multivariate polynomial of total degree at most six is identified
with its actual triangular coefficient array. This permits affine substitutions to be
checked by ordinary polynomial arithmetic before invoking the real Bernstein theorem.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The genuine two-variable monomial exponent corresponding to a pair of degrees. -/
def triangleExponent (p : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem triangleExponent_zero (p : ℕ × ℕ) : triangleExponent p 0 = p.1 := by
  simp [triangleExponent]

theorem triangleExponent_one (p : ℕ × ℕ) : triangleExponent p 1 = p.2 := by
  simp [triangleExponent]

theorem triangleExponent_reconstruct (d : Fin 2 →₀ ℕ) :
    triangleExponent (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact triangleExponent_zero _
  · exact triangleExponent_one _

/-- The ordinary rational coefficient array of a genuine multivariate polynomial. -/
def planePolynomialCoefficients (P : MvPolynomial (Fin 2) ℚ) (p : ℕ × ℕ) : ℚ :=
  P.coeff (triangleExponent p)

/-- Coefficient extraction reconstructs every actual plane polynomial of degree at most six. -/
theorem planePolynomial_eval_eq_trianglePolynomial (P : MvPolynomial (Fin 2) ℚ)
    (hP : P.totalDegree ≤ 6) (x y : ℝ) :
    P.eval₂ (Rat.castHom ℝ) ![x, y] = trianglePolynomial (planePolynomialCoefficients P) x y := by
  classical
  let S := triangleIndices.filter (fun p ↦ planePolynomialCoefficients P p ≠ 0)
  have hsum : (∑ p ∈ S, (planePolynomialCoefficients P p : ℝ) * (x ^ p.1 * y ^ p.2)) =
      trianglePolynomial (planePolynomialCoefficients P) x y := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hz : planePolynomialCoefficients P p = 0 := by
      simpa only [S, Finset.mem_filter, hp, true_and, not_ne_iff] using hnot
    simp only [hz, Rat.cast_zero, zero_mul]
  rw [← hsum, MvPolynomial.eval₂_eq']
  refine Finset.sum_bij (fun d _ ↦ (d 0, d 1)) ?_ ?_ ?_ ?_
  · intro d hd
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_triangleIndices.mpr
      have ht := (MvPolynomial.le_totalDegree hd).trans hP
      rw [d.sum_fintype (fun _ n ↦ n) (fun _ ↦ rfl)] at ht
      simpa only [Fin.sum_univ_two] using ht
    · simpa only [planePolynomialCoefficients, triangleExponent_reconstruct] using
        (MvPolynomial.mem_support_iff.mp hd)
  · intro d hd e he hde
    have h := congrArg triangleExponent hde
    simpa only [triangleExponent_reconstruct] using h
  · intro p hp
    refine ⟨triangleExponent p, ?_, ?_⟩
    · exact MvPolynomial.mem_support_iff.mpr (Finset.mem_filter.mp hp).2
    · simp only [triangleExponent_zero, triangleExponent_one, Prod.eta]
  · intro d hd
    simp only [Rat.castHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, planePolynomialCoefficients,
      triangleExponent_reconstruct]

/-- Exact rational Bernstein coefficients imply a real inequality for the actual polynomial. -/
theorem planePolynomial_nonneg_of_bernstein (P : MvPolynomial (Fin 2) ℚ)
    (hP : P.totalDegree ≤ 6)
    (hc : ∀ p ∈ triangleIndices,
      0 ≤ triangleBernsteinCoefficient (planePolynomialCoefficients P) p.1 p.2)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    0 ≤ P.eval₂ (Rat.castHom ℝ) ![x, y] := by
  rw [planePolynomial_eval_eq_trianglePolynomial P hP]
  exact trianglePolynomial_nonneg_of_bernstein _ hc hx hy hxy

end PartialBalayage.Maximal.Square
