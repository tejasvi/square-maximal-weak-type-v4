/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.RectanglePolynomialBound

/-!
# Bernstein lower bounds for centered tensor-cubic rectangle polynomials

On the square `|x|, |y| ≤ δ` a tensor cubic is a convex combination of its sixteen Bernstein
coefficients (in the variables `(x + δ) / (2δ)` and `(y + δ) / (2δ)`), so the least of them bounds
the polynomial from below. With interval coefficients every Bernstein coefficient is bounded below
by choosing the endpoint that matches the sign of its weight.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- Bernstein coefficients of `(2s - 1)^i` in degree three: row `i`, column `k`. -/
def bernsteinPowerMatrix : Fin 4 → Fin 4 → ℚ :=
  ![![1, 1, 1, 1], ![-1, -1 / 3, 1 / 3, 1], ![1, -1 / 3, -1 / 3, 1], ![-1, 1, -1, 1]]

/-- The weight of the monomial `p` in the Bernstein coefficient `(k, l)`. -/
def bernsteinWeight (δ : ℚ) (p : RectangleIndex) (k l : Fin 4) : ℚ :=
  δ ^ (p.1.val + p.2.val) * bernsteinPowerMatrix p.1 k * bernsteinPowerMatrix p.2 l

/-- A lower bound of one Bernstein coefficient from the coefficient intervals. -/
def bernsteinCoefficientLower (C : RectangleIndex → RationalInterval) (δ : ℚ) (k l : Fin 4) : ℚ :=
  ∑ p, if 0 ≤ bernsteinWeight δ p k l then bernsteinWeight δ p k l * (C p).lower
    else bernsteinWeight δ p k l * (C p).upper

/-- The least of the sixteen Bernstein coefficient lower bounds. -/
def bernsteinIntervalLower (C : RectangleIndex → RationalInterval) (δ : ℚ) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun q : Fin 4 × Fin 4 ↦ bernsteinCoefficientLower C δ q.1 q.2)

/-- The cubic Bernstein basis on `[-δ, δ]`, scaled by `δ ^ 3`. -/
noncomputable def bernsteinBasis (δ x : ℝ) : Fin 4 → ℝ :=
  ![(δ - x) ^ 3 / 8, 3 * (δ + x) * (δ - x) ^ 2 / 8, 3 * (δ + x) ^ 2 * (δ - x) / 8, (δ + x) ^ 3 / 8]

theorem bernsteinBasis_nonneg {δ x : ℝ} (hx : |x| ≤ δ) (k : Fin 4) : 0 ≤ bernsteinBasis δ x k := by
  have h1 : 0 ≤ δ - x := by linarith [le_abs_self x]
  have h2 : 0 ≤ δ + x := by linarith [neg_abs_le x]
  fin_cases k <;> simp [bernsteinBasis] <;> positivity

/-- The real Bernstein coefficient of a tensor cubic. -/
noncomputable def bernsteinCoefficient (c : RectangleIndex → ℝ) (δ : ℝ) (k l : Fin 4) : ℝ :=
  ∑ p : RectangleIndex, δ ^ (p.1.val + p.2.val) * (bernsteinPowerMatrix p.1 k : ℝ) *
    (bernsteinPowerMatrix p.2 l : ℝ) * c p

private theorem fin4_val_three : ((3 : Fin 4) : ℕ) = 3 := rfl

/-- The Bernstein form of a tensor cubic, multiplied by `δ ^ 6`. -/
theorem bernstein_expansion (c : RectangleIndex → ℝ) (δ x y : ℝ) :
    δ ^ 6 * rectanglePolynomial c x y =
      ∑ k, ∑ l, bernsteinBasis δ x k * bernsteinBasis δ y l * bernsteinCoefficient c δ k l := by
  simp only [rectanglePolynomial, bernsteinCoefficient, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp only [bernsteinBasis, bernsteinPowerMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero,
    Fin.val_one, Fin.val_two, fin4_val_three, Fin.isValue]
  push_cast
  ring

theorem bernsteinBasis_sum (δ x y : ℝ) :
    ∑ k, ∑ l, bernsteinBasis δ x k * bernsteinBasis δ y l = δ ^ 6 := by
  simp only [bernsteinBasis, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  ring

theorem bernsteinCoefficientLower_le {c : RectangleIndex → ℝ} {C : RectangleIndex → RationalInterval}
    (hC : ∀ p, (C p).Contains (c p)) (δ : ℚ) (k l : Fin 4) :
    (bernsteinCoefficientLower C δ k l : ℝ) ≤ bernsteinCoefficient c δ k l := by
  unfold bernsteinCoefficientLower bernsteinCoefficient
  push_cast
  apply Finset.sum_le_sum
  intro p _
  have hw : ((bernsteinWeight δ p k l : ℚ) : ℝ) =
      (δ : ℝ) ^ (p.1.val + p.2.val) * (bernsteinPowerMatrix p.1 k : ℝ) *
        (bernsteinPowerMatrix p.2 l : ℝ) := by
    simp [bernsteinWeight]
  split_ifs with h
  · have h' : (0 : ℝ) ≤ (bernsteinWeight δ p k l : ℝ) := by exact_mod_cast h
    rw [← hw]
    exact_mod_cast (mul_le_mul_of_nonneg_left (hC p).1 h')
  · have h' : ((bernsteinWeight δ p k l : ℚ) : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    rw [← hw]
    exact_mod_cast (mul_le_mul_of_nonpos_left (hC p).2 h')

theorem bernsteinIntervalLower_le_coefficient (C : RectangleIndex → RationalInterval) (δ : ℚ)
    (k l : Fin 4) : bernsteinIntervalLower C δ ≤ bernsteinCoefficientLower C δ k l :=
  Finset.inf'_le (fun q : Fin 4 × Fin 4 ↦ bernsteinCoefficientLower C δ q.1 q.2)
    (Finset.mem_univ (k, l))

/-- Exact coefficient enclosures yield a true lower bound on the whole rectangle. -/
theorem bernsteinIntervalLower_le {c : RectangleIndex → ℝ}
    {C : RectangleIndex → RationalInterval} {δ : ℚ} {x y : ℝ}
    (hC : ∀ p, (C p).Contains (c p)) (hδ : 0 ≤ δ)
    (hx : |x| ≤ (δ : ℝ)) (hy : |y| ≤ (δ : ℝ)) :
    (bernsteinIntervalLower C δ : ℝ) ≤ rectanglePolynomial c x y := by
  set L : ℝ := ((bernsteinIntervalLower C δ : ℚ) : ℝ) with hLdef
  have hL : ∀ k l, L ≤ bernsteinCoefficient c δ k l := fun k l ↦
    (Rat.cast_le.mpr (bernsteinIntervalLower_le_coefficient C δ k l)).trans
      (bernsteinCoefficientLower_le hC δ k l)
  rcases hδ.lt_or_eq with hpos | hzero
  · have hpos' : (0 : ℝ) < δ := by exact_mod_cast hpos
    have h6 : (0 : ℝ) < (δ : ℝ) ^ 6 := by positivity
    have hsum : (δ : ℝ) ^ 6 * L ≤ (δ : ℝ) ^ 6 * rectanglePolynomial c x y := by
      rw [bernstein_expansion, ← bernsteinBasis_sum (δ : ℝ) x y, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (hL k l)
        (mul_nonneg (bernsteinBasis_nonneg hx k) (bernsteinBasis_nonneg hy l))
    exact le_of_mul_le_mul_left hsum h6
  · subst hzero
    have hx0 : x = 0 := abs_nonpos_iff.mp (by simpa using hx)
    have hy0 : y = 0 := abs_nonpos_iff.mp (by simpa using hy)
    subst hx0 hy0
    have h00 := hL 0 0
    have hc : bernsteinCoefficient c ((0 : ℚ) : ℝ) 0 0 = c (0, 0) := by
      simp [bernsteinCoefficient, bernsteinPowerMatrix, Fintype.sum_prod_type, Fin.sum_univ_four]
    have hp : rectanglePolynomial c 0 0 = c (0, 0) := by
      simp [rectanglePolynomial, Fintype.sum_prod_type, Fin.sum_univ_four]
    linarith

/-- A proved approximation error is subtracted from the Bernstein lower bound. -/
theorem bernsteinIntervalLower_sub_error_le {c : RectangleIndex → ℝ}
    {C : RectangleIndex → RationalInterval} {δ E : ℚ} {x y z : ℝ}
    (hC : ∀ p, (C p).Contains (c p)) (hδ : 0 ≤ δ)
    (hx : |x| ≤ (δ : ℝ)) (hy : |y| ≤ (δ : ℝ))
    (hz : |z - rectanglePolynomial c x y| ≤ (E : ℝ)) :
    ((bernsteinIntervalLower C δ - E : ℚ) : ℝ) ≤ z := by
  have hb := bernsteinIntervalLower_le hC hδ hx hy
  rw [Rat.cast_sub]
  linarith [neg_abs_le (z - rectanglePolynomial c x y)]

end PartialBalayage.Maximal.Square
