/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RationalInterval

/-!
# Sound centered rectangle polynomial bounds

The constant coefficient is enclosed from below, and every other monomial is
bounded by its absolute coefficient and the corresponding power of the rectangle
radius. The final rational arithmetic bound therefore applies to the actual real
polynomial throughout the closed rectangle.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The sixteen tensor-cubic indices used by each actual generator rectangle. -/
abbrev RectangleIndex := Fin 4 × Fin 4

/-- Tensor-cubic evaluation in coordinates centered at the rectangle midpoint. -/
def rectanglePolynomial (c : RectangleIndex → ℝ) (x y : ℝ) : ℝ :=
  ∑ p, c p * x ^ p.1.val * y ^ p.2.val

/-- The transparent exact rational lower bound used by a rectangle leaf. -/
def rectangleIntervalLower (c : RectangleIndex → RationalInterval) (δ : ℚ) : ℚ :=
  (c (0, 0)).lower -
    ∑ p ∈ Finset.univ.erase (0, 0), (c p).absBound * δ ^ (p.1.val + p.2.val)

theorem abs_rectangle_monomial_le {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hx : |x| ≤ δ) (hy : |y| ≤ δ) (p : RectangleIndex) :
    |x ^ p.1.val * y ^ p.2.val| ≤ δ ^ (p.1.val + p.2.val) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx _)
    (pow_le_pow_left₀ (abs_nonneg _) hy _) (by positivity) (by positivity)

/-- Exact coefficient enclosures yield a true lower bound on the whole rectangle. -/
theorem rectangleIntervalLower_le {c : RectangleIndex → ℝ}
    {C : RectangleIndex → RationalInterval} {δ : ℚ} {x y : ℝ}
    (hC : ∀ p, (C p).Contains (c p)) (hδ : 0 ≤ δ)
    (hx : |x| ≤ (δ : ℝ)) (hy : |y| ≤ (δ : ℝ)) :
    (rectangleIntervalLower C δ : ℝ) ≤ rectanglePolynomial c x y := by
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hterm (p : RectangleIndex) :
      -((C p).absBound : ℝ) * (δ : ℝ) ^ (p.1.val + p.2.val) ≤
        c p * x ^ p.1.val * y ^ p.2.val := by
    have hb : |c p * x ^ p.1.val * y ^ p.2.val| ≤
        ((C p).absBound : ℝ) * (δ : ℝ) ^ (p.1.val + p.2.val) := by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul (hC p).abs_le
        (abs_rectangle_monomial_le hδ' hx hy p) (abs_nonneg _) (by
          exact_mod_cast RationalInterval.absBound_nonneg (C p))
    linarith [neg_abs_le (c p * x ^ p.1.val * y ^ p.2.val)]
  have hs := Finset.sum_le_sum (s := Finset.univ.erase (0, 0)) (fun p _ ↦ hterm p)
  have he : rectanglePolynomial c x y = c (0, 0) +
      ∑ p ∈ Finset.univ.erase (0, 0), c p * x ^ p.1.val * y ^ p.2.val := by
    rw [rectanglePolynomial, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0, 0))]
    simp only [Fin.val_zero, pow_zero, mul_one]
    ring
  rw [he]
  simp only [rectangleIntervalLower, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  have hs' : -(∑ p ∈ Finset.univ.erase (0, 0),
      ((C p).absBound : ℝ) * (δ : ℝ) ^ (p.1.val + p.2.val)) ≤
        ∑ p ∈ Finset.univ.erase (0, 0), c p * x ^ p.1.val * y ^ p.2.val := by
    simpa only [neg_mul, Finset.sum_neg_distrib] using hs
  linarith [(hC (0, 0)).1]

/-- A proved approximation error is subtracted from the exact polynomial lower bound. -/
theorem rectangleIntervalLower_sub_error_le {c : RectangleIndex → ℝ}
    {C : RectangleIndex → RationalInterval} {δ E : ℚ} {x y z : ℝ}
    (hC : ∀ p, (C p).Contains (c p)) (hδ : 0 ≤ δ)
    (hx : |x| ≤ (δ : ℝ)) (hy : |y| ≤ (δ : ℝ))
    (hz : |z - rectanglePolynomial c x y| ≤ (E : ℝ)) :
    ((rectangleIntervalLower C δ - E : ℚ) : ℝ) ≤ z := by
  have hb := rectangleIntervalLower_le hC hδ hx hy
  rw [Rat.cast_sub]
  linarith [neg_abs_le (z - rectanglePolynomial c x y)]

end PartialBalayage.Maximal.Square
