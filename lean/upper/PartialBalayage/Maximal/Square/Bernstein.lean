/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Tactic

/-!
# Exact triangular Bernstein certificates of degree six

The rational change of basis is proved as a real polynomial identity. Nonnegative
certificate coefficients therefore imply a genuine pointwise polynomial inequality on
the closed unit triangle. The finite checks use ordinary kernel reduction and ring proofs.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- All monomial and Bernstein indices of total degree at most six. -/
def triangleIndices : Finset (ℕ × ℕ) :=
  ((Finset.range 7).product (Finset.range 7)).filter (fun p ↦ p.1 + p.2 ≤ 6)

/-- The genuine triangular Bernstein basis of total degree six. -/
def triangleBernstein (a b : ℕ) (x y : ℝ) : ℝ :=
  (Nat.choose 6 a * Nat.choose (6 - a) b : ℕ) * x ^ a * y ^ b *
    (1 - x - y) ^ (6 - a - b)

/-- The exact rational coefficient of one monomial in the triangular Bernstein basis. -/
def monomialBernsteinCoefficient (i j a b : ℕ) : ℚ :=
  if i ≤ a ∧ j ≤ b then
    (Nat.choose a i * Nat.choose b j : ℕ) /
      (Nat.choose 6 (i + j) * Nat.choose (i + j) i : ℕ)
  else 0

theorem mem_triangleIndices {a b : ℕ} :
    (a, b) ∈ triangleIndices ↔ a + b ≤ 6 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, h⟩

theorem triangleIndices_card : triangleIndices.card = 28 := by decide

set_option maxHeartbeats 2000000 in
/-- The supplement's rational triangular change of basis is an exact real identity. -/
theorem monomial_eq_triangleBernstein (i j : ℕ) (hij : i + j ≤ 6) (x y : ℝ) :
    x ^ i * y ^ j = ∑ p ∈ triangleIndices,
      (monomialBernsteinCoefficient i j p.1 p.2 : ℝ) *
        triangleBernstein p.1 p.2 x y := by
  have hi : i ≤ 6 := by omega
  have hj : j ≤ 6 := by omega
  interval_cases i <;> interval_cases j <;> try omega
  all_goals norm_num [triangleIndices, monomialBernsteinCoefficient, triangleBernstein,
    Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ, Nat.choose]
  all_goals ring

/-- Every basis function is nonnegative throughout the closed unit triangle. -/
theorem triangleBernstein_nonneg (a b : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    0 ≤ triangleBernstein a b x y := by
  have hz : 0 ≤ 1 - x - y := by linarith
  unfold triangleBernstein
  positivity

/-- The genuine degree-six triangular Bernstein basis is a partition of unity. -/
theorem triangleBernstein_sum (x y : ℝ) :
    ∑ p ∈ triangleIndices, triangleBernstein p.1 p.2 x y = 1 := by
  have h := monomial_eq_triangleBernstein 0 0 (by omega) x y
  simpa only [monomialBernsteinCoefficient, Nat.zero_le, and_self, ↓reduceIte,
    Nat.choose_zero_right, zero_add, Nat.cast_one, one_div, inv_one, Rat.cast_one,
    one_mul, pow_zero, mul_one] using h.symm

/-- A degree-six polynomial in its ordinary monomial coefficients. -/
def trianglePolynomial (c : ℕ × ℕ → ℚ) (x y : ℝ) : ℝ :=
  ∑ p ∈ triangleIndices, (c p : ℝ) * (x ^ p.1 * y ^ p.2)

/-- The exact rational certificate coefficients for an ordinary polynomial. -/
def triangleBernsteinCoefficient (c : ℕ × ℕ → ℚ) (a b : ℕ) : ℚ :=
  ∑ p ∈ triangleIndices, c p * monomialBernsteinCoefficient p.1 p.2 a b

/-- Rational certificate computation reconstructs the actual real polynomial. -/
theorem trianglePolynomial_eq_bernstein (c : ℕ × ℕ → ℚ) (x y : ℝ) :
    trianglePolynomial c x y = ∑ p ∈ triangleIndices,
      (triangleBernsteinCoefficient c p.1 p.2 : ℝ) *
        triangleBernstein p.1 p.2 x y := by
  unfold trianglePolynomial triangleBernsteinCoefficient
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [monomial_eq_triangleBernstein p.1 p.2 (mem_triangleIndices.mp hp),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- An exact finite rational certificate implies pointwise nonnegativity on the triangle. -/
theorem trianglePolynomial_nonneg_of_bernstein (c : ℕ × ℕ → ℚ)
    (hc : ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient c p.1 p.2)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    0 ≤ trianglePolynomial c x y := by
  rw [trianglePolynomial_eq_bernstein]
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (by exact_mod_cast hc p hp)
    (triangleBernstein_nonneg p.1 p.2 hx hy hxy)

end PartialBalayage.Maximal.Square
