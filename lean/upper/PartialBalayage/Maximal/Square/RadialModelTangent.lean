/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20). -/
module

public import PartialBalayage.Maximal.Square.RadialTailMoments
public import PartialBalayage.Maximal.Square.RadialTangent
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Actual tangent planes for the finite incoming-tail lower model

The finite incoming polynomial consists of nonnegative powers in the radius and
even powers in the coordinate difference. Each summand has its genuine convex
tangent. Adding those tangents and the negative radial-power tangent proves the
actual affine lower plane used by every generator rectangle.
-/

@[expose] public section

noncomputable section

open Set

namespace PartialBalayage.Maximal.Square

/-- The even part of the genuine integrated-tail coefficient sequence. -/
def radialEvenCoefficient (n : ℕ) : ℚ :=
  if Even n then radialIncomingCoefficient n else 0

/-- The actual finite incoming-tail polynomial in the nonnegative radius coordinate. -/
def radialPositivePolynomial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (radialIncomingCoefficient n : ℝ) * x ^ n

/-- The actual finite even polynomial in the signed coordinate difference. -/
def radialEvenPolynomial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (radialEvenCoefficient n : ℝ) * x ^ n

/-- The exact derivative of a finite coefficient polynomial. -/
def radialPolynomialDerivative (c : ℕ → ℚ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (c n : ℝ) * (n : ℝ) * x ^ (n - 1)

/-- The actual lower model, with downward radial and incoming-tail coefficients. -/
def radialGeneratorLowerModel (S ρ R : ℝ) (N : ℕ) (r d : ℝ) : ℝ :=
  S * r ^ (-47 / 20 : ℝ) +
    2 * ρ * (radialPositivePolynomial N (r / R) + radialEvenPolynomial N (d / R))

/-- The actual radius derivative of the finite lower model. -/
def radialGeneratorLowerModelDr (S ρ R : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (-47 / 20 : ℝ) * S * r ^ (-67 / 20 : ℝ) +
    2 * ρ / R * radialPolynomialDerivative radialIncomingCoefficient N (r / R)

/-- The actual coordinate-difference derivative of the finite lower model. -/
def radialGeneratorLowerModelDd (ρ R : ℝ) (N : ℕ) (d : ℝ) : ℝ :=
  2 * ρ / R * radialPolynomialDerivative radialEvenCoefficient N (d / R)

private theorem convex_tangent_le {s : Set ℝ} {f : ℝ → ℝ} {a x v : ℝ}
    (hc : ConvexOn ℝ s f) (ha : a ∈ s) (hx : x ∈ s) (hd : HasDerivAt f v a) :
    f a + v * (x - a) ≤ f x := by
  rcases lt_trichotomy x a with h | h | h
  · have hs := hc.slope_le_of_hasDerivAt hx ha h hd
    rw [slope_def_field] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · rw [h]
    simp
  · have hs := hc.le_slope_of_hasDerivAt ha hx h hd
    rw [slope_def_field] at hs
    have hs' := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem pow_nat_tangent_nonneg (n : ℕ) {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    a ^ n + (n : ℝ) * a ^ (n - 1) * (x - a) ≤ x ^ n := by
  by_cases h₀ : n = 0
  · subst n
    simp
  by_cases h₁ : n = 1
  · subst n
    simp
  exact convex_tangent_le (strictConvexOn_pow (by omega : 2 ≤ n)).convexOn ha hx
    (hasDerivAt_pow n a)

theorem pow_even_tangent (n : ℕ) (hn : Even n) (a x : ℝ) :
    a ^ n + (n : ℝ) * a ^ (n - 1) * (x - a) ≤ x ^ n := by
  by_cases h₀ : n = 0
  · subst n
    simp
  exact convex_tangent_le (hn.strictConvexOn_pow h₀).convexOn (mem_univ a) (mem_univ x)
    (hasDerivAt_pow n a)

theorem radialPositivePolynomial_tangent {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (N : ℕ) :
    radialPositivePolynomial N a +
      radialPolynomialDerivative radialIncomingCoefficient N a * (x - a) ≤
        radialPositivePolynomial N x := by
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun n _ ↦
    mul_le_mul_of_nonneg_left (pow_nat_tangent_nonneg n ha hx)
      (show (0 : ℝ) ≤ radialIncomingCoefficient n by
        exact_mod_cast radialIncomingCoefficient_nonneg n))
  simpa only [radialPositivePolynomial, radialPolynomialDerivative, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc] using hs

theorem radialEvenPolynomial_tangent (a x : ℝ) (N : ℕ) :
    radialEvenPolynomial N a +
      radialPolynomialDerivative radialEvenCoefficient N a * (x - a) ≤
        radialEvenPolynomial N x := by
  have ht (n : ℕ) : (radialEvenCoefficient n : ℝ) *
      (a ^ n + (n : ℝ) * a ^ (n - 1) * (x - a)) ≤
        (radialEvenCoefficient n : ℝ) * x ^ n := by
    by_cases hn : Even n
    · have hc : (0 : ℝ) ≤ radialEvenCoefficient n := by
        rw [radialEvenCoefficient, ite_eq_left hn]
        exact_mod_cast radialIncomingCoefficient_nonneg n
      exact mul_le_mul_of_nonneg_left (pow_even_tangent n hn a x) hc
    · simp only [radialEvenCoefficient, ite_eq_right hn, Rat.cast_zero, zero_mul]
      exact le_rfl
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun n _ ↦ ht n)
  simpa only [radialEvenPolynomial, radialPolynomialDerivative, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc] using hs

/-- The exact finite model has its genuine affine tangent at every positive radius. -/
theorem radialGeneratorLowerModel_tangent {S ρ R r₀ r d₀ d : ℝ} (N : ℕ)
    (hS : 0 ≤ S) (hρ : 0 ≤ ρ) (hR : 0 < R) (hr₀ : 0 < r₀) (hr : 0 < r) :
    radialGeneratorLowerModel S ρ R N r₀ d₀ +
      radialGeneratorLowerModelDr S ρ R N r₀ * (r - r₀) +
      radialGeneratorLowerModelDd ρ R N d₀ * (d - d₀) ≤
        radialGeneratorLowerModel S ρ R N r d := by
  have hd : HasDerivAt (fun t : ℝ ↦ t ^ (-47 / 20 : ℝ))
      ((-47 / 20 : ℝ) * r₀ ^ (-67 / 20 : ℝ)) r₀ := by
    convert Real.hasDerivAt_rpow_const (p := (-47 / 20 : ℝ)) (Or.inl hr₀.ne') using 1
    norm_num
  have ht₀ := mul_le_mul_of_nonneg_left
    (convex_tangent_le (convexOn_rpow_of_nonpos (-47 / 20) (by norm_num)) hr₀ hr hd) hS
  have ht₁ := mul_le_mul_of_nonneg_left
    (radialPositivePolynomial_tangent (div_nonneg hr₀.le hR.le)
      (div_nonneg hr.le hR.le) N) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ)
  have ht₂ := mul_le_mul_of_nonneg_left (radialEvenPolynomial_tangent (d₀ / R) (d / R) N)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ)
  have hsum := add_le_add (add_le_add ht₀ ht₁) ht₂
  convert hsum using 1 <;>
    dsimp only [radialGeneratorLowerModel, radialGeneratorLowerModelDr,
      radialGeneratorLowerModelDd] <;> ring

end PartialBalayage.Maximal.Square
