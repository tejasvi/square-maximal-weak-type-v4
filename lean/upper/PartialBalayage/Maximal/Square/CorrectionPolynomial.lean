/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32 instead of 1/16. -/
module

public import PartialBalayage.Maximal.Square.CellPolynomial

/-!
# Genuine signed correction polynomials on grid cells

Finite orbit summation and signed rational weights preserve the closed-cell polynomial
identity. These are ordinary real equalities for the actual frozen kernel correction.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

theorem bicubicPolynomial_zero (t s : ℝ) :
    bicubicPolynomial (fun _ _ ↦ 0) t s = 0 := by
  simp only [bicubicPolynomial, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

theorem bicubicPolynomial_add (c d : ℕ → ℕ → ℚ) (t s : ℝ) :
    bicubicPolynomial (fun a b ↦ c a b + d a b) t s =
      bicubicPolynomial c t s + bicubicPolynomial d t s := by
  simp only [bicubicPolynomial, Rat.cast_add, add_mul, Finset.sum_add_distrib]

theorem bicubicPolynomial_smul (a : ℚ) (c : ℕ → ℕ → ℚ) (t s : ℝ) :
    bicubicPolynomial (fun i j ↦ a * c i j) t s = (a : ℝ) * bicubicPolynomial c t s := by
  simp only [bicubicPolynomial, Rat.cast_mul, Finset.mul_sum, mul_assoc]

/-- The real evaluation of an actual finite weighted sum is the weighted evaluation sum. -/
theorem bicubicPolynomial_weightedList {ι : Type*} (L : List ι) (a : ι → ℚ)
    (c : ι → ℕ → ℕ → ℚ) (t s : ℝ) :
    bicubicPolynomial (fun i j ↦ (L.map (fun z ↦ a z * c z i j)).sum) t s =
      (L.map (fun z ↦ (a z : ℝ) * bicubicPolynomial (c z) t s)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, bicubicPolynomial_zero]
  | cons z zs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [bicubicPolynomial_add, bicubicPolynomial_smul, ih]

/-- The exact signed correction agrees with its rational bicubic polynomial on every cell. -/
theorem splineCorrection_eq_cellPolynomial (k l : ℤ) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    splineCorrection (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) =
      bicubicPolynomial (correctionCellCoefficient k l) t s := by
  unfold splineCorrection correctionCellCoefficient
  simp_rw [orbitSpline_eq_cellPolynomial _ _ k l ht₀ ht₁ hs₀ hs₁]
  exact (bicubicPolynomial_weightedList splineOrbits (fun z ↦ z.2.2)
    (fun z ↦ orbitCellCoefficient z.1 z.2.1 k l) t s).symm

end PartialBalayage.Maximal.Square
