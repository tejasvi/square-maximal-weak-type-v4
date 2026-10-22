/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 72 cells and 145 signed knots (offset 72) for our kernel. -/
module

public import PartialBalayage.Maximal.Square.GeneratorCellCoefficients
public import PartialBalayage.Maximal.Square.CubicIntervalBound

/-!
# Genuine closed-interval cubic data for the spline generator

The validity checks compare proposed centered rows with the proved actual
coefficient table and bound their true Bernstein coefficients. They therefore
give both the actual centered polynomial and its bound throughout the closed
interval, including every dyadic endpoint.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Proposed finite centered rows and bounds for one genuine generator cell interval. -/
structure GeneratorCubicIntervalData where
  cell : Fin 72
  lower : ℚ
  width : ℚ
  centered : Fin 145 → Fin 4 → ℚ
  bound : Fin 145 → ℚ

namespace GeneratorCubicIntervalData

/-- Exact rational midpoint of the closed interval. -/
def midpoint (D : GeneratorCubicIntervalData) : ℚ := D.lower + D.width / 2

/-- Exact coefficient equalities and Bernstein bounds for the genuine cell cubics. -/
def IsValid (D : GeneratorCubicIntervalData) : Prop :=
  0 < D.width ∧
    (∀ k b, D.centered k b =
      cubicAffineCoefficients (generatorCellCoefficients D.cell k) D.midpoint 1 b) ∧
    ∀ k b, |cubicBernsteinCoefficients
      (cubicAffineCoefficients (generatorCellCoefficients D.cell k) D.lower D.width) b| ≤
        D.bound k

instance (D : GeneratorCubicIntervalData) : Decidable D.IsValid := by
  unfold IsValid
  infer_instance

/-- The checked centered row is the actual polynomial at every real argument. -/
theorem polynomial_eq {D : GeneratorCubicIntervalData} (hD : D.IsValid) (k : Fin 145)
    (s : ℝ) :
    splineGeneratorCellPolynomial (D.cell.val : ℤ) ((k.val : ℤ) - 72) s =
      centeredCubic (fun b ↦ (D.centered k b : ℝ)) (s - (D.midpoint : ℝ)) := by
  rw [splineGeneratorCellPolynomial_eq_generatorCellCoefficients]
  have he : cubicAffineCoefficients (generatorCellCoefficients D.cell k) D.midpoint 1 =
      D.centered k := by
    funext b
    exact (hD.2.1 k b).symm
  have h := centeredCubic_affine (generatorCellCoefficients D.cell k) D.midpoint 1
    (s - (D.midpoint : ℝ))
  rw [he] at h
  simpa only [Rat.cast_one, one_mul, add_sub_cancel] using h

/-- The checked Bernstein bound applies to every point of the actual closed interval. -/
theorem abs_polynomial_le {D : GeneratorCubicIntervalData} (hD : D.IsValid) (k : Fin 145)
    {s : ℝ} (hs₀ : (D.lower : ℝ) ≤ s) (hs₁ : s ≤ ((D.lower + D.width : ℚ) : ℝ)) :
    |splineGeneratorCellPolynomial (D.cell.val : ℤ) ((k.val : ℤ) - 72) s| ≤
      (D.bound k : ℝ) := by
  rw [splineGeneratorCellPolynomial_eq_generatorCellCoefficients]
  exact abs_centeredCubic_le_on_interval hD.1 (hD.2.2 k) hs₀ hs₁

/-- Every checked coefficient-polynomial bound is nonnegative. -/
theorem bound_nonneg {D : GeneratorCubicIntervalData} (hD : D.IsValid) (k : Fin 145) :
    0 ≤ D.bound k :=
  (abs_nonneg _).trans (hD.2.2 k 0)

end GeneratorCubicIntervalData

end PartialBalayage.Maximal.Square
