/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCoefficientRange
public import PartialBalayage.Maximal.Square.SplineTaylorSum

/-!
# Genuine generator-cell cubic polynomials

Each exact cubic coefficient row evaluates to the actual fourth difference of
the signed spline coefficient functions throughout the closed grid cell.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual real cubic specified by a genuine generator-cell coefficient row. -/
def splineGeneratorCellPolynomial (cell k : ℤ) (s : ℝ) : ℝ :=
  ∑ b ∈ Finset.range 4, (splineGeneratorCellCoefficient cell k b : ℝ) * s ^ b

theorem cubicSpline_cell_shift {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (cell j : ℤ) :
    cubicSpline ((cell : ℝ) + s - j) = cubicSplineCellPolynomial (cell - j) s := by
  have he : (cell : ℝ) + s - j = s + ((cell - j : ℤ) : ℝ) := by push_cast; ring
  rw [he, cubicSpline_eq_cellPolynomial (cell - j) hs₀ hs₁]

/-- The exact rational row is the genuine spline finite difference on the whole closed cell. -/
theorem splineGeneratorCellPolynomial_eq_sum {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (cell k : ℤ) :
    splineGeneratorCellPolynomial cell k s =
      ∑ q : Fin 5, (splineFourthDifferenceCoefficient q : ℝ) *
        ∑ j ∈ Finset.Icc (cell - 1) (cell + 2),
          (splineCoefficient (k + 2 - (q.val : ℤ)) j : ℝ) *
            cubicSpline ((cell : ℝ) + s - j) := by
  simp_rw [cubicSpline_cell_shift hs₀ hs₁]
  simp only [splineGeneratorCellPolynomial, splineGeneratorCellCoefficient,
    cubicSplineCellPolynomial, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The finite coefficient row has the same genuine evaluation in `Fin 4` coordinates. -/
theorem splineGeneratorCellPolynomial_eq_centeredCubic (cell k : ℤ) (s : ℝ) :
    splineGeneratorCellPolynomial cell k s =
      centeredCubic (fun b : Fin 4 ↦ (splineGeneratorCellCoefficient cell k b : ℝ)) s := by
  norm_num [splineGeneratorCellPolynomial, centeredCubic, Fin.sum_univ_succ,
    Finset.sum_range_succ]
  ring

end PartialBalayage.Maximal.Square
