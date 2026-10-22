/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: our index box |i|, |j| <= 70 (shifted knots |k| <= 72 instead of 26) and the power |x|^(73/40). -/
module

public import PartialBalayage.Maximal.Square.SplineGeneratorCellPolynomial
public import PartialBalayage.Maximal.Square.CubicIntervalBound

/-!
# Actual finite regrouping of the spline generator potential

Index translation is proved on the genuine finite coefficient box. The spline
support reduces the other coordinate to four local indices. The resulting
potential expansion uses the actual cubic coefficient rows, not a proposed
generator certificate.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

-- Elaborating membership in the index box can reduce `List.range 141`, deeper than the
-- default recursion limit.
set_option maxRecDepth 20000

theorem splineCoefficient_eq_zero_of_left_off_box {i : ℤ} (hi : i ∉ Finset.Icc (-70) 70)
    (j : ℤ) : splineCoefficient i j = 0 := by
  apply splineCoefficient_eq_zero_off_box
  intro h
  exact hi (Finset.mem_product.mp h).1

theorem splineCoefficient_eq_zero_of_right_off_box (i : ℤ) {j : ℤ}
    (hj : j ∉ Finset.Icc (-70) 70) : splineCoefficient i j = 0 := by
  apply splineCoefficient_eq_zero_off_box
  intro h
  exact hj (Finset.mem_product.mp h).2

/-- Translation of a true finitely supported coefficient sequence to the knot box. -/
theorem spline_shifted_coefficient_sum (w F : ℤ → ℝ)
    (hw : ∀ i ∉ Finset.Icc (-70) 70, w i = 0) (q : Fin 5) :
    (∑ i ∈ Finset.Icc (-70) 70, w i * F (i - 2 + (q.val : ℤ))) =
      ∑ k ∈ Finset.Icc (-72) 72, w (k + 2 - (q.val : ℤ)) * F k := by
  have hq : (q.val : ℤ) ≤ 4 := by exact_mod_cast (show q.val ≤ 4 by omega)
  have hq₀ : (0 : ℤ) ≤ q.val := by exact_mod_cast (Nat.zero_le q.val)
  have hs : (∑ i ∈ Finset.Icc (-70) 70, w i * F (i - 2 + (q.val : ℤ))) =
      ∑ k ∈ Finset.Icc (-72 + (q.val : ℤ)) (68 + (q.val : ℤ)),
        w (k + 2 - (q.val : ℤ)) * F k := by
    apply Finset.sum_bij (fun i _ ↦ i - 2 + (q.val : ℤ))
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i hi j hj hij
      omega
    · intro k hk
      refine ⟨k + 2 - (q.val : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        omega
      · ring
    · intro i hi
      congr 1
      congr 1
      ring
  rw [hs]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk hn
    have hi : k + 2 - (q.val : ℤ) ∉ Finset.Icc (-70) 70 := by
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    rw [hw _ hi, zero_mul]

theorem cubicSpline_eq_zero_off_closed_cell {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    {cell j : ℤ} (hj : j ∉ Finset.Icc (cell - 1) (cell + 2)) :
    cubicSpline ((cell : ℝ) + s - j) = 0 := by
  apply cubicSpline_eq_zero_of_two_le_abs
  have hj' : j ≤ cell - 2 ∨ cell + 3 ≤ j := by
    simp only [Finset.mem_Icc] at hj
    omega
  rcases hj' with hj' | hj'
  · have h : (j : ℝ) ≤ (cell : ℝ) - 2 := by exact_mod_cast hj'
    exact (le_abs_self _).trans' (by linarith)
  · have h : (cell : ℝ) + 3 ≤ (j : ℝ) := by exact_mod_cast hj'
    exact (neg_le_abs _).trans' (by linarith)

/-- The genuine spline coefficient function reduces to its four local cell indices. -/
theorem spline_coefficient_sum_eq_local (i cell : ℤ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    (∑ j ∈ Finset.Icc (-70) 70,
      (splineCoefficient i j : ℝ) * cubicSpline ((cell : ℝ) + s - j)) =
        ∑ j ∈ Finset.Icc (cell - 1) (cell + 2),
          (splineCoefficient i j : ℝ) * cubicSpline ((cell : ℝ) + s - j) := by
  let F (j : ℤ) := (splineCoefficient i j : ℝ) * cubicSpline ((cell : ℝ) + s - j)
  have h₁ : (Finset.Icc (-70) 70).sum F =
      (Finset.Icc (-70) 70 ∪ Finset.Icc (cell - 1) (cell + 2)).sum F := by
    apply Finset.sum_subset Finset.subset_union_left
    intro j hj hn
    simp only [splineCoefficient_eq_zero_of_right_off_box i hn, Rat.cast_zero, zero_mul]
  have h₂ : (Finset.Icc (cell - 1) (cell + 2)).sum F =
      (Finset.Icc (-70) 70 ∪ Finset.Icc (cell - 1) (cell + 2)).sum F := by
    apply Finset.sum_subset Finset.subset_union_right
    intro j hj hn
    simp only [cubicSpline_eq_zero_off_closed_cell hs₀ hs₁ hn, mul_zero]
  exact h₁.trans h₂.symm

/-- One genuine orientation of the finite signed generator correction. -/
def splineGeneratorOneCorrection (u v : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc (-70) 70, ∑ j ∈ Finset.Icc (-70) 70,
    (splineCoefficient i j : ℝ) * cubicSpline (v - j) * splineGeneratorPower (u - i)

theorem splineGeneratorCorrectionPower_eq_two_orientations (u v : ℝ) :
    splineGeneratorCorrectionPower u v =
      splineGeneratorOneCorrection u v + splineGeneratorOneCorrection v u := by
  unfold splineGeneratorCorrectionPower splineGeneratorOneCorrection splineCoefficientBox
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [splineCoefficient_swap j i]
    ring

/-- The actual potential orientation is the finite sum of its genuine local cubic rows. -/
theorem splineGeneratorOneCorrection_eq_cell_sum (u : ℝ) (cell : ℤ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    splineGeneratorOneCorrection u ((cell : ℝ) + s) =
      ∑ k ∈ Finset.Icc (-72) 72,
        splineGeneratorCellPolynomial cell k s * |u - (k : ℝ)| ^ (73 / 40 : ℝ) := by
  let W (i : ℤ) := ∑ j ∈ Finset.Icc (-70) 70,
    (splineCoefficient i j : ℝ) * cubicSpline ((cell : ℝ) + s - j)
  have hW : ∀ i ∉ Finset.Icc (-70) 70, W i = 0 := by
    intro i hi
    simp only [W, splineCoefficient_eq_zero_of_left_off_box hi, Rat.cast_zero, zero_mul,
      Finset.sum_const_zero]
  have h₀ : splineGeneratorOneCorrection u ((cell : ℝ) + s) =
      ∑ q : Fin 5, (splineFourthDifferenceCoefficient q : ℝ) *
        ∑ i ∈ Finset.Icc (-70) 70,
          W i * |u - ((i - 2 + (q.val : ℤ) : ℤ) : ℝ)| ^ (73 / 40 : ℝ) := by
    unfold splineGeneratorOneCorrection
    simp only [← Finset.sum_mul]
    change (∑ i ∈ Finset.Icc (-70) 70, W i * splineGeneratorPower (u - i)) = _
    simp_rw [splineGeneratorPower_eq_five_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro i hi
    have he : u - (i : ℝ) + 2 - (q.val : ℝ) =
        u - ((i - 2 + (q.val : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [he]
    ring
  rw [h₀]
  simp_rw [spline_shifted_coefficient_sum W (fun k ↦ |u - (k : ℝ)| ^ (73 / 40 : ℝ)) hW]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have he (q : Fin 5) : W (k + 2 - (q.val : ℤ)) =
      ∑ j ∈ Finset.Icc (cell - 1) (cell + 2),
        (splineCoefficient (k + 2 - (q.val : ℤ)) j : ℝ) *
          cubicSpline ((cell : ℝ) + s - j) :=
    spline_coefficient_sum_eq_local _ _ hs₀ hs₁
  simp_rw [he, ← mul_assoc]
  rw [← Finset.sum_mul, ← splineGeneratorCellPolynomial_eq_sum hs₀ hs₁]

/-- Both genuine orientations use the actual closed-cell cubic rows. -/
theorem splineGeneratorCorrectionPower_eq_cell_sums (i j : ℤ) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    splineGeneratorCorrectionPower ((i : ℝ) + t) ((j : ℝ) + s) =
      (∑ k ∈ Finset.Icc (-72) 72, splineGeneratorCellPolynomial j k s *
        |(i : ℝ) + t - (k : ℝ)| ^ (73 / 40 : ℝ)) +
      ∑ k ∈ Finset.Icc (-72) 72, splineGeneratorCellPolynomial i k t *
        |(j : ℝ) + s - (k : ℝ)| ^ (73 / 40 : ℝ) := by
  rw [splineGeneratorCorrectionPower_eq_two_orientations,
    splineGeneratorOneCorrection_eq_cell_sum _ _ hs₀ hs₁,
    splineGeneratorOneCorrection_eq_cell_sum _ _ ht₀ ht₁]

/-- The exact rational generator-cell cubic coefficients at a new rational center. -/
def centeredSplineGeneratorCellCoefficients (cell k : ℤ) (mid : ℚ) : Fin 4 → ℚ :=
  cubicAffineCoefficients (fun b ↦ splineGeneratorCellCoefficient cell k b) mid 1

/-- The actual generator-cell cubic has the exact centered coefficient expansion. -/
theorem splineGeneratorCellPolynomial_eq_centered (cell k : ℤ) (mid : ℚ) (s : ℝ) :
    splineGeneratorCellPolynomial cell k s =
      centeredCubic (fun b ↦ (centeredSplineGeneratorCellCoefficients cell k mid b : ℝ))
        (s - (mid : ℝ)) := by
  have h := centeredCubic_affine (fun b ↦ splineGeneratorCellCoefficient cell k b)
    mid 1 (s - (mid : ℝ))
  simpa only [Rat.cast_one, one_mul, add_sub_cancel,
    centeredSplineGeneratorCellCoefficients, ← splineGeneratorCellPolynomial_eq_centeredCubic]
    using h

/-- Ordinary rational Bernstein checks bound the actual generator coefficient polynomial. -/
theorem abs_splineGeneratorCellPolynomial_le (cell k : ℤ) {l w M : ℚ} {s : ℝ}
    (hw : 0 < w)
    (hM : ∀ b, |cubicBernsteinCoefficients
      (cubicAffineCoefficients (fun b ↦ splineGeneratorCellCoefficient cell k b) l w) b| ≤ M)
    (hs₀ : (l : ℝ) ≤ s) (hs₁ : s ≤ ((l + w : ℚ) : ℝ)) :
    |splineGeneratorCellPolynomial cell k s| ≤ (M : ℝ) := by
  rw [splineGeneratorCellPolynomial_eq_centeredCubic]
  exact abs_centeredCubic_le_on_interval hw hM hs₀ hs₁

end PartialBalayage.Maximal.Square
