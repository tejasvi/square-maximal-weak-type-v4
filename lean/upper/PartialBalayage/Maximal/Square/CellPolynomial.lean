/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32 instead of 1/16. -/
module

public import PartialBalayage.Maximal.Square.Kernel

/-!
# The actual spline polynomials on closed grid cells

The four rational coefficient rows in the certificate are identified with the actual
cardinal spline for every point of a closed unit cell. The signed correction is therefore
an actual bicubic polynomial on every closed grid cell, including its boundary points.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The exact rational polynomial coefficient for one translated spline on a unit cell. -/
def cubicSplineCellCoefficient (k : ℤ) (i : ℕ) : ℚ :=
  if k = -2 then if i = 3 then 1 / 6 else 0
  else if k = -1 then
    if i = 0 then 1 / 6 else if i = 1 then 1 / 2 else
      if i = 2 then 1 / 2 else if i = 3 then -(1 / 2) else 0
  else if k = 0 then
    if i = 0 then 2 / 3 else if i = 2 then -1 else if i = 3 then 1 / 2 else 0
  else if k = 1 then
    if i = 0 then 1 / 6 else if i = 1 then -(1 / 2) else
      if i = 2 then 1 / 2 else if i = 3 then -(1 / 6) else 0
  else 0

/-- The exact cell polynomial, evaluated as a genuine real polynomial. -/
def cubicSplineCellPolynomial (k : ℤ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 4, (cubicSplineCellCoefficient k i : ℝ) * t ^ i

/-- The four rational coefficient rows really describe the actual closed-cell spline. -/
theorem cubicSpline_eq_cellPolynomial (k : ℤ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    cubicSpline (t + k) = cubicSplineCellPolynomial k t := by
  by_cases h₂ : k = -2
  · subst k
    rw [cubicSpline_eq_positivePart_formula]
    have h₀ : t + (-2 : ℤ) + 2 = t := by norm_num
    have h₁ : t + (-2 : ℤ) + 1 ≤ 0 := by norm_num; linarith
    have h₂ : t + (-2 : ℤ) ≤ 0 := by norm_num; linarith
    have h₃ : t + (-2 : ℤ) - 1 ≤ 0 := by norm_num; linarith
    have h₄ : t + (-2 : ℤ) - 2 ≤ 0 := by norm_num; linarith
    rw [h₀, max_eq_left ht₀, max_eq_right h₁, max_eq_right h₂,
      max_eq_right h₃, max_eq_right h₄]
    norm_num [cubicSplineCellPolynomial, cubicSplineCellCoefficient, Finset.sum_range_succ]
    ring
  by_cases h₁ : k = -1
  · subst k
    rw [cubicSpline_eq_positivePart_formula]
    have h₀ : 0 ≤ t + (-1 : ℤ) + 2 := by norm_num; linarith
    have h₁ : 0 ≤ t + (-1 : ℤ) + 1 := by norm_num; linarith
    have h₂ : t + (-1 : ℤ) ≤ 0 := by norm_num; linarith
    have h₃ : t + (-1 : ℤ) - 1 ≤ 0 := by norm_num; linarith
    have h₄ : t + (-1 : ℤ) - 2 ≤ 0 := by norm_num; linarith
    rw [max_eq_left h₀, max_eq_left h₁, max_eq_right h₂,
      max_eq_right h₃, max_eq_right h₄]
    norm_num [cubicSplineCellPolynomial, cubicSplineCellCoefficient, Finset.sum_range_succ]
    ring
  by_cases h₀ : k = 0
  · subst k
    rw [cubicSpline_eq_positivePart_formula]
    have h₀ : 0 ≤ t + (0 : ℤ) + 2 := by norm_num; linarith
    have h₁ : 0 ≤ t + (0 : ℤ) + 1 := by norm_num; linarith
    have h₂ : 0 ≤ t + (0 : ℤ) := by simpa using ht₀
    have h₃ : t + (0 : ℤ) - 1 ≤ 0 := by norm_num; linarith
    have h₄ : t + (0 : ℤ) - 2 ≤ 0 := by norm_num; linarith
    rw [max_eq_left h₀, max_eq_left h₁, max_eq_left h₂,
      max_eq_right h₃, max_eq_right h₄]
    norm_num [cubicSplineCellPolynomial, cubicSplineCellCoefficient, Finset.sum_range_succ]
    ring
  by_cases h₁' : k = 1
  · subst k
    rw [cubicSpline_eq_positivePart_formula]
    have h₀ : 0 ≤ t + (1 : ℤ) + 2 := by norm_num; linarith
    have h₁ : 0 ≤ t + (1 : ℤ) + 1 := by norm_num; linarith
    have h₂ : 0 ≤ t + (1 : ℤ) := by norm_num; linarith
    have h₃ : 0 ≤ t + (1 : ℤ) - 1 := by norm_num; linarith
    have h₄ : t + (1 : ℤ) - 2 ≤ 0 := by norm_num; linarith
    rw [max_eq_left h₀, max_eq_left h₁, max_eq_left h₂,
      max_eq_left h₃, max_eq_right h₄]
    norm_num [cubicSplineCellPolynomial, cubicSplineCellCoefficient, Finset.sum_range_succ]
    ring
  have hk : k ≤ -3 ∨ 2 ≤ k := by omega
  have ht : 2 ≤ |t + (k : ℝ)| := by
    rcases hk with hk | hk
    · have hk' : (k : ℝ) ≤ -3 := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith : t + (k : ℝ) ≤ 0)]
      linarith
    · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      exact (le_abs_self (t + (k : ℝ))).trans' (by linarith)
  rw [cubicSpline_eq_zero_of_two_le_abs ht]
  simp only [cubicSplineCellPolynomial, cubicSplineCellCoefficient,
    h₂, h₁, h₀, h₁', ↓reduceIte, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

/-- The exact rational bicubic coefficient of one actual orbit on a grid cell. -/
def orbitCellCoefficient (i j : ℕ) (k l : ℤ) (a b : ℕ) : ℚ :=
  ∑ p ∈ splineOrbit i j,
    cubicSplineCellCoefficient (k - p.1) a * cubicSplineCellCoefficient (l - p.2) b

/-- The actual signed correction's rational bicubic coefficient on one grid cell. -/
def correctionCellCoefficient (k l : ℤ) (a b : ℕ) : ℚ :=
  (splineOrbits.map (fun t ↦ t.2.2 * orbitCellCoefficient t.1 t.2.1 k l a b)).sum

/-- Evaluation of an ordinary rational bicubic polynomial. -/
def bicubicPolynomial (c : ℕ → ℕ → ℚ) (t s : ℝ) : ℝ :=
  ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4, (c a b : ℝ) * (t ^ a * s ^ b)

/-- The actual tensor product has the exact rational closed-cell polynomial. -/
theorem tensorSpline_eq_bicubic {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (k l : ℤ) :
    cubicSpline (t + k) * cubicSpline (s + l) =
      bicubicPolynomial (fun a b ↦
        cubicSplineCellCoefficient k a * cubicSplineCellCoefficient l b) t s := by
  rw [cubicSpline_eq_cellPolynomial k ht₀ ht₁,
    cubicSpline_eq_cellPolynomial l hs₀ hs₁]
  unfold cubicSplineCellPolynomial bicubicPolynomial
  simp only [Finset.sum_mul, Finset.mul_sum, Rat.cast_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Every actual orbit agrees with its computed bicubic polynomial throughout a closed cell. -/
theorem orbitSpline_eq_cellPolynomial (i j : ℕ) (k l : ℤ) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    orbitSpline i j (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) =
      bicubicPolynomial (orbitCellCoefficient i j k l) t s := by
  have harg (p : ℤ) : 32 * (((k : ℝ) + t) / 32) - p = t + ((k - p : ℤ) : ℝ) := by
    push_cast
    ring
  have harg' (p : ℤ) : 32 * (((l : ℝ) + s) / 32) - p = s + ((l - p : ℤ) : ℝ) := by
    push_cast
    ring
  unfold orbitSpline
  simp_rw [harg, harg', tensorSpline_eq_bicubic ht₀ ht₁ hs₀ hs₁]
  unfold bicubicPolynomial orbitCellCoefficient
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  all_goals
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]

end PartialBalayage.Maximal.Square
