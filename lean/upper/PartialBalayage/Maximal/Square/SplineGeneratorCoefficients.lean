/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: our index box |i|, |j| <= 70 (from i <= 70 for every orbit representative), spline scale 32 and the power |x|^(73/40). -/
module

public import PartialBalayage.Maximal.Square.CellLocalCoefficient
public import PartialBalayage.Maximal.Square.SplineGenerator

/-!
# Actual signed tensor coefficients for the spline generator

The genuine finite orbit sum is identified with its exact integer coefficient
lookup. The fourfold finite difference then gives the exact rational cubic
coefficient sequence used on each generator grid cell.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- A common finite integer box containing every actual signed tensor index. -/
def splineCoefficientBox : Finset (ℤ × ℤ) :=
  (Finset.Icc (-70) 70).product (Finset.Icc (-70) 70)

theorem splineOrbit_subset_coefficientBox {i j : ℕ} (hij : j ≤ i ∧ i ≤ 70) :
    splineOrbit i j ⊆ splineCoefficientBox := by
  intro p hp
  have hi : i ≤ 70 := hij.2
  have hj : j ≤ 70 := hij.1.trans hij.2
  have hab := natAbs_of_mem_splineOrbit hp
  have hp₀ : p.1.natAbs ≤ 70 := by rcases hab with h | h <;> omega
  have hp₁ : p.2.natAbs ≤ 70 := by rcases hab with h | h <;> omega
  have hp₀' : |p.1| ≤ (70 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hp₀
  have hp₁' : |p.2| ≤ (70 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hp₁
  rw [splineCoefficientBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc]
  exact ⟨_root_.abs_le.mp hp₀', _root_.abs_le.mp hp₁'⟩

-- Elaborating membership in the box can reduce `List.range 141`, deeper than the default limit.
set_option maxRecDepth 20000 in
/-- The actual signed coefficient is zero outside the common finite index box. -/
theorem splineCoefficient_eq_zero_off_box {i j : ℤ}
    (hij : (i, j) ∉ splineCoefficientBox) : splineCoefficient i j = 0 := by
  unfold splineCoefficient
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  have hn : (i, j) ∉ splineOrbit t.1 t.2.1 := by
    intro h
    exact hij (splineOrbit_subset_coefficientBox (splineOrbits_admissible t ht) h)
  simp only [hn, ↓reduceIte]

private theorem weighted_real_list_sum_finset {ι κ : Type*} (L : List ι) (S : Finset κ)
    (F : ι → κ → ℝ) :
    (L.map (fun t ↦ ∑ p ∈ S, F t p)).sum = ∑ p ∈ S, (L.map (fun t ↦ F t p)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, Finset.sum_const_zero]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

set_option maxRecDepth 20000 in
/-- Every genuine weighted orbit sum uses the actual transparent signed lookup. -/
theorem weighted_orbit_sum_eq_coefficientBox (F : ℤ × ℤ → ℝ) :
    (splineOrbits.map (fun t ↦ (t.2.2 : ℝ) *
      ∑ p ∈ splineOrbit t.1 t.2.1, F p)).sum =
        ∑ p ∈ splineCoefficientBox, (splineCoefficient p.1 p.2 : ℝ) * F p := by
  have ho (t : ℕ × ℕ × ℚ) (ht : t ∈ splineOrbits) :
      (∑ p ∈ splineOrbit t.1 t.2.1, F p) =
        ∑ p ∈ splineCoefficientBox, if p ∈ splineOrbit t.1 t.2.1 then F p else 0 := by
    rw [← Finset.sum_subset (splineOrbit_subset_coefficientBox
      (splineOrbits_admissible t ht)) (by
        intro p hp hn
        simp only [hn, ↓reduceIte])]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hp, ite_eq_left]
  have hL : (splineOrbits.map (fun t ↦ (t.2.2 : ℝ) *
      ∑ p ∈ splineOrbit t.1 t.2.1, F p)).sum =
        (splineOrbits.map (fun t ↦ ∑ p ∈ splineCoefficientBox,
          (t.2.2 : ℝ) * (if p ∈ splineOrbit t.1 t.2.1 then F p else 0))).sum := by
    congr 1
    apply List.map_congr_left
    intro t ht
    rw [ho t ht, Finset.mul_sum]
  rw [hL, weighted_real_list_sum_finset]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [splineCoefficient, Rat.cast_list_sum, ← List.sum_map_mul_right, List.map_map,
    Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro t ht
  split_ifs <;> simp only [Rat.cast_zero, mul_zero, zero_mul]

/-- The actual full frozen spline correction has the genuine signed tensor expansion. -/
theorem splineCorrection_eq_coefficientBox (u v : ℝ) :
    splineCorrection u v = ∑ p ∈ splineCoefficientBox, (splineCoefficient p.1 p.2 : ℝ) *
      (cubicSpline (32 * u - p.1) * cubicSpline (32 * v - p.2)) := by
  exact weighted_orbit_sum_eq_coefficientBox _

/-- Exact coefficients of the fourth finite difference of the cubic spline. -/
def splineFourthDifferenceCoefficient : Fin 5 → ℚ := ![1, -4, 6, -4, 1]

theorem splineGeneratorPower_eq_five_sum (x : ℝ) :
    splineGeneratorPower x = ∑ q : Fin 5, (splineFourthDifferenceCoefficient q : ℝ) *
      |x + 2 - (q.val : ℝ)| ^ (73 / 40 : ℝ) := by
  norm_num [splineGeneratorPower, splineFourthDifferenceCoefficient, Fin.sum_univ_succ]
  ring_nf

/-- The actual generator correction before its positive normalization and scale factors. -/
def splineGeneratorCorrectionPower (u v : ℝ) : ℝ :=
  ∑ p ∈ splineCoefficientBox, (splineCoefficient p.1 p.2 : ℝ) *
    (cubicSpline (v - p.2) * splineGeneratorPower (u - p.1) +
      cubicSpline (u - p.1) * splineGeneratorPower (v - p.2))

/-- The exact rational cubic coefficients of one genuine generator grid cell. -/
def splineGeneratorCellCoefficient (cell k : ℤ) (b : ℕ) : ℚ :=
  ∑ q : Fin 5, splineFourthDifferenceCoefficient q *
    ∑ j ∈ Finset.Icc (cell - 1) (cell + 2),
      splineCoefficient (k + 2 - (q.val : ℤ)) j * cubicSplineCellCoefficient (cell - j) b

end PartialBalayage.Maximal.Square
