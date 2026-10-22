/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CellLocalCoefficient

/-!
# Transparent sixteen-term cell coefficient arithmetic

The genuine integer support interval is rewritten as a range of length four. The
resulting expression contains only literal representative lookups and rational arithmetic.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The actual bicubic coefficient as a transparent sixteen-term rational expression. -/
def localCellCoefficient (k l : ℤ) (a b : ℕ) : ℚ :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
    representativeCoefficient (max (k - 1 + i).natAbs (l - 1 + j).natAbs)
      (min (k - 1 + i).natAbs (l - 1 + j).natAbs) *
        (cubicSplineCellCoefficient (1 - i) a * cubicSplineCellCoefficient (1 - j) b)

/-- This transparent finite expression is the actual signed cell coefficient. -/
theorem correctionCellCoefficient_eq_local_range (k l : ℤ) (a b : ℕ) :
    correctionCellCoefficient k l a b = localCellCoefficient k l a b := by
  rw [correctionCellCoefficient_eq_local]
  simp_rw [splineCoefficient_eq_representative]
  have hk : k + 2 + 1 - (k - 1) = 4 := by ring
  have hl : l + 2 + 1 - (l - 1) = 4 := by ring
  unfold cellTensorIndices
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp only [Int.Icc_eq_finset_map, hk, hl,
    Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  unfold localCellCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2 <;> congr 1 <;> ring

theorem cubicSplineCellCoefficient_eq_zero_of_four_le (k : ℤ) {a : ℕ} (ha : 4 ≤ a) :
    cubicSplineCellCoefficient k a = 0 := by
  have h₀ : a ≠ 0 := by omega
  have h₁ : a ≠ 1 := by omega
  have h₂ : a ≠ 2 := by omega
  have h₃ : a ≠ 3 := by omega
  simp only [cubicSplineCellCoefficient, h₀, h₁, h₂, h₃, ↓reduceIte, ite_self]

theorem correctionCellCoefficient_eq_zero_of_four_le_left (k l : ℤ) {a : ℕ}
    (ha : 4 ≤ a) (b : ℕ) : correctionCellCoefficient k l a b = 0 := by
  simp only [correctionCellCoefficient, orbitCellCoefficient,
    cubicSplineCellCoefficient_eq_zero_of_four_le _ ha, zero_mul,
    Finset.sum_const_zero, mul_zero, List.map_const', List.sum_replicate, nsmul_zero]

theorem correctionCellCoefficient_eq_zero_of_four_le_right (k l : ℤ) (a : ℕ) {b : ℕ}
    (hb : 4 ≤ b) : correctionCellCoefficient k l a b = 0 := by
  simp only [correctionCellCoefficient, orbitCellCoefficient,
    cubicSplineCellCoefficient_eq_zero_of_four_le _ hb, mul_zero,
    Finset.sum_const_zero, List.map_const', List.sum_replicate, nsmul_zero]

end PartialBalayage.Maximal.Square
