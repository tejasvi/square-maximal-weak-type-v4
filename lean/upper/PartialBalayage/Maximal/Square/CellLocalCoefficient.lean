/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CellPolynomial
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Local finite arithmetic for the actual signed spline coefficients

Orbit membership is replaced by its unique ordered absolute-value representative.
The bicubic coefficient on a cell uses only the sixteen tensor indices whose supports
meet that cell. Both reductions are actual equalities, allowing efficient rational checks.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The literal coefficient indexed by an ordered nonnegative representative. -/
def representativeCoefficient (i j : ℕ) : ℚ :=
  (splineOrbits.map (fun t ↦ if t.1 = i ∧ t.2.1 = j then t.2.2 else 0)).sum

theorem mem_splineOrbit_of_natAbs {i j : ℕ} {a b : ℤ}
    (ha : a.natAbs = i) (hb : b.natAbs = j) : (a, b) ∈ splineOrbit i j := by
  have ha' : (i : ℤ) = |a| := by rw [← ha, Int.natCast_natAbs]
  have hb' : (j : ℤ) = |b| := by rw [← hb, Int.natCast_natAbs]
  rcases abs_choice a with h | h <;> rcases abs_choice b with h' | h'
  all_goals rw [h] at ha'; rw [h'] at hb'
  all_goals simp only [splineOrbit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  all_goals omega

/-- Actual orbit membership is exactly the ordered absolute-value index test. -/
theorem mem_splineOrbit_iff_representative {i j : ℕ} (hji : j ≤ i) (a b : ℤ) :
    (a, b) ∈ splineOrbit i j ↔
      i = max a.natAbs b.natAbs ∧ j = min a.natAbs b.natAbs := by
  constructor
  · intro h
    rcases natAbs_of_mem_splineOrbit h with h | h <;>
      rcases h with ⟨ha, hb⟩ <;> simp only [ha, hb]
    · exact ⟨max_eq_left hji |>.symm, min_eq_right hji |>.symm⟩
    · exact ⟨max_eq_right hji |>.symm, min_eq_left hji |>.symm⟩
  · rintro ⟨rfl, rfl⟩
    by_cases h : b.natAbs ≤ a.natAbs
    · simp only [max_eq_left h, min_eq_right h]
      exact mem_splineOrbit_of_natAbs rfl rfl
    · have h' : a.natAbs ≤ b.natAbs := by omega
      simp only [max_eq_right h', min_eq_left h']
      exact (mem_splineOrbit_swap _ _ _ _).mpr (mem_splineOrbit_of_natAbs rfl rfl)

/-- The actual signed tensor coefficient equals its literal ordered lookup. -/
theorem splineCoefficient_eq_representative (a b : ℤ) :
    splineCoefficient a b =
      representativeCoefficient (max a.natAbs b.natAbs) (min a.natAbs b.natAbs) := by
  unfold splineCoefficient representativeCoefficient
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [mem_splineOrbit_iff_representative (splineOrbits_admissible t ht).1]

/-- The sixteen integer tensor indices whose cardinal-spline supports meet a closed cell. -/
def cellTensorIndices (k l : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (k - 1) (k + 2)).product (Finset.Icc (l - 1) (l + 2))

theorem cubicSplineCellCoefficient_eq_zero_of_not_mem {k : ℤ} (a : ℕ)
    (hk : k ∉ Finset.Icc (-2) 1) : cubicSplineCellCoefficient k a = 0 := by
  have hk₂ : k ≠ -2 := by intro h; subst k; norm_num at hk
  have hk₁ : k ≠ -1 := by intro h; subst k; norm_num at hk
  have hk₀ : k ≠ 0 := by intro h; subst k; norm_num at hk
  have hk₁' : k ≠ 1 := by intro h; subst k; norm_num at hk
  simp only [cubicSplineCellCoefficient, hk₂, hk₁, hk₀, hk₁', ↓reduceIte]

theorem tensorCellCoefficient_eq_zero_off_cell (k l : ℤ) (a b : ℕ) (p : ℤ × ℤ)
    (hp : p ∉ cellTensorIndices k l) :
    cubicSplineCellCoefficient (k - p.1) a * cubicSplineCellCoefficient (l - p.2) b = 0 := by
  by_cases hx : p.1 ∈ Finset.Icc (k - 1) (k + 2)
  · have hy : p.2 ∉ Finset.Icc (l - 1) (l + 2) := by
      intro hy
      exact hp (Finset.mem_product.mpr ⟨hx, hy⟩)
    have h : l - p.2 ∉ Finset.Icc (-2) 1 := by
      simp only [Finset.mem_Icc] at hy ⊢
      omega
    rw [cubicSplineCellCoefficient_eq_zero_of_not_mem b h, mul_zero]
  · have h : k - p.1 ∉ Finset.Icc (-2) 1 := by
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    rw [cubicSplineCellCoefficient_eq_zero_of_not_mem a h, zero_mul]

/-- The full actual orbit sum is a sum on its sixteen local tensor indices. -/
theorem orbitCellCoefficient_eq_local (i j : ℕ) (k l : ℤ) (a b : ℕ) :
    orbitCellCoefficient i j k l a b = ∑ p ∈ cellTensorIndices k l,
      if p ∈ splineOrbit i j then
        cubicSplineCellCoefficient (k - p.1) a * cubicSplineCellCoefficient (l - p.2) b
      else 0 := by
  classical
  let F (p : ℤ × ℤ) :=
    cubicSplineCellCoefficient (k - p.1) a * cubicSplineCellCoefficient (l - p.2) b
  let G (p : ℤ × ℤ) := if p ∈ splineOrbit i j then F p else 0
  change (splineOrbit i j).sum F = (cellTensorIndices k l).sum G
  have h₁ : (splineOrbit i j).sum G =
      (splineOrbit i j ∪ cellTensorIndices k l).sum G := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hn
    simp only [hn, ↓reduceIte]
  have h₂ : (cellTensorIndices k l).sum G =
      (splineOrbit i j ∪ cellTensorIndices k l).sum G := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hn
    have hz : F p = 0 := tensorCellCoefficient_eq_zero_off_cell k l a b p hn
    simp only [hz, ite_self]
  rw [← h₂] at h₁
  rw [← h₁]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [G, hp, ↓reduceIte]

/-- Finite literal lists and genuine finite spatial sums commute. -/
theorem weightedList_sum_finset {ι κ : Type*} (L : List ι) (S : Finset κ)
    (F : ι → κ → ℚ) :
    (L.map (fun t ↦ ∑ p ∈ S, F t p)).sum = ∑ p ∈ S, (L.map (fun t ↦ F t p)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, Finset.sum_const_zero]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- Only sixteen actual signed tensor coefficients contribute to a cell coefficient. -/
theorem correctionCellCoefficient_eq_local (k l : ℤ) (a b : ℕ) :
    correctionCellCoefficient k l a b = ∑ p ∈ cellTensorIndices k l,
      splineCoefficient p.1 p.2 *
        (cubicSplineCellCoefficient (k - p.1) a * cubicSplineCellCoefficient (l - p.2) b) := by
  simp only [correctionCellCoefficient, orbitCellCoefficient_eq_local, Finset.mul_sum]
  rw [weightedList_sum_finset]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [splineCoefficient, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro t ht
  split_ifs <;> simp only [mul_zero, zero_mul]

end PartialBalayage.Maximal.Square
