/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TriangleGeometry
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Actual quarter-diamond grid coverage

The two initial triangles cover every closed unit cell. The radius-seven-fourths
quarter diamond is represented in cells with index sum at most twenty-seven, including
the outer edge; no boundary points are removed from the geometric certificate.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The lower closed triangle of a unit cell. -/
def lowerCellTriangle : RationalTriangle := ⟨(0, 0), (1, 0), (0, 1)⟩

/-- The upper closed triangle of a unit cell, in the certificate's order. -/
def upperCellTriangle : RationalTriangle := ⟨(1, 1), (0, 1), (1, 0)⟩

theorem lowerCellTriangle_contains {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ 1) :
    lowerCellTriangle.Contains (t, s) := by
  refine ⟨t, s, ht, hs, hts, ?_⟩
  simp only [RationalTriangle.point, lowerCellTriangle, Rat.cast_zero, Rat.cast_one,
    sub_zero, sub_self, one_mul, zero_mul, add_zero, zero_add]

theorem upperCellTriangle_contains {t s : ℝ}
    (ht : t ≤ 1) (hs : s ≤ 1) (hts : 1 ≤ t + s) :
    upperCellTriangle.Contains (t, s) := by
  refine ⟨1 - t, 1 - s, by linarith, by linarith, by linarith, ?_⟩
  ext <;> simp only [RationalTriangle.point, upperCellTriangle, Rat.cast_zero,
    Rat.cast_one] <;> ring

/-- The initial pair of closed triangles covers the entire closed unit box. -/
theorem cellTriangle_coverage {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    lowerCellTriangle.Contains (t, s) ∨ upperCellTriangle.Contains (t, s) := by
  by_cases h : t + s ≤ 1
  · exact Or.inl (lowerCellTriangle_contains ht₀ hs₀ h)
  · exact Or.inr (upperCellTriangle_contains ht₁ hs₁ (by linarith))

/-- Every point of the closed quarter diamond belongs to an actual retained grid cell. -/
theorem exists_closed_quarter_grid {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : u + v ≤ 7 / 4) :
    ∃ k l : ℕ, k + l ≤ 27 ∧ ∃ t s : ℝ,
      0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 ∧
        u = ((k : ℝ) + t) / 16 ∧ v = ((l : ℝ) + s) / 16 := by
  let k := Nat.floor (16 * u)
  let l := Nat.floor (16 * v)
  have hk : (k : ℝ) ≤ 16 * u := Nat.floor_le (by positivity)
  have hl : (l : ℝ) ≤ 16 * v := Nat.floor_le (by positivity)
  have hk' : 16 * u < (k : ℝ) + 1 := Nat.lt_floor_add_one (16 * u)
  have hl' : 16 * v < (l : ℝ) + 1 := Nat.lt_floor_add_one (16 * v)
  by_cases hkl : k + l ≤ 27
  · refine ⟨k, l, hkl, 16 * u - k, 16 * v - l, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals linarith
  have hkl' : k + l = 28 := by
    have hsum : ((k + l : ℕ) : ℝ) ≤ 28 := by push_cast; linarith
    have hsum' : k + l ≤ 28 := by exact_mod_cast hsum
    omega
  have hku : (k : ℝ) = 16 * u := by
    have hsum : (k : ℝ) + (l : ℝ) = 28 := by exact_mod_cast hkl'
    linarith
  have hlv : (l : ℝ) = 16 * v := by
    have hsum : (k : ℝ) + (l : ℝ) = 28 := by exact_mod_cast hkl'
    linarith
  by_cases hk₀ : k = 0
  · have hl₂₈ : l = 28 := by omega
    refine ⟨0, 27, by omega, 0, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_, ?_⟩
    · simp only [hk₀, Nat.cast_zero] at hku
      norm_num
      linarith
    · simp only [hl₂₈, Nat.cast_ofNat] at hlv
      norm_num
      linarith
  · have hk₁ : 1 ≤ k := by omega
    refine ⟨k - 1, l, by omega, 1, 0, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_, ?_⟩
    · rw [Nat.cast_sub hk₁]
      norm_num only [Nat.cast_one]
      linarith
    · norm_num only [add_zero]
      linarith

end PartialBalayage.Maximal.Square
