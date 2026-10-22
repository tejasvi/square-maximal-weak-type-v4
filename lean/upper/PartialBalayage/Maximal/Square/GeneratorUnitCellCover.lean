/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: cells i, j < 53 with i + j < 53 for the interior support bound u + v < 264/5. -/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleGeometry
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Genuine unit-cell coverage of the ordered generator region

Taking the actual natural-number floors puts each positive ordered point in a
closed unit cell. The strict support inequality selects one of the 210 cells
whose integer lower corners satisfy the same strict inequality.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The actual unit rectangle at the given nonnegative integer corner. -/
def generatorUnitRectangle (i j : ℕ) : GeneratorRectangle := ⟨i, j, 0, 0, 0⟩

/-- The actual ordered open support region is covered by the finite unit-cell family. -/
theorem exists_generatorUnitRectangle_contains {u v : ℝ}
    (hv : 0 < v) (hvu : v ≤ u) (hr : u + v < 264 / 5) :
    ∃ i j : Fin 53, j.val ≤ i.val ∧ i.val + j.val < 53 ∧
      (generatorUnitRectangle i.val j.val).Contains u v := by
  have hu0 : 0 ≤ u := le_trans hv.le hvu
  have hu28 : u < 53 := by linarith
  have hv28 : v < 53 := hvu.trans_lt hu28
  let i : Fin 53 := ⟨Nat.floor u, (Nat.floor_lt hu0).mpr hu28⟩
  let j : Fin 53 := ⟨Nat.floor v, (Nat.floor_lt hv.le).mpr hv28⟩
  have hij : j.val ≤ i.val := Nat.floor_mono hvu
  have hi : (i.val : ℝ) ≤ u := Nat.floor_le hu0
  have hj : (j.val : ℝ) ≤ v := Nat.floor_le hv.le
  have his : u < (i.val : ℝ) + 1 := Nat.lt_floor_add_one u
  have hjs : v < (j.val : ℝ) + 1 := Nat.lt_floor_add_one v
  have hs : i.val + j.val < 53 := by
    have h : ((i.val + j.val : ℕ) : ℝ) < 53 := by
      push_cast
      linarith [add_le_add hi hj]
    exact_mod_cast h
  refine ⟨i, j, hij, hs, ?_⟩
  simp only [generatorUnitRectangle, GeneratorRectangle.Contains,
    GeneratorRectangle.lowerU, GeneratorRectangle.lowerV, GeneratorRectangle.width,
    pow_zero, div_one, Nat.cast_zero, zero_mul, add_zero, Int.cast_natCast,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
  exact ⟨hi, his.le, hj, hjs.le⟩

end PartialBalayage.Maximal.Square
