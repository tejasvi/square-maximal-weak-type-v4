/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorShapes
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Positivity

/-!
# Dyadic interval shapes inside a unit cell

Every leaf coordinate interval is a dyadic interval `[j / 2^d, (j + 1) / 2^d]` of a unit
cell, recorded once in the shape table and shared by all cells.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The depth of a recorded shape. -/
def shapeDepth (s : Fin generatorShapeCount) : ℕ := (generatorShapes s).1

/-- The index of a recorded shape. -/
def shapeIndex (s : Fin generatorShapeCount) : ℕ := (generatorShapes s).2

/-- Exact width `1 / 2^d`. -/
def shapeWidth (s : Fin generatorShapeCount) : ℚ := 1 / 2 ^ shapeDepth s

/-- Exact lower endpoint `j / 2^d`. -/
def shapeLower (s : Fin generatorShapeCount) : ℚ := shapeIndex s / 2 ^ shapeDepth s

/-- Exact midpoint. -/
def shapeMid (s : Fin generatorShapeCount) : ℚ := shapeLower s + shapeWidth s / 2

theorem shapeWidth_pos (s : Fin generatorShapeCount) : 0 < shapeWidth s := by
  unfold shapeWidth; positivity

theorem shapeLower_nonneg (s : Fin generatorShapeCount) : 0 ≤ shapeLower s := by
  unfold shapeLower; positivity

theorem shapeLower_add_width_le (s : Fin generatorShapeCount) : shapeLower s + shapeWidth s ≤ 1 := by
  have h := generatorShapes_index_lt s
  unfold shapeLower shapeWidth
  rw [← add_div, div_le_one (by positivity)]
  have h' : ((shapeIndex s : ℕ) : ℚ) + 1 ≤ ((2 ^ shapeDepth s : ℕ) : ℚ) := by
    exact_mod_cast h
  simpa [shapeIndex, shapeDepth] using h'

end PartialBalayage.Maximal.Square
