/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.RectanglePolynomialBound

/-!
# Actual closed dyadic rectangles for the generator partition

The five literal indices determine exact rational endpoints, midpoints, and
half-widths. Genuine membership in the closed rectangle supplies the displacement
bounds used by the real polynomial and Taylor estimates.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Literal integer cell and dyadic subrectangle indices. -/
structure GeneratorRectangle where
  cellU : ℤ
  cellV : ℤ
  depth : ℕ
  indexU : ℕ
  indexV : ℕ
  deriving DecidableEq

namespace GeneratorRectangle

/-- Exact rational dyadic width. -/
def width (T : GeneratorRectangle) : ℚ := 1 / (2 : ℚ) ^ T.depth

/-- Exact rational half-width. -/
def radius (T : GeneratorRectangle) : ℚ := T.width / 2

/-- Exact rational first-coordinate lower endpoint. -/
def lowerU (T : GeneratorRectangle) : ℚ := T.cellU + T.indexU * T.width

/-- Exact rational second-coordinate lower endpoint. -/
def lowerV (T : GeneratorRectangle) : ℚ := T.cellV + T.indexV * T.width

/-- Exact first-coordinate midpoint. -/
def centerU (T : GeneratorRectangle) : ℚ := T.lowerU + T.radius

/-- Exact second-coordinate midpoint. -/
def centerV (T : GeneratorRectangle) : ℚ := T.lowerV + T.radius

/-- Membership in the actual closed rectangle specified by its literal data. -/
def Contains (T : GeneratorRectangle) (u v : ℝ) : Prop :=
  (T.lowerU : ℝ) ≤ u ∧ u ≤ ((T.lowerU + T.width : ℚ) : ℝ) ∧
    (T.lowerV : ℝ) ≤ v ∧ v ≤ ((T.lowerV + T.width : ℚ) : ℝ)

theorem width_pos (T : GeneratorRectangle) : 0 < T.width := by unfold width; positivity

theorem radius_pos (T : GeneratorRectangle) : 0 < T.radius :=
  div_pos T.width_pos (by norm_num)

/-- Actual closed-rectangle membership gives both true midpoint displacement bounds. -/
theorem Contains.displacement_le {T : GeneratorRectangle} {u v : ℝ}
    (h : T.Contains u v) :
    |u - (T.centerU : ℝ)| ≤ (T.radius : ℝ) ∧
      |v - (T.centerV : ℝ)| ≤ (T.radius : ℝ) := by
  have hu₀ := h.1
  have hu₁ := h.2.1
  have hv₀ := h.2.2.1
  have hv₁ := h.2.2.2
  simp only [centerU, centerV, radius, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at *
  constructor <;> apply _root_.abs_le.mpr <;> constructor <;> linarith

/-- The rectangle's lower-corner sum is a genuine lower bound for every contained radius. -/
theorem Contains.lower_sum_le {T : GeneratorRectangle} {u v : ℝ} (h : T.Contains u v) :
    ((T.lowerU + T.lowerV : ℚ) : ℝ) ≤ u + v := by
  rw [Rat.cast_add]
  exact add_le_add h.1 h.2.2.1

end GeneratorRectangle

end PartialBalayage.Maximal.Square
