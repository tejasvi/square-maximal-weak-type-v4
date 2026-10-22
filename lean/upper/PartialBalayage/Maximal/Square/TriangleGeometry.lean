/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Tactic

/-!
# Genuine coverage by the four midpoint triangles

The certificate's recursive geometric subdivision is justified for every point of a
closed triangle, including boundaries and degenerate cases. All vertices are rational,
but membership and the coverage theorem concern actual real points.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- One actual rational triangle, with its ordered vertices. -/
structure RationalTriangle where
  v₀ : ℚ × ℚ
  v₁ : ℚ × ℚ
  v₂ : ℚ × ℚ
  deriving DecidableEq

/-- The actual affine map from the closed unit triangle to a rational triangle. -/
def RationalTriangle.point (T : RationalTriangle) (x y : ℝ) : ℝ × ℝ :=
  ((T.v₀.1 : ℝ) + ((T.v₁.1 : ℝ) - T.v₀.1) * x +
      ((T.v₂.1 : ℝ) - T.v₀.1) * y,
    (T.v₀.2 : ℝ) + ((T.v₁.2 : ℝ) - T.v₀.2) * x +
      ((T.v₂.2 : ℝ) - T.v₀.2) * y)

/-- Actual point membership in the affine closed triangle. -/
def RationalTriangle.Contains (T : RationalTriangle) (p : ℝ × ℝ) : Prop :=
  ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 ∧ T.point x y = p

/-- The exact rational midpoint of two vertices. -/
def rationalMidpoint (p q : ℚ × ℚ) : ℚ × ℚ := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- The child triangle adjacent to the first original vertex. -/
def RationalTriangle.child₀ (T : RationalTriangle) : RationalTriangle :=
  ⟨T.v₀, rationalMidpoint T.v₀ T.v₁, rationalMidpoint T.v₂ T.v₀⟩

/-- The child triangle adjacent to the second original vertex. -/
def RationalTriangle.child₁ (T : RationalTriangle) : RationalTriangle :=
  ⟨rationalMidpoint T.v₀ T.v₁, T.v₁, rationalMidpoint T.v₁ T.v₂⟩

/-- The child triangle adjacent to the third original vertex. -/
def RationalTriangle.child₂ (T : RationalTriangle) : RationalTriangle :=
  ⟨rationalMidpoint T.v₂ T.v₀, rationalMidpoint T.v₁ T.v₂, T.v₂⟩

/-- The central midpoint child triangle, in the actual certificate order. -/
def RationalTriangle.child₃ (T : RationalTriangle) : RationalTriangle :=
  ⟨rationalMidpoint T.v₀ T.v₁, rationalMidpoint T.v₁ T.v₂,
    rationalMidpoint T.v₂ T.v₀⟩

/-- The actual four midpoint triangles cover every point of the original closed triangle. -/
theorem RationalTriangle.contains_child_of_contains (T : RationalTriangle) {p : ℝ × ℝ}
    (hp : T.Contains p) :
    T.child₀.Contains p ∨ T.child₁.Contains p ∨
      T.child₂.Contains p ∨ T.child₃.Contains p := by
  rcases hp with ⟨x, y, hx, hy, hxy, rfl⟩
  by_cases h₀ : x + y ≤ 1 / 2
  · left
    refine ⟨2 * x, 2 * y, by positivity, by positivity, by linarith, ?_⟩
    ext <;> simp only [point, child₀, rationalMidpoint, Rat.cast_add, Rat.cast_div,
      Rat.cast_ofNat] <;> ring
  by_cases h₁ : 1 / 2 ≤ x
  · right; left
    refine ⟨2 * x - 1, 2 * y, by linarith, by positivity, by linarith, ?_⟩
    ext <;> simp only [point, child₁, rationalMidpoint, Rat.cast_add, Rat.cast_div,
      Rat.cast_ofNat] <;> ring
  by_cases h₂ : 1 / 2 ≤ y
  · right; right; left
    refine ⟨2 * x, 2 * y - 1, by positivity, by linarith, by linarith, ?_⟩
    ext <;> simp only [point, child₂, rationalMidpoint, Rat.cast_add, Rat.cast_div,
      Rat.cast_ofNat] <;> ring
  · right; right; right
    refine ⟨2 * (x + y) - 1, 1 - 2 * x, by linarith, by linarith, by linarith, ?_⟩
    ext <;> simp only [point, child₃, rationalMidpoint, Rat.cast_add, Rat.cast_div,
      Rat.cast_ofNat] <;> ring

end PartialBalayage.Maximal.Square
