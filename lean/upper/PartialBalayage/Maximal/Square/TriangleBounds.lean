/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TriangleGeometry

/-!
# Genuine affine coordinate and radius bounds on certificate triangles

Rational inequalities checked at the three vertices control all actual real points of
the closed triangle by barycentric nonnegativity. This justifies the grid-cell and
maximum-radius conditions used in every majorization leaf.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Exact rational membership in a closed unit grid cell. -/
def vertexInUnitBox (v : ℚ × ℚ) : Prop := 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 ∧ v.2 ≤ 1

/-- The three vertex checks giving actual unit-cell containment of a rational triangle. -/
def RationalTriangle.InUnitBox (T : RationalTriangle) : Prop :=
  vertexInUnitBox T.v₀ ∧ vertexInUnitBox T.v₁ ∧ vertexInUnitBox T.v₂

/-- A bound at three scalar vertices gives a genuine affine bound throughout the triangle. -/
theorem affine_le_of_vertex_le {a b c bound x y : ℝ}
    (ha : a ≤ bound) (hb : b ≤ bound) (hc : c ≤ bound)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    a + (b - a) * x + (c - a) * y ≤ bound := by
  have h₀ := mul_nonneg (sub_nonneg.mpr ha) (by linarith : 0 ≤ 1 - x - y)
  have h₁ := mul_nonneg (sub_nonneg.mpr hb) hx
  have h₂ := mul_nonneg (sub_nonneg.mpr hc) hy
  nlinarith

/-- A lower bound at three scalar vertices also holds throughout the actual triangle. -/
theorem le_affine_of_le_vertex {a b c bound x y : ℝ}
    (ha : bound ≤ a) (hb : bound ≤ b) (hc : bound ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    bound ≤ a + (b - a) * x + (c - a) * y := by
  have h₀ := mul_nonneg (sub_nonneg.mpr ha) (by linarith : 0 ≤ 1 - x - y)
  have h₁ := mul_nonneg (sub_nonneg.mpr hb) hx
  have h₂ := mul_nonneg (sub_nonneg.mpr hc) hy
  nlinarith

/-- The actual affine point lies in the closed unit cell after the rational vertex checks. -/
theorem RationalTriangle.point_in_unitBox (T : RationalTriangle) (hT : T.InUnitBox)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    0 ≤ (T.point x y).1 ∧ (T.point x y).1 ≤ 1 ∧
      0 ≤ (T.point x y).2 ∧ (T.point x y).2 ≤ 1 := by
  rcases hT with ⟨⟨h₀₀, h₀₁, h₀₂, h₀₃⟩,
    ⟨h₁₀, h₁₁, h₁₂, h₁₃⟩, ⟨h₂₀, h₂₁, h₂₂, h₂₃⟩⟩
  unfold point
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_affine_of_le_vertex (a := (T.v₀.1 : ℝ)) (b := (T.v₁.1 : ℝ))
      (c := (T.v₂.1 : ℝ)) (by exact_mod_cast h₀₀) (by exact_mod_cast h₁₀)
      (by exact_mod_cast h₂₀) hx hy hxy
  · exact affine_le_of_vertex_le (a := (T.v₀.1 : ℝ)) (b := (T.v₁.1 : ℝ))
      (c := (T.v₂.1 : ℝ)) (by exact_mod_cast h₀₁) (by exact_mod_cast h₁₁)
      (by exact_mod_cast h₂₁) hx hy hxy
  · exact le_affine_of_le_vertex (a := (T.v₀.2 : ℝ)) (b := (T.v₁.2 : ℝ))
      (c := (T.v₂.2 : ℝ)) (by exact_mod_cast h₀₂) (by exact_mod_cast h₁₂)
      (by exact_mod_cast h₂₂) hx hy hxy
  · exact affine_le_of_vertex_le (a := (T.v₀.2 : ℝ)) (b := (T.v₁.2 : ℝ))
      (c := (T.v₂.2 : ℝ)) (by exact_mod_cast h₀₃) (by exact_mod_cast h₁₃)
      (by exact_mod_cast h₂₃) hx hy hxy

/-- Three exact rational radius checks imply the true radius bound on every affine point. -/
theorem RationalTriangle.point_sum_le (T : RationalTriangle) {q : ℚ}
    (h₀ : T.v₀.1 + T.v₀.2 ≤ q) (h₁ : T.v₁.1 + T.v₁.2 ≤ q)
    (h₂ : T.v₂.1 + T.v₂.2 ≤ q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    (T.point x y).1 + (T.point x y).2 ≤ (q : ℝ) := by
  have h₀' : (T.v₀.1 : ℝ) + T.v₀.2 ≤ (q : ℝ) := by exact_mod_cast h₀
  have h₁' : (T.v₁.1 : ℝ) + T.v₁.2 ≤ (q : ℝ) := by exact_mod_cast h₁
  have h₂' : (T.v₂.1 : ℝ) + T.v₂.2 ≤ (q : ℝ) := by exact_mod_cast h₂
  have h := affine_le_of_vertex_le h₀' h₁' h₂' hx hy hxy
  convert h using 1
  unfold point
  ring

end PartialBalayage.Maximal.Square
