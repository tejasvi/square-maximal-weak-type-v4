/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32; adds the lower radius bound used by tangents below a triangle; the per-leaf assembly moved to KernelMajorizationProofCore. -/
module

public import PartialBalayage.Maximal.Square.MajorizationLeaf
public import PartialBalayage.Maximal.Square.ArrayPolynomial

/-!
# Pointwise soundness of the checked triangle data

Three rational vertex inequalities give the radius bounds used by the radial minorants.
The conclusions hold at every point of the closed real triangle.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Bounded ordinary kernel checks cover every genuine degree-six Bernstein index. -/
theorem triangleBernstein_nonneg_of_fin_checks (c : ℕ × ℕ → ℚ)
    (hc : ∀ a b : Fin 7, a.val + b.val ≤ 6 →
      0 ≤ triangleBernsteinCoefficient c a.val b.val) :
    ∀ p ∈ triangleIndices, 0 ≤ triangleBernsteinCoefficient c p.1 p.2 := by
  intro p hp
  have h := mem_triangleIndices.mp hp
  exact hc ⟨p.1, by omega⟩ ⟨p.2, by omega⟩ h

/-- The three exact rational upper radius checks for a grid triangle. -/
def RationalTriangle.HasRadiusBound (T : RationalTriangle) (k l : ℕ) (q : ℚ) : Prop :=
  (k + l : ℚ) + T.v₀.1 + T.v₀.2 ≤ 32 * q ∧
    (k + l : ℚ) + T.v₁.1 + T.v₁.2 ≤ 32 * q ∧
      (k + l : ℚ) + T.v₂.1 + T.v₂.2 ≤ 32 * q

/-- The three exact rational lower radius checks for a grid triangle. -/
def RationalTriangle.HasRadiusLowerBound (T : RationalTriangle) (k l : ℕ) (q : ℚ) : Prop :=
  32 * q ≤ (k + l : ℚ) + T.v₀.1 + T.v₀.2 ∧
    32 * q ≤ (k + l : ℚ) + T.v₁.1 + T.v₁.2 ∧
      32 * q ≤ (k + l : ℚ) + T.v₂.1 + T.v₂.2

instance (T : RationalTriangle) (k l : ℕ) (q : ℚ) : Decidable (T.HasRadiusBound k l q) := by
  unfold RationalTriangle.HasRadiusBound; infer_instance

instance (T : RationalTriangle) (k l : ℕ) (q : ℚ) :
    Decidable (T.HasRadiusLowerBound k l q) := by
  unfold RationalTriangle.HasRadiusLowerBound; infer_instance

/-- The vertex checks give the true radius bound on the actual quarter-grid image. -/
theorem RationalTriangle.radius_le_of_vertices (T : RationalTriangle)
    (k l : ℕ) {q : ℚ} (hq : T.HasRadiusBound k l q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    ((k : ℝ) + (T.point x y).1) / 32 + ((l : ℝ) + (T.point x y).2) / 32 ≤ (q : ℝ) := by
  have hs := T.point_sum_le (q := 32 * q - (k + l : ℚ))
    (by linarith [hq.1]) (by linarith [hq.2.1]) (by linarith [hq.2.2]) hx hy hxy
  push_cast at hs
  linarith

/-- The lower vertex checks give the true lower radius bound on the actual triangle. -/
theorem RationalTriangle.le_radius_of_vertices (T : RationalTriangle)
    (k l : ℕ) {q : ℚ} (hq : T.HasRadiusLowerBound k l q)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    (q : ℝ) ≤ ((k : ℝ) + (T.point x y).1) / 32 + ((l : ℝ) + (T.point x y).2) / 32 := by
  have h₀' : 32 * q - (k + l : ℚ) ≤ T.v₀.1 + T.v₀.2 := by linarith [hq.1]
  have h₁' : 32 * q - (k + l : ℚ) ≤ T.v₁.1 + T.v₁.2 := by linarith [hq.2.1]
  have h₂' : 32 * q - (k + l : ℚ) ≤ T.v₂.1 + T.v₂.2 := by linarith [hq.2.2]
  have h₀ : ((32 * q - (k + l : ℚ) : ℚ) : ℝ) ≤ (T.v₀.1 : ℝ) + T.v₀.2 := by exact_mod_cast h₀'
  have h₁ : ((32 * q - (k + l : ℚ) : ℚ) : ℝ) ≤ (T.v₁.1 : ℝ) + T.v₁.2 := by exact_mod_cast h₁'
  have h₂ : ((32 * q - (k + l : ℚ) : ℚ) : ℝ) ≤ (T.v₂.1 : ℝ) + T.v₂.2 := by exact_mod_cast h₂'
  have h := le_affine_of_le_vertex h₀ h₁ h₂ hx hy hxy
  have he : (T.v₀.1 : ℝ) + T.v₀.2 + ((T.v₁.1 : ℝ) + T.v₁.2 - ((T.v₀.1 : ℝ) + T.v₀.2)) * x +
      ((T.v₂.1 : ℝ) + T.v₂.2 - ((T.v₀.1 : ℝ) + T.v₀.2)) * y =
        (T.point x y).1 + (T.point x y).2 := by
    unfold RationalTriangle.point; ring
  rw [he] at h
  push_cast at h
  linarith

end PartialBalayage.Maximal.Square
