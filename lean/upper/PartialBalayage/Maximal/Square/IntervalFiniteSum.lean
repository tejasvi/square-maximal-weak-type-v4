/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineTaylorSum

/-!
# Sound finite interval assembly for generator tensor coefficients

Exact rational endpoint summation and signed scalar multiplication enclose the
actual centered tensor coefficients. Multiplication by the nonnegative generator
factor then preserves those enclosures.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

namespace RationalInterval

/-- Exact endpoint summation of a finite family of rational intervals. -/
def sum {ι : Type*} (s : Finset ι) (I : ι → RationalInterval) : RationalInterval :=
  ⟨∑ z ∈ s, (I z).lower, ∑ z ∈ s, (I z).upper⟩

/-- Finite interval summation contains the actual sum of all contained real values. -/
theorem Contains.sum {ι : Type*} (s : Finset ι) {I : ι → RationalInterval} {x : ι → ℝ}
    (hI : ∀ z ∈ s, (I z).Contains (x z)) :
    (RationalInterval.sum s I).Contains (∑ z ∈ s, x z) := by
  change ((∑ z ∈ s, (I z).lower : ℚ) : ℝ) ≤ _ ∧
    _ ≤ ((∑ z ∈ s, (I z).upper : ℚ) : ℝ)
  simp only [Rat.cast_sum]
  exact ⟨Finset.sum_le_sum (fun z hz ↦ (hI z hz).1),
    Finset.sum_le_sum (fun z hz ↦ (hI z hz).2)⟩

end RationalInterval

/-- Exact intervals for a finite family of genuine centered tensor products. -/
def generatorTensorIntervals {ι : Type*} (s : Finset ι) (D : ι → Fin 4 → ℚ)
    (H : ι → Fin 4 → RationalInterval) (p : RectangleIndex) : RationalInterval :=
  RationalInterval.sum s (fun z ↦ (H z p.1).scale (D z p.2))

/-- The signed finite tensor interval contains the genuine real coefficient. -/
theorem generatorTensorIntervals_contains {ι : Type*} (s : Finset ι)
    (D : ι → Fin 4 → ℚ) (H : ι → Fin 4 → RationalInterval) (h : ι → Fin 4 → ℝ)
    (hH : ∀ z ∈ s, ∀ i, (H z i).Contains (h z i)) (p : RectangleIndex) :
    (generatorTensorIntervals s D H p).Contains
      (∑ z ∈ s, (D z p.2 : ℝ) * h z p.1) := by
  apply RationalInterval.Contains.sum
  intro z hz
  exact (hH z hz p.1).scale (D z p.2)

/-- Scaling the true tensor coefficient by a genuine nonnegative enclosed factor. -/
theorem scaled_generatorTensorIntervals_contains {ι : Type*} (s : Finset ι)
    (D : ι → Fin 4 → ℚ) (H : ι → Fin 4 → RationalInterval) (h : ι → Fin 4 → ℝ)
    (hH : ∀ z ∈ s, ∀ i, (H z i).Contains (h z i))
    {S : RationalInterval} {σ : ℝ} (hS : S.Contains σ) (hS₀ : 0 ≤ S.lower)
    (p : RectangleIndex) :
    (S.nonnegMul (generatorTensorIntervals s D H p)).Contains
      (σ * ∑ z ∈ s, (D z p.2 : ℝ) * h z p.1) :=
  hS.nonnegMul (generatorTensorIntervals_contains s D H h hH p) hS₀

end PartialBalayage.Maximal.Square
