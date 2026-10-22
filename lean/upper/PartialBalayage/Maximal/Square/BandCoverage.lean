/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandLeaf
public import PartialBalayage.Maximal.Square.CorrectionPolynomial
public import PartialBalayage.Maximal.Square.Data.RepresentativeCoefficientMatrix
public import PartialBalayage.Maximal.Square.GeneratorRectangleSubdivision

/-!
# Zero cells and subdivision trees outside the diamond

On a unit cell whose sixteen tensor coefficients vanish the spline correction vanishes, so the
kernel vanishes at every point of the cell outside the diamond. Every other ordered cell outside
the diamond carries a subdivision tree whose leaves are checked band leaves; squares without
exterior points are pruned.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The literal coefficient lookup of a signed index pair. -/
def literalSplineCoefficient (a b : ℤ) : ℚ :=
  literalRepresentativeCoefficient (max a.natAbs b.natAbs) (min a.natAbs b.natAbs)

theorem splineCoefficient_eq_literal (a b : ℤ) : splineCoefficient a b = literalSplineCoefficient a b := by
  rw [splineCoefficient_eq_representative, representativeCoefficient_eq_literal]; rfl

/-- The sixteen tensor coefficients of a cell vanish (decidable form). -/
def ZeroCell (k l : ℤ) : Prop := ∀ i j : Fin 4, literalSplineCoefficient (k - 1 + i) (l - 1 + j) = 0

instance (k l : ℤ) : Decidable (ZeroCell k l) := by unfold ZeroCell; infer_instance

theorem splineCorrection_eq_zero_of_zeroCell {k l : ℤ} (hz : ZeroCell k l) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    splineCorrection (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) = 0 := by
  rw [splineCorrection_eq_cellPolynomial k l ht₀ ht₁ hs₀ hs₁]
  have hc : correctionCellCoefficient k l = fun _ _ ↦ 0 := by
    funext a b
    rw [correctionCellCoefficient_eq_local]
    apply Finset.sum_eq_zero
    intro p hp
    unfold cellTensorIndices at hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp₁ hp₂
    have h := hz ⟨(p.1 - (k - 1)).toNat, by omega⟩ ⟨(p.2 - (l - 1)).toNat, by omega⟩
    have e₁ : k - 1 + (((p.1 - (k - 1)).toNat : ℕ) : ℤ) = p.1 := by omega
    have e₂ : l - 1 + (((p.2 - (l - 1)).toNat : ℕ) : ℤ) = p.2 := by omega
    simp only at h
    rw [e₁, e₂] at h
    rw [splineCoefficient_eq_literal, h, zero_mul]
  rw [hc]
  exact bicubicPolynomial_zero t s

/-- On a zero cell the kernel vanishes outside the diamond. -/
theorem kernel_eq_zero_of_zeroCell {k l : ℤ} (hz : ZeroCell k l) {t s : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hr : supportRadius ≤ diamondRadius (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32))
    (hne : ¬ ((((k : ℝ) + t) / 32) = 0 ∧ (((l : ℝ) + s) / 32) = 0)) :
    kernel (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) = 0 := by
  unfold kernel
  rw [if_neg hne, splineCorrection_eq_zero_of_zeroCell hz ht₀ ht₁ hs₀ hs₁, add_zero]
  unfold radialBase
  have hp := Real.rpow_le_rpow_of_nonpos supportRadius_pos hr (by norm_num : -(47 / 40 : ℝ) ≤ 0)
  rw [max_eq_right (sub_nonpos.mpr hp), mul_zero]

/-- A finite subdivision tree of a cell outside the diamond. -/
inductive BandPartitionTree (σ : Type) where
  | leaf (rectangle : GeneratorRectangle) (label : σ)
  | pruned (rectangle : GeneratorRectangle)
  | branch (rectangle : GeneratorRectangle)
      (lowerLower lowerUpper upperLower upperUpper : BandPartitionTree σ)

namespace BandPartitionTree

def root {σ : Type} : BandPartitionTree σ → GeneratorRectangle
  | .leaf T _ => T
  | .pruned T => T
  | .branch T _ _ _ _ => T

/-- Leaf identities, subdivisions, and pruning of squares without exterior points. -/
def IsValid {σ : Type} (leaves : σ → GeneratorRectangle) : BandPartitionTree σ → Prop
  | .leaf T i => T = leaves i
  | .pruned T => T.lowerU + T.lowerV + 2 * T.width ≤ 264 / 5
  | .branch T ll lu ul uu =>
      ll.root = T.child 0 0 ∧ lu.root = T.child 0 1 ∧
        ul.root = T.child 1 0 ∧ uu.root = T.child 1 1 ∧
        ll.IsValid leaves ∧ lu.IsValid leaves ∧ ul.IsValid leaves ∧ uu.IsValid leaves

instance {σ : Type} [DecidableEq σ] (leaves : σ → GeneratorRectangle)
    (T : BandPartitionTree σ) : Decidable (T.IsValid leaves) := by
  induction T with
  | leaf => unfold IsValid; infer_instance
  | pruned => unfold IsValid; infer_instance
  | branch T ll lu ul uu hll hlu hul huu =>
    unfold IsValid
    letI := hll; letI := hlu; letI := hul; letI := huu
    infer_instance

theorem not_contains_of_upper_sum_le {T : GeneratorRectangle} {u v : ℝ}
    (hT : T.lowerU + T.lowerV + 2 * T.width ≤ 264 / 5) (hr : 264 / 5 < u + v) : ¬ T.Contains u v := by
  intro h
  have h₁ := h.2.1
  have h₂ := h.2.2.2
  have hT' : ((T.lowerU + T.lowerV + 2 * T.width : ℚ) : ℝ) ≤ ((264 / 5 : ℚ) : ℝ) := by
    exact_mod_cast hT
  push_cast at h₁ h₂ hT'
  linarith

/-- Every exterior point of the root lies in a leaf. -/
theorem coverage {σ : Type} {leaves : σ → GeneratorRectangle}
    {T : BandPartitionTree σ} (hT : T.IsValid leaves)
    {u v : ℝ} (h : T.root.Contains u v) (hr : 264 / 5 < u + v) :
    ∃ i, (leaves i).Contains u v := by
  induction T with
  | leaf R i =>
    change R = leaves i at hT
    exact ⟨i, hT ▸ h⟩
  | pruned R =>
    exact False.elim (not_contains_of_upper_sum_le hT hr h)
  | branch R ll lu ul uu hll hlu hul huu =>
    rcases hT with ⟨rll, rlu, rul, ruu, vll, vlu, vul, vuu⟩
    rcases h.child_coverage with h | h | h | h
    · exact hll vll (rll.symm ▸ h)
    · exact hlu vlu (rlu.symm ▸ h)
    · exact hul vul (rul.symm ▸ h)
    · exact huu vuu (ruu.symm ▸ h)

end BandPartitionTree

end PartialBalayage.Maximal.Square
