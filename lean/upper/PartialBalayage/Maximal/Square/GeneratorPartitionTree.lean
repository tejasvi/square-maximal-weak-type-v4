/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: interior support bound u + v < 264/5. -/
module

public import PartialBalayage.Maximal.Square.GeneratorRectangleSubdivision

/-!
# Sound finite generator subdivision trees

Every branch is checked against the four actual closed dyadic children. Only an
exact exterior lower-corner inequality permits pruning. Consequently a valid
tree covers every point of its root inside the true strict support triangle.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- A finite proposed subdivision with explicit rectangles and leaf labels. -/
inductive GeneratorPartitionTree (σ : Type) where
  | leaf (rectangle : GeneratorRectangle) (label : σ)
  | pruned (rectangle : GeneratorRectangle)
  | branch (rectangle : GeneratorRectangle)
      (lowerLower lowerUpper upperLower upperUpper : GeneratorPartitionTree σ)

namespace GeneratorPartitionTree

/-- The actual proposed root rectangle of the finite subdivision. -/
def root {σ : Type} : GeneratorPartitionTree σ → GeneratorRectangle
  | .leaf T _ => T
  | .pruned T => T
  | .branch T _ _ _ _ => T

/-- Exact finite checks connecting all leaves, subdivisions and excluded rectangles. -/
def IsValid {σ : Type} (leaves : σ → GeneratorRectangle) : GeneratorPartitionTree σ → Prop
  | .leaf T i => T = leaves i
  | .pruned T => 264 / 5 ≤ T.lowerU + T.lowerV
  | .branch T ll lu ul uu =>
      ll.root = T.child 0 0 ∧ lu.root = T.child 0 1 ∧
        ul.root = T.child 1 0 ∧ uu.root = T.child 1 1 ∧
        ll.IsValid leaves ∧ lu.IsValid leaves ∧ ul.IsValid leaves ∧ uu.IsValid leaves

instance {σ : Type} [DecidableEq σ] (leaves : σ → GeneratorRectangle)
    (T : GeneratorPartitionTree σ) : Decidable (T.IsValid leaves) := by
  induction T with
  | leaf => unfold IsValid; infer_instance
  | pruned => unfold IsValid; infer_instance
  | branch T ll lu ul uu hll hlu hul huu =>
    unfold IsValid
    letI := hll
    letI := hlu
    letI := hul
    letI := huu
    infer_instance

/-- Actual closed coverage follows from the finite checked subdivision alone. -/
theorem coverage {σ : Type} {leaves : σ → GeneratorRectangle}
    {T : GeneratorPartitionTree σ} (hT : T.IsValid leaves)
    {u v : ℝ} (h : T.root.Contains u v) (hr : u + v < 264 / 5) :
    ∃ i, (leaves i).Contains u v := by
  induction T with
  | leaf R i =>
    change R = leaves i at hT
    exact ⟨i, hT ▸ h⟩
  | pruned R =>
    exact False.elim (R.not_contains_of_lower_sum_le hT hr h)
  | branch R ll lu ul uu hll hlu hul huu =>
    rcases hT with ⟨rll, rlu, rul, ruu, vll, vlu, vul, vuu⟩
    rcases h.child_coverage with h | h | h | h
    · exact hll vll (rll.symm ▸ h)
    · exact hlu vlu (rlu.symm ▸ h)
    · exact hul vul (rul.symm ▸ h)
    · exact huu vuu (ruu.symm ▸ h)

end GeneratorPartitionTree

end PartialBalayage.Maximal.Square
