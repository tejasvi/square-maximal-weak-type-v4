/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
import Hl47a.Statement
import PartialBalayage.Maximal.SquareWeakBounds

/-!
# `c₂ ≤ 3.59123` for centred squares

The definitions of `Hl47a.Statement` are, up to names, those of `PartialBalayage.TableDefinitions`,
so the constant is definitionally `PartialBalayage.cubeWeakTypeConstant 2`, which the ported
partial-balayage proof bounds strictly by `359123/100000`.
-/

namespace Hl47a

open MeasureTheory
open scoped ENNReal

theorem weakTypeConstant_eq_cubeWeakTypeConstant (d : ℕ) :
    weakTypeConstant d = PartialBalayage.cubeWeakTypeConstant d :=
  rfl

/-- `c₂ < 3.59123`. -/
theorem weakTypeConstant_two_lt : weakTypeConstant 2 < ENNReal.ofReal (359123 / 100000) :=
  PartialBalayage.Maximal.square_weakTypeConstant_lt_3_59123

/-- The paper's Theorem 1.2: `c₂ ≤ 3.59123`. -/
theorem weakTypeConstant_two_le : weakTypeConstant 2 ≤ ENNReal.ofReal (359123 / 100000) :=
  weakTypeConstant_two_lt.le

/-- `3.59123` is a weak type `(1, 1)` bound for centred squares. -/
theorem isWeakTypeBound_two : IsWeakTypeBound 2 (ENNReal.ofReal (359123 / 100000)) := by
  obtain ⟨C, hC, hlt⟩ := sInf_lt_iff.mp weakTypeConstant_two_lt
  intro f hf α
  have hle := hlt.le
  exact (hC f hf α).trans (by gcongr)

/-- The paper's form with non-strict level sets and real levels `λ > 0`. -/
theorem nonstrict_two : NonstrictClaim := by
  intro f hf l hl
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  have hl0 : ENNReal.ofReal l ≠ 0 := by simpa using hl
  have hlt : a * ENNReal.ofReal l < ENNReal.ofReal l := by
    simpa [mul_comm] using ENNReal.mul_lt_mul_right hl0 ENNReal.ofReal_ne_top ha
  calc a * (ENNReal.ofReal l * volume {x | ENNReal.ofReal l ≤ maximalFunction f x})
      = (a * ENNReal.ofReal l) * volume {x | ENNReal.ofReal l ≤ maximalFunction f x} := by
        rw [mul_assoc]
    _ ≤ (a * ENNReal.ofReal l) * volume {x | a * ENNReal.ofReal l < maximalFunction f x} := by
        refine mul_le_mul' le_rfl (measure_mono ?_)
        intro x hx
        exact hlt.trans_le hx
    _ ≤ ENNReal.ofReal (359123 / 100000) * ∫⁻ x, ‖f x‖ₑ := isWeakTypeBound_two f hf _

end Hl47a
