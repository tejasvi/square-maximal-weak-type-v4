/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 145 signed knots (offset 72) and exponent 73/40 for our kernel. -/
module

public import PartialBalayage.Maximal.Square.GeneratorPowerTaylorData

/-!
# Sharing the actual power checks across reflected Taylor centers

Reflection preserves the exact absolute-power and error checks, while the actual
Taylor coefficients retain the sign of the reflected center. A family can
therefore reuse the already proved positive-center root data without checking
the same 40th-power inequalities repeatedly.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square.GeneratorPowerTaylorData

/-- Reflection of the genuine Taylor center, retaining its absolute-power root data. -/
def reflect (D : GeneratorPowerTaylorData) : GeneratorPowerTaylorData :=
  { D with center := -D.center }

/-- Reflection preserves all exact checks on the actual absolute powers and error. -/
theorem IsValid.reflect {D : GeneratorPowerTaylorData} (hD : D.IsValid) :
    D.reflect.IsValid := by
  simpa only [IsValid, GeneratorPowerTaylorData.reflect, neg_ne_zero, abs_neg] using hD

@[simp] theorem reflect_center (D : GeneratorPowerTaylorData) : D.reflect.center = -D.center :=
  rfl

@[simp] theorem reflect_radius (D : GeneratorPowerTaylorData) : D.reflect.radius = D.radius :=
  rfl

/-- A finite actual Taylor family sharing positive-center data and its reflections. -/
def signedFamily (D : Fin 145 → GeneratorPowerTaylorData) (negative : Fin 145 → Bool)
    (k : Fin 145) : GeneratorPowerTaylorData :=
  if negative k then (D k).reflect else D k

/-- Every member of the shared signed family satisfies the genuine power and error checks. -/
theorem signedFamily_valid {D : Fin 145 → GeneratorPowerTaylorData}
    (hD : ∀ k, (D k).IsValid) (negative : Fin 145 → Bool) (k : Fin 145) :
    (signedFamily D negative k).IsValid := by
  unfold signedFamily
  split_ifs
  · exact (hD k).reflect
  · exact hD k

end PartialBalayage.Maximal.Square.GeneratorPowerTaylorData
