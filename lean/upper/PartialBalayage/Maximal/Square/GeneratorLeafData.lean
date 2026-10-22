/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid spacing 1/32, term counts up to 8192, interior bound u + v < 264/5. -/
module

public import PartialBalayage.Maximal.Square.GeneratorInteriorRectangle
public import PartialBalayage.Maximal.Square.GeneratorRectangleGeometry
public import PartialBalayage.Maximal.Square.GeneratorRadialRootData

/-!
# Actual generator leaf data and pointwise soundness

Every coordinate interval is tied to the actual dyadic rectangle by exact
endpoint and width checks. The radial tangent uses its actual midpoint, or the
upper corner near the origin. A positive computed bound then applies throughout
the real rectangle's strict support interior.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Candidate actual generator rectangle with checked coordinate and radial data. -/
structure GeneratorLeafData where
  rectangle : GeneratorRectangle
  coordinateU : GeneratorCoordinateData
  coordinateV : GeneratorCoordinateData
  terms : Fin 8193
  radialRoot : GeneratorRadialRootData

namespace GeneratorLeafData

/-- Positive tangent first coordinate, shifted to the upper corner near the origin. -/
def baseU (D : GeneratorLeafData) : ℚ :=
  if D.rectangle.lowerU + D.rectangle.lowerV < 2 * D.rectangle.width then
    D.rectangle.lowerU + D.rectangle.width else D.rectangle.centerU

/-- Positive tangent second coordinate with the same genuine geometric choice. -/
def baseV (D : GeneratorLeafData) : ℚ :=
  if D.rectangle.lowerU + D.rectangle.lowerV < 2 * D.rectangle.width then
    D.rectangle.lowerV + D.rectangle.width else D.rectangle.centerV

/-- The actual finite radial tangent at the selected physical point. -/
def plane (D : GeneratorLeafData) : RadialGeneratorPlaneData :=
  D.radialRoot.plane ((D.baseU - D.baseV) / 32) D.terms

/-- Exact genuine coefficient, power and remainder rectangle lower bound. -/
def lowerBound (D : GeneratorLeafData) : ℚ :=
  generatorCheckedRectangleLower D.coordinateU D.coordinateV D.plane
    D.baseU D.baseV D.rectangle.radius

/-- Finite actual endpoint, width and radial-center checks. -/
def MetadataValid (D : GeneratorLeafData) : Prop :=
  D.coordinateU.cubic.width = D.rectangle.width ∧
    D.coordinateV.cubic.width = D.rectangle.width ∧
    (D.coordinateU.cubic.cell.val : ℚ) + D.coordinateU.cubic.lower = D.rectangle.lowerU ∧
    (D.coordinateV.cubic.cell.val : ℚ) + D.coordinateV.cubic.lower = D.rectangle.lowerV ∧
    0 ≤ D.coordinateU.cubic.lower ∧ D.coordinateU.cubic.lower + D.coordinateU.cubic.width ≤ 1 ∧
    0 ≤ D.coordinateV.cubic.lower ∧ D.coordinateV.cubic.lower + D.coordinateV.cubic.width ≤ 1 ∧
    D.radialRoot.radius = (D.baseU + D.baseV) / 32

instance (D : GeneratorLeafData) : Decidable D.MetadataValid := by
  unfold MetadataValid
  infer_instance

/-- Actual geometric metadata and the exact positive rectangle lower-bound check. -/
def NumericalValid (D : GeneratorLeafData) : Prop :=
  D.MetadataValid ∧ 0 < D.lowerBound

instance (D : GeneratorLeafData) : Decidable D.NumericalValid := by
  unfold NumericalValid
  infer_instance

/-- All actual coordinate and scalar numerical checks for a leaf. -/
def IsValid (D : GeneratorLeafData) : Prop :=
  D.coordinateU.IsValid ∧ D.coordinateV.IsValid ∧ D.radialRoot.IsValid ∧ D.NumericalValid

instance (D : GeneratorLeafData) : Decidable D.IsValid := by
  unfold IsValid
  infer_instance

/-- A checked leaf is positive on every actual contained strict-interior point. -/
theorem positivity {D : GeneratorLeafData} (hD : D.IsValid) {u v : ℝ}
    (h : D.rectangle.Contains u v) (hu : 0 < u) (hv : 0 < v) (hr : u + v < 264 / 5) :
    0 < generatorInteriorDensity u v := by
  rcases hD with ⟨hU, hV, hRoot, hMeta, hL⟩
  rcases hMeta with ⟨wU, wV, loU, loV, lU, uU, lV, uV, hRadius⟩
  let t : ℝ := u - (D.coordinateU.cubic.cell.val : ℝ)
  let s : ℝ := v - (D.coordinateV.cubic.cell.val : ℝ)
  have loU' : (D.coordinateU.cubic.cell.val : ℝ) +
      (D.coordinateU.cubic.lower : ℝ) = (D.rectangle.lowerU : ℝ) := by
    exact_mod_cast loU
  have loV' : (D.coordinateV.cubic.cell.val : ℝ) +
      (D.coordinateV.cubic.lower : ℝ) = (D.rectangle.lowerV : ℝ) := by
    exact_mod_cast loV
  have wU' : (D.coordinateU.cubic.width : ℝ) = (D.rectangle.width : ℝ) := by
    exact_mod_cast wU
  have wV' : (D.coordinateV.cubic.width : ℝ) = (D.rectangle.width : ℝ) := by
    exact_mod_cast wV
  have ht₀ : (D.coordinateU.cubic.lower : ℝ) ≤ t := by
    dsimp [t]
    linarith [h.1]
  have ht₁ : t ≤ ((D.coordinateU.cubic.lower + D.coordinateU.cubic.width : ℚ) : ℝ) := by
    simp only [t, Rat.cast_add]
    have he := h.2.1
    rw [Rat.cast_add] at he
    linarith
  have hs₀ : (D.coordinateV.cubic.lower : ℝ) ≤ s := by
    dsimp [s]
    linarith [h.2.2.1]
  have hs₁ : s ≤ ((D.coordinateV.cubic.lower + D.coordinateV.cubic.width : ℚ) : ℝ) := by
    simp only [s, Rat.cast_add]
    have he := h.2.2.2
    rw [Rat.cast_add] at he
    linarith
  have htu : 0 ≤ t := (show (0 : ℝ) ≤ (D.coordinateU.cubic.lower : ℝ) by
    exact_mod_cast lU).trans ht₀
  have htv : t ≤ 1 := ht₁.trans (by exact_mod_cast uU)
  have hsu : 0 ≤ s := (show (0 : ℝ) ≤ (D.coordinateV.cubic.lower : ℝ) by
    exact_mod_cast lV).trans hs₀
  have hsv : s ≤ 1 := hs₁.trans (by exact_mod_cast uV)
  have heU : (D.coordinateU.cubic.cell.val : ℝ) + t = u := by dsimp [t]; ring
  have heV : (D.coordinateV.cubic.cell.val : ℝ) + s = v := by dsimp [s]; ring
  have hP : D.plane.IsValid :=
    GeneratorRadialRootData.plane_valid hRoot ((D.baseU - D.baseV) / 32) D.terms
  have he := generatorInteriorDensity_pos_of_checked_rectangle hU hV hP hRadius rfl
    (by simp only [GeneratorRectangle.radius, wU])
    (by simp only [GeneratorRectangle.radius, wV]) hL htu htv hsu hsv ht₀ ht₁ hs₀ hs₁
    (heU.symm ▸ hu) (heV.symm ▸ hv) (by simpa only [heU, heV] using hr)
  simpa only [heU, heV] using he

end GeneratorLeafData

end PartialBalayage.Maximal.Square
