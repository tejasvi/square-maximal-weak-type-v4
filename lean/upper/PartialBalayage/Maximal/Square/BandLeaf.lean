/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandLine2
public import PartialBalayage.Maximal.Square.BandDensity
public import PartialBalayage.Maximal.Square.GeneratorLeafData

/-!
# Checked leaves outside the diamond

A band leaf is a dyadic square with computed coordinate data and, for each of the two lines
through its far corner, the enclosure data of the exterior line integral. The radial term is
bounded below by the far-corner plane with rational value and slopes; the spline term is
bounded as for the interior leaves. A positive rectangle bound proves positivity of the
exterior source density at every point of the leaf outside the diamond.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- One candidate leaf outside the diamond. -/
structure BandLeafData where
  rectangle : GeneratorRectangle
  coordinateU : GeneratorCoordinateData
  coordinateV : GeneratorCoordinateData
  line1 : Option BandLineData2
  line2 : Option BandLineData2

namespace BandLeafData

variable (C : BandConstants)

def cornerU (D : BandLeafData) : ℚ := D.rectangle.lowerU + D.rectangle.width

def cornerV (D : BandLeafData) : ℚ := D.rectangle.lowerV + D.rectangle.width

def lineValue : Option BandLineData2 → ℚ
  | some L => BandLineData2.lineLower C L
  | none => 0

def slopeUValue : Option BandLineData2 → ℚ
  | some L => BandLineData2.slopeULower C L
  | none => 0

def slopeVValue : Option BandLineData2 → ℚ
  | some L => BandLineData2.slopeVLower C L
  | none => 0

/-- The rational value of the radial plane at the far corner. -/
def radialK (D : BandLeafData) : ℚ := lineValue C D.line1 + lineValue C D.line2

/-- The rational first-coordinate slope (grid units). -/
def radialGu (D : BandLeafData) : ℚ := (slopeUValue C D.line1 + slopeVValue C D.line2) / 32

/-- The rational second-coordinate slope (grid units). -/
def radialGv (D : BandLeafData) : ℚ := (slopeVValue C D.line1 + slopeUValue C D.line2) / 32

/-- The radial plane coefficients about the rectangle midpoint. -/
def radialCoefficients (D : BandLeafData) (p : RectangleIndex) : ℚ :=
  let uc := (D.coordinateU.cubic.cell.val : ℚ) + D.coordinateU.cubic.midpoint
  let vc := (D.coordinateV.cubic.cell.val : ℚ) + D.coordinateV.cubic.midpoint
  if p = (0, 0) then
    generatorRadialCoefficient * (radialK C D + radialGu C D * (D.cornerU - uc) +
      radialGv C D * (D.cornerV - vc))
  else if p = (1, 0) then -(generatorRadialCoefficient * radialGu C D)
  else if p = (0, 1) then -(generatorRadialCoefficient * radialGv C D)
  else 0

/-- The exact rectangle lower bound of a band leaf. -/
def lowerBound (D : BandLeafData) : ℚ :=
  bernsteinIntervalLower
      (generatorCombinedIntervals D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers splineGeneratorFactorInterval
        (fun p ↦ RationalInterval.point (radialCoefficients C D p))) D.rectangle.radius -
    splineGeneratorFactorInterval.upper *
      generatorApproximationError D.coordinateU.cubic D.coordinateV.cubic
        D.coordinateU.powers D.coordinateV.powers

/-- The line data refer to the far corner, or the line misses the diamond. -/
def LineMeta (a b : ℚ) : Option BandLineData2 → Prop
  | some L => L.a = a ∧ L.b = b ∧ L.IsValid
  | none => 33 / 20 ≤ b

instance (a b : ℚ) (L : Option BandLineData2) : Decidable (LineMeta a b L) := by
  cases L <;> unfold LineMeta <;> infer_instance

/-- Geometric metadata and line data checks. -/
def MetadataValid (D : BandLeafData) : Prop :=
  D.coordinateU.cubic.width = D.rectangle.width ∧
    D.coordinateV.cubic.width = D.rectangle.width ∧
    (D.coordinateU.cubic.cell.val : ℚ) + D.coordinateU.cubic.lower = D.rectangle.lowerU ∧
    (D.coordinateV.cubic.cell.val : ℚ) + D.coordinateV.cubic.lower = D.rectangle.lowerV ∧
    0 ≤ D.coordinateU.cubic.lower ∧ D.coordinateU.cubic.lower + D.coordinateU.cubic.width ≤ 1 ∧
    0 ≤ D.coordinateV.cubic.lower ∧ D.coordinateV.cubic.lower + D.coordinateV.cubic.width ≤ 1 ∧
    LineMeta (D.cornerU / 32) (D.cornerV / 32) D.line1 ∧
    LineMeta (D.cornerV / 32) (D.cornerU / 32) D.line2

instance (D : BandLeafData) : Decidable D.MetadataValid := by
  unfold MetadataValid; infer_instance

/-- All checks of a band leaf. -/
def IsValid (D : BandLeafData) : Prop := D.MetadataValid ∧ 0 < lowerBound C D

instance (D : BandLeafData) : Decidable (IsValid C D) := by
  unfold IsValid; infer_instance

variable {C}

/-- The exterior line integral at a point below the corner is above the rational plane. -/
theorem line_lower_plane (hC : C.IsValid) {a₁ b₁ : ℚ} {L : Option BandLineData2}
    (hL : LineMeta a₁ b₁ L) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : supportRadius < a + b)
    (haa : a ≤ a₁) (hbb : b ≤ b₁) :
    (lineValue C L : ℝ) + (slopeUValue C L : ℝ) * ((a₁ : ℝ) - a) +
        (slopeVValue C L : ℝ) * ((b₁ : ℝ) - b) ≤ bandLine a b := by
  have hplane := bandLine_plane_le' ha hb hr haa hbb
  cases L with
  | none =>
    simp only [lineValue, slopeUValue, slopeVValue, Rat.cast_zero, zero_mul, add_zero]
    have hb₁ : supportRadius ≤ (b₁ : ℝ) := by
      have h : ((33 / 20 : ℚ) : ℝ) ≤ (b₁ : ℝ) := by exact_mod_cast hL
      simpa [supportRadius] using h
    rw [bandLine_eq_zero_of_le hb₁, bandSlopeU_eq_zero_of_le hb₁, bandSlopeV_eq_zero_of_le hb₁]
      at hplane
    simpa using hplane
  | some L =>
    obtain ⟨hLa, hLb, hLv⟩ := hL
    simp only [lineValue, slopeUValue, slopeVValue]
    have h₁ := BandLineData2.lineLower_le hC hLv
    have h₂ := BandLineData2.slopeULower_le hC hLv
    have h₃ := BandLineData2.slopeVLower_le hC hLv
    rw [hLa, hLb] at h₁ h₂ h₃
    have hda : (0 : ℝ) ≤ (a₁ : ℝ) - a := by linarith
    have hdb : (0 : ℝ) ≤ (b₁ : ℝ) - b := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h₂ hda, mul_le_mul_of_nonneg_right h₃ hdb]

theorem rectanglePolynomial_plane (r₀ r₁ r₂ : ℝ) (x y : ℝ) :
    rectanglePolynomial (fun p ↦ if p = (0, 0) then r₀ else if p = (1, 0) then r₁
      else if p = (0, 1) then r₂ else 0) x y = r₀ + r₁ * x + r₂ * y := by
  simp only [rectanglePolynomial, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp
  ring

/-- A checked band leaf is positive at every point of its rectangle outside the diamond. -/
theorem positivity (hC : C.IsValid) {D : BandLeafData} (hD : IsValid C D) {u v : ℝ}
    (h : D.rectangle.Contains u v) (hu : 0 < u) (hv : 0 < v) (hr : 264 / 5 < u + v) :
    0 < bandDensity u v := by
  rcases hD with ⟨⟨wU, wV, loU, loV, lU, uU, lV, uV, hL₁, hL₂⟩, hL⟩
  let t : ℝ := u - (D.coordinateU.cubic.cell.val : ℝ)
  let s : ℝ := v - (D.coordinateV.cubic.cell.val : ℝ)
  have loU' : (D.coordinateU.cubic.cell.val : ℝ) + (D.coordinateU.cubic.lower : ℝ) =
      (D.rectangle.lowerU : ℝ) := by exact_mod_cast loU
  have loV' : (D.coordinateV.cubic.cell.val : ℝ) + (D.coordinateV.cubic.lower : ℝ) =
      (D.rectangle.lowerV : ℝ) := by exact_mod_cast loV
  have wU' : (D.coordinateU.cubic.width : ℝ) = (D.rectangle.width : ℝ) := by exact_mod_cast wU
  have wV' : (D.coordinateV.cubic.width : ℝ) = (D.rectangle.width : ℝ) := by exact_mod_cast wV
  have ht₀ : (D.coordinateU.cubic.lower : ℝ) ≤ t := by dsimp [t]; linarith [h.1]
  have ht₁ : t ≤ ((D.coordinateU.cubic.lower + D.coordinateU.cubic.width : ℚ) : ℝ) := by
    simp only [t, Rat.cast_add]
    have he := h.2.1
    rw [Rat.cast_add] at he
    linarith
  have hs₀ : (D.coordinateV.cubic.lower : ℝ) ≤ s := by dsimp [s]; linarith [h.2.2.1]
  have hs₁ : s ≤ ((D.coordinateV.cubic.lower + D.coordinateV.cubic.width : ℚ) : ℝ) := by
    simp only [s, Rat.cast_add]
    have he := h.2.2.2
    rw [Rat.cast_add] at he
    linarith
  have htu : 0 ≤ t := (show (0 : ℝ) ≤ (D.coordinateU.cubic.lower : ℝ) by exact_mod_cast lU).trans ht₀
  have htv : t ≤ 1 := ht₁.trans (by exact_mod_cast uU)
  have hsu : 0 ≤ s := (show (0 : ℝ) ≤ (D.coordinateV.cubic.lower : ℝ) by exact_mod_cast lV).trans hs₀
  have hsv : s ≤ 1 := hs₁.trans (by exact_mod_cast uV)
  have heU : (D.coordinateU.cubic.cell.val : ℝ) + t = u := by dsimp [t]; ring
  have heV : (D.coordinateV.cubic.cell.val : ℝ) + s = v := by dsimp [s]; ring
  have hU := D.coordinateU.isValid
  have hV := D.coordinateV.isValid
  have hLow := generatorCombinedIntervals_lower hU.1 hV.1 D.coordinateU.powers_valid
    D.coordinateV.powers_valid hU.2.1 hV.2.1 hU.2.2 hV.2.2 splineGeneratorFactorInterval_contains
    splineGeneratorFactorInterval_lower_nonneg
    (R := fun p ↦ RationalInterval.point (radialCoefficients C D p))
    (r := fun p ↦ (radialCoefficients C D p : ℝ)) (fun p ↦ RationalInterval.point_contains _)
    (δ := D.rectangle.radius) (by simp only [GeneratorRectangle.radius, wU])
    (by simp only [GeneratorRectangle.radius, wV]) htu htv hsu hsv ht₀ ht₁ hs₀ hs₁
  -- the plane polynomial
  set uc : ℚ := (D.coordinateU.cubic.cell.val : ℚ) + D.coordinateU.cubic.midpoint
  set vc : ℚ := (D.coordinateV.cubic.cell.val : ℚ) + D.coordinateV.cubic.midpoint
  have hplane : rectanglePolynomial (fun p ↦ (radialCoefficients C D p : ℝ))
      (t - (D.coordinateU.cubic.midpoint : ℝ)) (s - (D.coordinateV.cubic.midpoint : ℝ)) =
      (generatorRadialCoefficient : ℝ) * ((radialK C D : ℝ) + (radialGu C D : ℝ) * ((D.cornerU : ℝ) - u) +
        (radialGv C D : ℝ) * ((D.cornerV : ℝ) - v)) := by
    have hfun : (fun p ↦ (radialCoefficients C D p : ℝ)) = fun p ↦
        if p = (0, 0) then ((generatorRadialCoefficient * (radialK C D + radialGu C D * (D.cornerU - uc) +
          radialGv C D * (D.cornerV - vc)) : ℚ) : ℝ)
        else if p = (1, 0) then ((-(generatorRadialCoefficient * radialGu C D) : ℚ) : ℝ)
        else if p = (0, 1) then ((-(generatorRadialCoefficient * radialGv C D) : ℚ) : ℝ) else 0 := by
      funext p
      unfold radialCoefficients
      split_ifs <;> simp [uc, vc]
    rw [hfun, rectanglePolynomial_plane]
    simp only [uc, vc]
    push_cast
    rw [← heU, ← heV]
    ring
  -- the radial bound
  have hc : (0 : ℝ) < radialCoefficient := by norm_num [radialCoefficient]
  have hcq : (generatorRadialCoefficient : ℝ) = radialCoefficient := by
    norm_num [generatorRadialCoefficient, radialCoefficient]
  have hcorU : u ≤ (D.cornerU : ℝ) := by
    have he := h.2.1; simp only [cornerU]; push_cast at he ⊢; linarith
  have hcorV : v ≤ (D.cornerV : ℝ) := by
    have he := h.2.2.2; simp only [cornerV]; push_cast at he ⊢; linarith
  have hR : supportRadius < u / 32 + v / 32 := by norm_num only [supportRadius]; linarith
  have h₁ := line_lower_plane hC hL₁ (a := u / 32) (b := v / 32) (by positivity) (by positivity) hR
    (by push_cast; linarith) (by push_cast; linarith)
  have h₂ := line_lower_plane hC hL₂ (a := v / 32) (b := u / 32) (by positivity) (by positivity)
    (by linarith) (by push_cast; linarith) (by push_cast; linarith)
  have hrad : (radialK C D : ℝ) + (radialGu C D : ℝ) * ((D.cornerU : ℝ) - u) +
      (radialGv C D : ℝ) * ((D.cornerV : ℝ) - v) ≤ bandLine (u / 32) (v / 32) + bandLine (v / 32) (u / 32) := by
    simp only [radialK, radialGu, radialGv]
    push_cast at h₁ h₂ ⊢
    nlinarith [h₁, h₂]
  have hLB : (0 : ℝ) < (lowerBound C D : ℝ) := by exact_mod_cast hL
  have hLow' : (lowerBound C D : ℝ) ≤ splineGeneratorFactor * splineGeneratorCorrectionPower u v +
      (generatorRadialCoefficient : ℝ) * ((radialK C D : ℝ) + (radialGu C D : ℝ) * ((D.cornerU : ℝ) - u) +
        (radialGv C D : ℝ) * ((D.cornerV : ℝ) - v)) := by
    have := hLow
    rw [hplane, heU, heV] at this
    exact this
  unfold bandDensity
  rw [hcq] at hLow'
  nlinarith [mul_le_mul_of_nonneg_left hrad hc.le]

end BandLeafData

end PartialBalayage.Maximal.Square
