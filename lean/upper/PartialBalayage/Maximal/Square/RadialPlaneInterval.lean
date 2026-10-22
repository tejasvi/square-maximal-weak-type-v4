/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40; the radius powers are enclosed by 20th-power checks. -/
module

public import PartialBalayage.Maximal.Square.RadialModelTangent
public import PartialBalayage.Maximal.Square.RationalInterval

/-!
# Exact intervals for genuine finite radial tangent planes

The finite incoming-tail polynomial and its derivatives are evaluated over the
rationals. Two ordinary 20th-power checks enclose the remaining negative powers
at the positive tangent radius. The resulting intervals contain the actual value
and both derivatives of the proved radial lower model for any finite truncation.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Exact rational evaluation of a finite coefficient polynomial. -/
def rationalRadialValue (c : ℕ → ℚ) (N : ℕ) (x : ℚ) : ℚ :=
  ∑ n ∈ Finset.range N, c n * x ^ n

/-- Exact rational evaluation of the derivative of a finite coefficient polynomial. -/
def rationalRadialDerivative (c : ℕ → ℚ) (N : ℕ) (x : ℚ) : ℚ :=
  ∑ n ∈ Finset.range N, c n * n * x ^ (n - 1)

theorem rationalRadialValue_cast (c : ℕ → ℚ) (N : ℕ) (x : ℚ) :
    (rationalRadialValue c N x : ℝ) =
      ∑ n ∈ Finset.range N, (c n : ℝ) * (x : ℝ) ^ n := by
  simp [rationalRadialValue]

theorem rationalRadialDerivative_cast (c : ℕ → ℚ) (N : ℕ) (x : ℚ) :
    (rationalRadialDerivative c N x : ℝ) = radialPolynomialDerivative c N (x : ℝ) := by
  simp [rationalRadialDerivative, radialPolynomialDerivative]

/-- Proposed root intervals for one actual finite radial tangent plane. -/
structure RadialGeneratorPlaneData where
  radius : ℚ
  difference : ℚ
  terms : ℕ
  radiusPower : RationalInterval
  derivativePower : RationalInterval

namespace RadialGeneratorPlaneData

/-- Exact checks on the genuine tangent radius and its two negative powers. -/
def IsValid (D : RadialGeneratorPlaneData) : Prop :=
  0 < D.radius ∧
    IsPowerEnclosureDeg 20 D.radius (-47) D.radiusPower.lower D.radiusPower.upper ∧
    IsPowerEnclosureDeg 20 D.radius (-67) D.derivativePower.lower D.derivativePower.upper

instance (D : RadialGeneratorPlaneData) : Decidable D.IsValid := by
  unfold IsValid IsPowerEnclosureDeg
  infer_instance

/-- Exact value interval for the actual finite lower model. -/
def valueInterval (D : RadialGeneratorPlaneData) (S ρ R : ℚ) : RationalInterval :=
  (D.radiusPower.scale S).add (RationalInterval.point (2 * ρ *
    (rationalRadialValue radialIncomingCoefficient D.terms (D.radius / R) +
      rationalRadialValue radialEvenCoefficient D.terms (D.difference / R))))

/-- Exact radius-derivative interval for the actual finite lower model. -/
def radiusDerivativeInterval (D : RadialGeneratorPlaneData) (S ρ R : ℚ) :
    RationalInterval :=
  (D.derivativePower.scale ((-47 / 20) * S)).add (RationalInterval.point
    (2 * ρ / R * rationalRadialDerivative radialIncomingCoefficient D.terms (D.radius / R)))

/-- Exact coordinate-difference derivative interval for the actual finite lower model. -/
def differenceDerivativeInterval (D : RadialGeneratorPlaneData) (ρ R : ℚ) :
    RationalInterval :=
  RationalInterval.point
    (2 * ρ / R * rationalRadialDerivative radialEvenCoefficient D.terms (D.difference / R))

theorem radiusPower_contains {D : RadialGeneratorPlaneData} (hD : D.IsValid) :
    D.radiusPower.Contains ((D.radius : ℝ) ^ (-47 / 20 : ℝ)) := by
  have hp := hD.2.1.rpow_bounds (by norm_num) hD.1.le
  simpa only [RationalInterval.Contains, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using hp

theorem derivativePower_contains {D : RadialGeneratorPlaneData} (hD : D.IsValid) :
    D.derivativePower.Contains ((D.radius : ℝ) ^ (-67 / 20 : ℝ)) := by
  have hp := hD.2.2.rpow_bounds (by norm_num) hD.1.le
  simpa only [RationalInterval.Contains, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using hp

/-- The checked rational value interval contains the actual model value. -/
theorem valueInterval_contains {D : RadialGeneratorPlaneData} (hD : D.IsValid)
    (S ρ R : ℚ) :
    (D.valueInterval S ρ R).Contains
      (radialGeneratorLowerModel S ρ R D.terms D.radius D.difference) := by
  have hp := (D.radiusPower_contains hD).scale S
  have ht := RationalInterval.point_contains (2 * ρ *
    (rationalRadialValue radialIncomingCoefficient D.terms (D.radius / R) +
      rationalRadialValue radialEvenCoefficient D.terms (D.difference / R)))
  have h := hp.add ht
  simpa [valueInterval, radialGeneratorLowerModel, rationalRadialValue,
    radialPositivePolynomial, radialEvenPolynomial] using h

/-- The checked rational derivative interval contains the actual radius derivative. -/
theorem radiusDerivativeInterval_contains {D : RadialGeneratorPlaneData} (hD : D.IsValid)
    (S ρ R : ℚ) :
    (D.radiusDerivativeInterval S ρ R).Contains
      (radialGeneratorLowerModelDr S ρ R D.terms D.radius) := by
  have hp := (D.derivativePower_contains hD).scale ((-47 / 20) * S)
  have ht := RationalInterval.point_contains
    (2 * ρ / R * rationalRadialDerivative radialIncomingCoefficient D.terms (D.radius / R))
  have h := hp.add ht
  simpa [radiusDerivativeInterval, radialGeneratorLowerModelDr, rationalRadialDerivative,
    radialPolynomialDerivative] using h

/-- The exact rational difference derivative is the genuine derivative of the model. -/
theorem differenceDerivativeInterval_contains (D : RadialGeneratorPlaneData) (ρ R : ℚ) :
    (D.differenceDerivativeInterval ρ R).Contains
      (radialGeneratorLowerModelDd ρ R D.terms D.difference) := by
  have h := RationalInterval.point_contains
    (2 * ρ / R * rationalRadialDerivative radialEvenCoefficient D.terms (D.difference / R))
  simpa [differenceDerivativeInterval, radialGeneratorLowerModelDd,
    rationalRadialDerivative, radialPolynomialDerivative] using h

end RadialGeneratorPlaneData

end PartialBalayage.Maximal.Square
