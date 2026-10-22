/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40, our radial coefficient and R = 33/20; adds the upper slope for tangents taken below a triangle. -/
module

public import PartialBalayage.Maximal.Square.RadialPowerData
public import PartialBalayage.Maximal.Square.RadialTangent

/-!
# Actual height and slope bounds from the rational radial data

The rational lower-polynomial constants are connected to the actual radial tangent.
At the exact support radius the height is zero, avoiding loss from interval subtraction.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The radial coefficient as an exact rational for certificate arithmetic. -/
def radialCoefficientRat : ℚ := 1977601376167 / 1099511627776

/-- The support radius as an exact rational for certificate arithmetic. -/
def supportRadiusRat : ℚ := 33 / 20

theorem radialCoefficientRat_cast : (radialCoefficientRat : ℝ) = radialCoefficient := by
  norm_num [radialCoefficientRat, radialCoefficient]

theorem supportRadiusRat_cast : (supportRadiusRat : ℝ) = supportRadius := by
  norm_num [supportRadiusRat, supportRadius]

/-- The true downward rational height used on a certificate triangle. -/
def certifiedRadialHeight (d R : RadialPowerData) : ℚ :=
  if d.radius = supportRadiusRat then 0
  else radialCoefficientRat * (d.lowerSix - R.upperSix)

/-- The true downward rational slope used for a tangent above the triangle. -/
def certifiedRadialSlope (d : RadialPowerData) : ℚ :=
  (47 / 40) * radialCoefficientRat * d.lowerEleven

/-- The true upward rational slope used for a tangent below the triangle. -/
def certifiedRadialSlopeUpper (d : RadialPowerData) : ℚ :=
  (47 / 40) * radialCoefficientRat * d.upperEleven

/-- Every valid exact radial row encloses the actual order-47/40 power. -/
theorem RadialPowerData.six_bounds {d : RadialPowerData} (hd : d.IsValid) :
    (d.lowerSix : ℝ) ≤ (d.radius : ℝ) ^ (-(47 / 40 : ℝ)) ∧
      (d.radius : ℝ) ^ (-(47 / 40 : ℝ)) ≤ (d.upperSix : ℝ) := by
  have h := hd.2.1.rpow_bounds (by norm_num) hd.1.le
  have hc : ((-47 : ℤ) : ℝ) / ((40 : ℕ) : ℝ) = -(47 / 40 : ℝ) := by norm_num
  rw [hc] at h
  exact h

/-- Every valid exact radial row encloses the actual slope power. -/
theorem RadialPowerData.eleven_bounds {d : RadialPowerData} (hd : d.IsValid) :
    (d.lowerEleven : ℝ) ≤ (d.radius : ℝ) ^ (-(87 / 40 : ℝ)) ∧
      (d.radius : ℝ) ^ (-(87 / 40 : ℝ)) ≤ (d.upperEleven : ℝ) := by
  have h := hd.2.2.rpow_bounds (by norm_num) hd.1.le
  have hc : ((-87 : ℤ) : ℝ) / ((40 : ℕ) : ℝ) = -(87 / 40 : ℝ) := by norm_num
  rw [hc] at h
  exact h

/-- The actual certified rational height is below the actual radial tangent height. -/
theorem certifiedRadialHeight_le {d R : RadialPowerData}
    (hd : d.IsValid) (hR : R.IsValid) (hRradius : R.radius = supportRadiusRat) :
    (certifiedRadialHeight d R : ℝ) ≤ radialCoefficient *
      ((d.radius : ℝ) ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))) := by
  unfold certifiedRadialHeight
  split_ifs with h
  · rw [h, supportRadiusRat_cast, sub_self, mul_zero, Rat.cast_zero]
  · have h₀ := (RadialPowerData.six_bounds hd).1
    have h₁ := (RadialPowerData.six_bounds hR).2
    rw [hRradius, supportRadiusRat_cast] at h₁
    simp only [Rat.cast_mul, Rat.cast_sub, radialCoefficientRat_cast]
    exact mul_le_mul_of_nonneg_left (sub_le_sub h₀ h₁) radialCoefficient_pos.le

/-- The actual certified rational slope is below the actual radial tangent slope. -/
theorem certifiedRadialSlope_le {d : RadialPowerData} (hd : d.IsValid) :
    (certifiedRadialSlope d : ℝ) ≤
      (47 / 40 : ℝ) * radialCoefficient * (d.radius : ℝ) ^ (-(87 / 40 : ℝ)) := by
  have hp : 0 ≤ (47 / 40 : ℝ) * radialCoefficient :=
    mul_nonneg (by norm_num) radialCoefficient_pos.le
  simp only [certifiedRadialSlope, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    radialCoefficientRat_cast]
  exact mul_le_mul_of_nonneg_left (RadialPowerData.eleven_bounds hd).1 hp

/-- The actual certified upper slope is above the actual radial tangent slope. -/
theorem le_certifiedRadialSlopeUpper {d : RadialPowerData} (hd : d.IsValid) :
    (47 / 40 : ℝ) * radialCoefficient * (d.radius : ℝ) ^ (-(87 / 40 : ℝ)) ≤
      (certifiedRadialSlopeUpper d : ℝ) := by
  have hp : 0 ≤ (47 / 40 : ℝ) * radialCoefficient :=
    mul_nonneg (by norm_num) radialCoefficient_pos.le
  simp only [certifiedRadialSlopeUpper, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    radialCoefficientRat_cast]
  exact mul_le_mul_of_nonneg_left (RadialPowerData.eleven_bounds hd).2 hp

/-- The certified lower slope is nonnegative. -/
theorem certifiedRadialSlope_nonneg {d : RadialPowerData} (hd : d.IsValid) :
    0 ≤ (certifiedRadialSlope d : ℝ) := by
  have h0 : (0 : ℝ) ≤ d.lowerEleven := by exact_mod_cast hd.2.2.1
  simp only [certifiedRadialSlope, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    radialCoefficientRat_cast]
  exact mul_nonneg (mul_nonneg (by norm_num) radialCoefficient_pos.le) h0

end PartialBalayage.Maximal.Square
