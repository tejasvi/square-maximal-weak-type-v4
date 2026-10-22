/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 (1 - alpha = -7/40, -2 - alpha = -127/40, coefficients 40/47, 2160/329, 2808/329). -/
module

public import PartialBalayage.Maximal.Square.DiamondCoordinateIntegral
public import PartialBalayage.Maximal.Square.BetaPrimeIntegral

/-!
# Actual positive-beta primitives for the diagonal integral

Ordinary derivatives turn the singular plus and minus kernels into
genuinely convergent positive beta densities and explicit endpoint terms.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual positive half-interval beta density. -/
def diagonalMinusBetaDensity (t : ℝ) : ℝ :=
  t ^ (-7 / 40 : ℝ) * (1 - t) ^ (-7 / 40 : ℝ)

/-- The actual positive beta-prime density. -/
def diagonalPlusBetaDensity (t : ℝ) : ℝ :=
  t ^ (-7 / 40 : ℝ) * (1 + t) ^ (-127 / 40 : ℝ)

/-- The genuine minus-kernel endpoint primitive. -/
def diagonalMinusPrimitive (t : ℝ) : ℝ :=
  (40 / 47 : ℝ) * t ^ (-7 / 40 : ℝ) * (1 - t) ^ (-47 / 40 : ℝ) -
    (2160 / 329 : ℝ) * (1 - 2 * t) * t ^ (-7 / 40 : ℝ) * (1 - t) ^ (-7 / 40 : ℝ)

/-- The genuine plus-kernel endpoint primitive. -/
def diagonalPlusPrimitive (t : ℝ) : ℝ :=
  t ^ (-7 / 40 : ℝ) * (1 + t) ^ (-87 / 40 : ℝ)

theorem hasDerivAt_diagonalPlusPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt diagonalPlusPrimitive
      ((-7 / 40 : ℝ) * t ^ (-47 / 40 : ℝ) * (1 + t) ^ (-87 / 40 : ℝ) -
        (87 / 40 : ℝ) * diagonalPlusBetaDensity t) t := by
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const
    (p := (-7 / 40 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-87 / 40 : ℝ)) (Or.inl htp)
  convert hd₁.mul hd₂ using 1
  · rfl
  · simp only [diagonalPlusBetaDensity, id_eq,
      show (-7 / 40 : ℝ) - 1 = -47 / 40 by ring,
      show (-87 / 40 : ℝ) - 1 = -127 / 40 by ring]
    ring

/-- The actual minus primitive leaves exactly the integrable positive beta density. -/
theorem hasDerivAt_diagonalMinusPrimitive {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt diagonalMinusPrimitive
      (t ^ (-47 / 40 : ℝ) * (1 - t) ^ (-87 / 40 : ℝ) +
        (2808 / 329 : ℝ) * diagonalMinusBetaDensity t) t := by
  have hq : 0 < 1 - t := by linarith
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-7 / 40 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-47 / 40 : ℝ)) (Or.inl hq.ne')
  have hd₃ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-7 / 40 : ℝ)) (Or.inl hq.ne')
  have hd₄ := ((hasDerivAt_id t).const_mul 2).const_sub 1
  have hd := (((hd₁.const_mul (40 / 47)).mul hd₂).sub
    ((((hd₄.const_mul (2160 / 329)).mul hd₁).mul hd₃)))
  have hp : t ^ (-47 / 40 : ℝ) = t ^ (-7 / 40 : ℝ) / t := by
    calc
      _ = t ^ ((-7 / 40 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub ht, Real.rpow_one]
  have hq₁ : (1 - t) ^ (-47 / 40 : ℝ) = (1 - t) ^ (-7 / 40 : ℝ) / (1 - t) := by
    calc
      _ = (1 - t) ^ ((-7 / 40 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hq, Real.rpow_one]
  have hq₂ : (1 - t) ^ (-87 / 40 : ℝ) = (1 - t) ^ (-7 / 40 : ℝ) / (1 - t) ^ 2 := by
    calc
      _ = (1 - t) ^ ((-7 / 40 : ℝ) - 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hq, Real.rpow_two]
  convert hd using 1
  · rfl
  · simp only [diagonalMinusBetaDensity, id_eq, Pi.mul_apply,
      show (-7 / 40 : ℝ) - 1 = -47 / 40 by ring,
      show (-47 / 40 : ℝ) - 1 = -87 / 40 by ring]
    rw [hp, hq₁, hq₂]
    field_simp
    ring

end PartialBalayage.Maximal.Square
