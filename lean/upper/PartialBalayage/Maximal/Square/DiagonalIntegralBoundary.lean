/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 (boundary coefficients -40/47, 40/7, 20/47; derivative coefficients 87/7, 2808/329). -/
module

public import PartialBalayage.Maximal.Square.DiagonalBetaPrimitives
public import PartialBalayage.Maximal.Square.RadialEndpointLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual diagonal integration-by-parts boundary functions

Genuine ordinary primitives cancel the singular origin and the infinite
endpoint. Their two smooth pieces agree at the actual crossing point.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

def diagonalNearDifference (t : ℝ) : ℝ :=
  (1 + t) ^ (-47 / 40 : ℝ) + (1 - t) ^ (-47 / 40 : ℝ) - 2

def diagonalFarDifference (t : ℝ) : ℝ :=
  (1 + t) ^ (-47 / 40 : ℝ) + t ^ (-47 / 40 : ℝ) - 2

/-- The true origin-side boundary function from two ordinary integrations by parts. -/
def diagonalNearBoundary (t : ℝ) : ℝ :=
  (-40 / 47 : ℝ) * t ^ (-47 / 40 : ℝ) * diagonalNearDifference t +
    (40 / 7 : ℝ) * diagonalPlusPrimitive t + diagonalMinusPrimitive t

/-- The true exterior-side boundary function. -/
def diagonalFarBoundary (t : ℝ) : ℝ :=
  (-40 / 47 : ℝ) * t ^ (-47 / 40 : ℝ) * diagonalFarDifference t +
    (40 / 7 : ℝ) * diagonalPlusPrimitive t + (20 / 47 : ℝ) * t ^ (-47 / 20 : ℝ)

theorem hasDerivAt_diagonalNearBoundary {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt diagonalNearBoundary
      (t ^ (-87 / 40 : ℝ) * diagonalNearDifference t -
        (87 / 7 : ℝ) * diagonalPlusBetaDensity t +
          (2808 / 329 : ℝ) * diagonalMinusBetaDensity t) t := by
  have hq : 0 < 1 - t := by linarith
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-47 / 40 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-47 / 40 : ℝ)) (Or.inl htp)
  have hd₃ := ((hasDerivAt_id t).const_sub 1).rpow_const
    (p := (-47 / 40 : ℝ)) (Or.inl hq.ne')
  have hd := ((((hd₁.const_mul (-40 / 47)).mul ((hd₂.add hd₃).sub_const 2)).add
    ((hasDerivAt_diagonalPlusPrimitive ht).const_mul (40 / 7))).add
      (hasDerivAt_diagonalMinusPrimitive ht ht₁))
  convert hd using 1
  · rfl
  · simp only [diagonalNearDifference, id_eq, Pi.add_apply,
      show (-47 / 40 : ℝ) - 1 = -87 / 40 by ring]
    ring

theorem hasDerivAt_diagonalFarBoundary {t : ℝ} (ht : 0 < t) :
    HasDerivAt diagonalFarBoundary
      (t ^ (-87 / 40 : ℝ) * diagonalFarDifference t -
        (87 / 7 : ℝ) * diagonalPlusBetaDensity t) t := by
  have htp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hd₁ := Real.hasDerivAt_rpow_const (p := (-47 / 40 : ℝ)) (Or.inl ht.ne')
  have hd₂ := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := (-47 / 40 : ℝ)) (Or.inl htp)
  have hd₃ := Real.hasDerivAt_rpow_const (p := (-47 / 20 : ℝ)) (Or.inl ht.ne')
  have hd := ((((hd₁.const_mul (-40 / 47)).mul ((hd₂.add hd₁).sub_const 2)).add
    ((hasDerivAt_diagonalPlusPrimitive ht).const_mul (40 / 7))).add
      (hd₃.const_mul (20 / 47)))
  have hp : t ^ (-67 / 20 : ℝ) = t ^ (-47 / 40 : ℝ) * t ^ (-87 / 40 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  convert hd using 1
  · rfl
  · simp only [diagonalFarDifference, id_eq, Pi.add_apply,
      show (-47 / 40 : ℝ) - 1 = -87 / 40 by ring,
      show (-47 / 20 : ℝ) - 1 = -67 / 20 by ring]
    rw [hp]
    ring

theorem diagonalMinusPrimitive_half :
    diagonalMinusPrimitive (1 / 2) = (20 / 47 : ℝ) * (1 / 2 : ℝ) ^ (-47 / 20 : ℝ) := by
  have hp : (1 / 2 : ℝ) ^ (-47 / 20 : ℝ) =
      2 * (1 / 2 : ℝ) ^ (-27 / 20 : ℝ) := by
    calc
      _ = (1 / 2 : ℝ) ^ ((-27 / 20 : ℝ) - 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring
  simp only [diagonalMinusPrimitive, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    show (1 : ℝ) - 2 * (1 / 2) = 0 by ring, mul_zero, zero_mul, sub_zero]
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), hp]
  rw [show (-7 / 40 : ℝ) + -47 / 40 = -27 / 20 by ring]
  ring

theorem diagonalNearBoundary_half_eq_far :
    diagonalNearBoundary (1 / 2) = diagonalFarBoundary (1 / 2) := by
  simp only [diagonalNearBoundary, diagonalFarBoundary, diagonalNearDifference,
    diagonalFarDifference, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    diagonalMinusPrimitive_half]

/-- The true divergent primitive terms cancel at the origin. -/
theorem tendsto_diagonalNearBoundary_zero :
    Tendsto diagonalNearBoundary (𝓝[>] 0) (𝓝 0) := by
  have hdiff : Tendsto (fun t : ℝ ↦ t ^ (-47 / 40 : ℝ) * diagonalNearDifference t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [diagonalNearDifference, mul_one, Real.one_rpow,
      show -(47 / 40 : ℝ) = -47 / 40 by ring] using
        tendsto_rpow_mul_shifted_secondDifference
          (by norm_num : (0 : ℝ) < 47 / 40) (by norm_num : (47 / 40 : ℝ) < 2)
            (by norm_num : (0 : ℝ) < 1)
  let f : ℝ → ℝ := fun t ↦ (40 / 7 : ℝ) * (1 + t) ^ (-87 / 40 : ℝ) +
    (40 / 47 : ℝ) * (1 - t) ^ (-47 / 40 : ℝ) -
      (2160 / 329 : ℝ) * (1 - 2 * t) * (1 - t) ^ (-7 / 40 : ℝ)
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp only [f]
    fun_prop (disch := norm_num)
  have hf₀ : f 0 = 0 := by norm_num [f]
  have hrem := tendsto_rpow_mul_of_hasDerivAt_zero hf.hasDerivAt hf₀
    (by norm_num : (-1 : ℝ) < -7 / 40)
  have h := (hdiff.const_mul (-40 / 47 : ℝ)).add hrem
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards with t
  dsimp only [diagonalNearBoundary, diagonalPlusPrimitive, diagonalMinusPrimitive, f]
  ring

/-- The genuine exterior boundary terms vanish at infinity. -/
theorem tendsto_diagonalFarBoundary_atTop :
    Tendsto diagonalFarBoundary atTop (𝓝 0) := by
  have h₁ : Tendsto (fun t : ℝ ↦ t ^ (-47 / 40 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(47 / 40 : ℝ) = -47 / 40 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 47 / 40)
  have h₂ : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-47 / 40 : ℝ)) atTop (𝓝 0) :=
    h₁.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have h₃ : Tendsto (fun t : ℝ ↦ t ^ (-7 / 40 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(7 / 40 : ℝ) = -7 / 40 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 40)
  have h₄ : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-87 / 40 : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ ↦ (1 + t) ^ (-(87 / 40 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 87 / 40)).comp
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa only [show -(87 / 40 : ℝ) = -87 / 40 by ring] using hh
  have h₅ : Tendsto (fun t : ℝ ↦ t ^ (-47 / 20 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(47 / 20 : ℝ) = -47 / 20 by ring] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 47 / 20)
  have h := (((h₁.const_mul (-40 / 47 : ℝ)).mul ((h₂.add h₁).sub_const 2)).add
    ((h₃.mul h₄).const_mul (40 / 7 : ℝ))).add (h₅.const_mul (20 / 47 : ℝ))
  simp only [mul_zero, zero_add, zero_mul] at h
  apply h.congr'
  filter_upwards with t
  dsimp only [diagonalFarBoundary, diagonalFarDifference, diagonalPlusPrimitive]

end PartialBalayage.Maximal.Square
