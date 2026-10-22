/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondAngularIntegral
public import PartialBalayage.Maximal.Square.SplineGeneratorScaling

/-!
# True homogeneity and diagonal reduction of the diamond generator

An actual change of variables in each convergent coordinate integral gives order `−2α`.
Together with genuine angular constancy this reduces its normalization to one fixed diagonal.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

theorem diamondCoordinateProfile_scale {s v : ℝ} (hs : 0 < s) (hv : 0 < v)
    (α u t : ℝ) :
    diamondCoordinateProfile α (s * u) (s * v) t =
      s ^ (-α) * diamondCoordinateProfile α u v (t / s) := by
  have he : s * u + t = s * (u + t / s) := by field_simp
  rw [diamondCoordinateProfile, he, abs_mul, abs_of_pos hs, ← mul_add,
    Real.mul_rpow hs.le (by positivity)]
  rfl

/-- Actual positive dilation gives the exact order of each original coordinate integral. -/
theorem diamondCoordinateIntegral_scale {s v : ℝ} (hs : 0 < s) (hv : 0 < v)
    (α u : ℝ) :
    diamondCoordinateIntegral α (s * u) (s * v) =
      s ^ (-2 * α) * diamondCoordinateIntegral α u v := by
  have he : diamondCoordinateProfile α (s * u) (s * v) =
      fun t ↦ s ^ (-α) * diamondCoordinateProfile α u v (t / s) := by
    funext t
    exact diamondCoordinateProfile_scale hs hv α u t
  unfold diamondCoordinateIntegral
  rw [he, stableGeneratorIntegral_const_mul, stableGeneratorIntegral_dilate α _ hs,
    smul_eq_mul, ← mul_assoc, ← Real.rpow_add hs]
  congr 2
  ring

/-- The actual paired generator is homogeneous of order `−2α`. -/
theorem diamondPairedGenerator_scale {s u v : ℝ} (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (α : ℝ) :
    diamondPairedGenerator α (s * u) (s * v) =
      s ^ (-2 * α) * diamondPairedGenerator α u v := by
  rw [diamondPairedGenerator, diamondCoordinateIntegral_scale hs hv,
    diamondCoordinateIntegral_scale hs hu, diamondPairedGenerator, mul_add]

/-- The genuine paired singular integral reduces to its fixed unit-radius diagonal. -/
theorem diamondPairedGenerator_eq_diagonal {α u v : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hu : 0 < u) (hv : 0 < v) :
    diamondPairedGenerator α u v = (u + v) ^ (-2 * α) *
      diamondPairedGenerator α (1 / 2) (1 / 2) := by
  have hr : 0 < u + v := add_pos hu hv
  have h := diamondPairedGenerator_angular_constant hα0 hα2 hu
    (by linarith : u < u + v) (by positivity : 0 < (u + v) / 2)
    (by linarith : (u + v) / 2 < u + v)
  have he₁ : u + v - u = v := by ring
  have he₂ : u + v - (u + v) / 2 = (u + v) / 2 := by ring
  rw [he₁, he₂] at h
  rw [h, show (u + v) / 2 = (u + v) * (1 / 2) by ring,
    diamondPairedGenerator_scale hr (by norm_num) (by norm_num)]

end PartialBalayage.Maximal.Square
