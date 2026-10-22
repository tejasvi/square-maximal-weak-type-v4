/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 and spline scale 32 instead of 16 (factor 32^(47/40)). -/
module

public import PartialBalayage.Maximal.Square.SplineGenerator

/-!
# True scaling and scalar multiplication of the actual spline generator

These identities concern the genuine spatial stable integrals. They supply the exact
scale factor for the certificate's tensor spline terms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

theorem stableGeneratorIntegral_const_mul (α c : ℝ) (φ : ℝ → ℝ) :
    PartialBalayage.Linear.stableGeneratorIntegral α (fun t ↦ c * φ t) =
      c * PartialBalayage.Linear.stableGeneratorIntegral α φ := by
  have heq : (fun t : ℝ ↦ t ^ (-1 - α) •
      PartialBalayage.Linear.stableSecondDifference (fun t ↦ c * φ t) t) =
      fun t : ℝ ↦ c * (t ^ (-1 - α) • PartialBalayage.Linear.stableSecondDifference φ t) := by
    funext t
    simp only [PartialBalayage.Linear.stableSecondDifference, smul_eq_mul]
    ring
  unfold PartialBalayage.Linear.stableGeneratorIntegral
  rw [heq, integral_const_mul]

/-- An actual positive spatial scale contributes the exact order `a^(47/40)`. -/
theorem stableGeneratorIntegral_cubicSpline_scaled (x : ℝ) {a : ℝ} (ha : 0 < a) :
    PartialBalayage.Linear.stableGeneratorIntegral (47 / 40 : ℝ)
      (fun t : ℝ ↦ cubicSpline (x + a * t)) =
        a ^ (47 / 40 : ℝ) * ((2560000 / 792561 : ℝ) * splineGeneratorPower x) := by
  have heq : (fun t : ℝ ↦ cubicSpline (x + a * t)) =
      fun t : ℝ ↦ cubicSpline (x + t / (1 / a)) := by
    funext t
    congr 1
    field_simp
  rw [heq, PartialBalayage.Linear.stableGeneratorIntegral_dilate (47 / 40 : ℝ)
    (fun t : ℝ ↦ cubicSpline (x + t)) (one_div_pos.mpr ha),
    stableGeneratorIntegral_cubicSpline, smul_eq_mul]
  congr 1
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

/-- The certificate's actual thirty-two-fold spline scale, with the exact normalization. -/
theorem stableGeneratorIntegral_cubicSpline_thirtyTwo (x : ℝ) :
    PartialBalayage.Linear.stableGeneratorIntegral (47 / 40 : ℝ)
      (fun t : ℝ ↦ cubicSpline (x + 32 * t)) =
        (32 : ℝ) ^ (47 / 40 : ℝ) * ((2560000 / 792561 : ℝ) * splineGeneratorPower x) :=
  stableGeneratorIntegral_cubicSpline_scaled x (by norm_num : (0 : ℝ) < 32)

end PartialBalayage.Maximal.Square
