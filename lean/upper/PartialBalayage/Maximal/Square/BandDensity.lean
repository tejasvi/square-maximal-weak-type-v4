/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandProfile
public import PartialBalayage.Maximal.Square.KernelSourceInteriorFormula

/-!
# The source density outside the diamond

At a point with positive coordinates outside the diamond the radial generator is the sum of the
two exterior line integrals, so the source density is
`sN * (c * (J(u, v) + J(v, u)) + F * P(32 u, 32 v))`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The explicit exterior source density in the unit-grid coordinates. -/
def bandDensity (u v : ℝ) : ℝ :=
  radialCoefficient * (bandLine (u / 32) (v / 32) + bandLine (v / 32) (u / 32)) +
    splineGeneratorFactor * splineGeneratorCorrectionPower u v

/-- The actual full generator outside the diamond. -/
theorem kernelGeneratorAt_eq_band {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : supportRadius < u + v) :
    kernelGeneratorAt (47 / 40) u v = stableNormalization (47 / 40) *
      (radialCoefficient * (bandLine u v + bandLine v u) +
        splineGeneratorFactor * splineGeneratorCorrectionPower (32 * u) (32 * v)) := by
  let x : E := WithLp.toLp 2 ![u, v]
  have hx₀ : x 0 = u := rfl
  have hx₁ : x 1 = v := rfl
  have hrx : supportRadius < diamondRadius (x 0) (x 1) := by
    simpa only [hx₀, hx₁, diamondRadius, abs_of_pos hu, abs_of_pos hv] using hr
  have he := coordinateStableGenerator_euclideanKernel_eq_density
    (by rw [hx₀]; exact hu.ne') (by rw [hx₁]; exact hv.ne') (ne_of_gt hrx)
  rw [coordinateStableGenerator_euclideanKernel_eq_at, hx₀, hx₁,
    squareGeneratorDensity_eq_formula] at he
  rw [he]
  have hrad : radialGeneratorDensity x = radialCoefficient * stableNormalization (47 / 40) *
      (bandLine u v + bandLine v u) := by
    unfold radialGeneratorDensity coordinateStableGenerator
    rw [Fin.sum_univ_two, coordinateLine_diamondTruncatedPower_zero,
      coordinateLine_diamondTruncatedPower_one, hx₀, hx₁, abs_of_pos hu, abs_of_pos hv,
      stableGeneratorIntegral_profile_eq_bandLine' hu hv hr,
      stableGeneratorIntegral_profile_eq_bandLine' hv hu (by linarith)]
    ring
  rw [hrad, hx₀, hx₁]
  ring

/-- The thirty-two-fold spatial scale of the exterior generator. -/
theorem kernelGeneratorAt_scaled_eq_band {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : 264 / 5 < u + v) :
    kernelGeneratorAt (47 / 40) (u / 32) (v / 32) =
      stableNormalization (47 / 40) * bandDensity u v := by
  rw [kernelGeneratorAt_eq_band (by positivity) (by positivity)
    (by norm_num only [supportRadius]; linarith)]
  unfold bandDensity
  rw [show 32 * (u / 32) = u by ring, show 32 * (v / 32) = v by ring]

end PartialBalayage.Maximal.Square
