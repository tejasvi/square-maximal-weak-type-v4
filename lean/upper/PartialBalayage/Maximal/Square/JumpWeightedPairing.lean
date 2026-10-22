/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpWeightedCompactness
public import PartialBalayage.Maximal.Square.JumpGeneratorPairing
public import PartialBalayage.Linear.WholeSpaceWeakPDE

/-!
# Actual compact physical pairings in the fixed weighted density space

Dividing a genuine compact continuous test by the strictly positive fixed heat
weight gives an actual weighted L² test. Its Hilbert pairing is exactly the
original compact physical-space pairing, so the joint weak limit retains the
original generator equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The original compact test divided by the actual strictly positive Gaussian weight. -/
def jumpWeightedTestFunction (φ : E → ℝ) (x : E) : ℝ := φ x / jumpExhaustionWeight x

theorem continuous_jumpWeightedTestFunction {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (jumpWeightedTestFunction φ) :=
  hφ.div continuous_jumpExhaustionWeight (fun x ↦ (jumpExhaustionWeight_pos x).ne')

theorem hasCompactSupport_jumpWeightedTestFunction {φ : E → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport (jumpWeightedTestFunction φ) := by
  have he : jumpWeightedTestFunction φ = φ * fun x ↦ (jumpExhaustionWeight x)⁻¹ := by
    funext x
    simp only [jumpWeightedTestFunction, div_eq_mul_inv, Pi.mul_apply]
  rw [he]
  exact hs.mul_right

/-- The genuine fixed weighted L² test class. -/
def jumpWeightedTest (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Lp ℝ 2 jumpExhaustionMeasure :=
  ((continuous_jumpWeightedTestFunction hφ).memLp_of_hasCompactSupport
    (hasCompactSupport_jumpWeightedTestFunction hs) (p := (2 : ℝ≥0∞))
    (μ := jumpExhaustionMeasure)).toLp (jumpWeightedTestFunction φ)

theorem jumpWeightedTest_ae (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    (jumpWeightedTest φ hφ hs : E → ℝ) =ᵐ[volume] jumpWeightedTestFunction φ := by
  apply (ae_jumpExhaustionMeasure_iff _).mp
  exact MemLp.coeFn_toLp _

/-- Any actual weighted density has a genuinely integrable original compact pairing. -/
theorem integrable_weightedDensity_mul_compactTest (ν : Lp ℝ 2 jumpExhaustionMeasure)
    (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x : E ↦ ν x * φ x) volume := by
  have hi : Integrable (fun x : E ↦ ν x * jumpWeightedTestFunction φ x)
      jumpExhaustionMeasure := by
    have hij : Integrable (fun x : E ↦ ν x * jumpWeightedTest φ hφ hs x)
        jumpExhaustionMeasure :=
      (Lp.memLp ν).integrable_mul (Lp.memLp (jumpWeightedTest φ hφ hs))
    apply hij.congr
    filter_upwards [(ae_jumpExhaustionMeasure_iff _).mpr (jumpWeightedTest_ae φ hφ hs)]
      with x hx
    rw [hx]
  unfold jumpExhaustionMeasure at hi
  rw [integrable_withDensity_iff_integrable_smul'
    continuous_jumpExhaustionWeight.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))] at hi
  apply hi.congr
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (jumpExhaustionWeight_pos x).le, smul_eq_mul]
  unfold jumpWeightedTestFunction
  field_simp [(jumpExhaustionWeight_pos x).ne']
  exact mul_comm _ _

/-- The true weighted Hilbert pairing equals the original physical compact pairing exactly. -/
theorem inner_jumpWeightedTest_eq_integral (ν : Lp ℝ 2 jumpExhaustionMeasure)
    (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    ⟪ν, jumpWeightedTest φ hφ hs⟫ = ∫ x : E, ν x * φ x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x : E, ν x * jumpWeightedTestFunction φ x ∂jumpExhaustionMeasure := by
      apply integral_congr_ae
      filter_upwards [(ae_jumpExhaustionMeasure_iff _).mpr (jumpWeightedTest_ae φ hφ hs)]
        with x hx
      simp only [Real.inner_apply, hx]
    _ = _ := by
      unfold jumpExhaustionMeasure
      rw [integral_withDensity_eq_integral_toReal_smul
        continuous_jumpExhaustionWeight.measurable.ennreal_ofReal
        (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (jumpExhaustionWeight_pos x).le, smul_eq_mul]
      unfold jumpWeightedTestFunction
      field_simp [(jumpExhaustionWeight_pos x).ne']

end PartialBalayage.Maximal.Square
