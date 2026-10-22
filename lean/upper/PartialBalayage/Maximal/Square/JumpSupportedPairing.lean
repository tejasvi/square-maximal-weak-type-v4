/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpCutoffApproximation

/-!
# Genuine compactly supported energy tests in the weighted density dual

The actual inverse Gaussian weight is bounded on every compact set. Thus
every genuinely supported volume L² value gives a true weighted L² dual test,
without assuming continuity of the energy state's representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Dividing an actual compactly supported L² function by the genuine heat weight
produces a true weighted L² function. -/
theorem memLp_jumpWeightedSupportedTest (u : Lp ℝ 2 (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    MemLp (jumpWeightedTestFunction (u : E → ℝ)) 2 jumpExhaustionMeasure := by
  have hc : Continuous (fun x : E ↦ (jumpExhaustionWeight x)⁻¹) :=
    continuous_jumpExhaustionWeight.inv₀ (fun x ↦ (jumpExhaustionWeight_pos x).ne')
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  have hm : AEStronglyMeasurable (jumpWeightedTestFunction (u : E → ℝ)) volume := by
    unfold jumpWeightedTestFunction
    simp only [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable u).mul hc.aestronglyMeasurable
  have hv : MemLp (jumpWeightedTestFunction (u : E → ℝ)) 2 volume := by
    apply (Lp.memLp u).of_le_mul hm (c := max C 0)
    filter_upwards [hu] with x hx
    unfold jumpWeightedTestFunction
    by_cases hxs : x ∈ S
    · rw [div_eq_mul_inv, norm_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left ((hC x hxs).trans (le_max_left C 0)) (norm_nonneg (u x))
    · rw [hx hxs, zero_div, norm_zero]
      positivity
  exact hv.of_measure_le_smul ENNReal.ofReal_ne_top jumpExhaustionMeasure_le_smul_volume

/-- The actual weighted dual class of a genuinely compactly supported volume L² value. -/
def jumpWeightedSupportedTest (u : Lp ℝ 2 (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    Lp ℝ 2 jumpExhaustionMeasure :=
  (memLp_jumpWeightedSupportedTest u hS hu).toLp (jumpWeightedTestFunction (u : E → ℝ))

theorem jumpWeightedSupportedTest_ae (u : Lp ℝ 2 (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    (jumpWeightedSupportedTest u hS hu : E → ℝ) =ᵐ[volume]
      jumpWeightedTestFunction (u : E → ℝ) := by
  apply (ae_jumpExhaustionMeasure_iff _).mp
  exact (memLp_jumpWeightedSupportedTest u hS hu).coeFn_toLp

/-- Genuine weighted densities pair integrably with every supported energy value. -/
theorem integrable_weightedDensity_mul_supportedL2 (ν : Lp ℝ 2 jumpExhaustionMeasure)
    (u : Lp ℝ 2 (volume : Measure E)) {S : Set E} (hS : IsCompact S)
    (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    Integrable (fun x : E ↦ ν x * u x) volume := by
  have hi : Integrable (fun x : E ↦ ν x * jumpWeightedTestFunction (u : E → ℝ) x)
      jumpExhaustionMeasure := by
    have hij := (Lp.memLp ν).integrable_mul (Lp.memLp (jumpWeightedSupportedTest u hS hu))
    apply hij.congr
    filter_upwards [(ae_jumpExhaustionMeasure_iff _).mpr
      (jumpWeightedSupportedTest_ae u hS hu)] with x hx
    simp only [Pi.mul_apply, hx]
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

/-- The genuine weighted dual pairing is the original physical supported pairing. -/
theorem inner_jumpWeightedSupportedTest_eq_integral (ν : Lp ℝ 2 jumpExhaustionMeasure)
    (u : Lp ℝ 2 (volume : Measure E)) {S : Set E} (hS : IsCompact S)
    (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    ⟪ν, jumpWeightedSupportedTest u hS hu⟫ = ∫ x : E, ν x * u x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x : E, ν x * jumpWeightedTestFunction (u : E → ℝ) x
        ∂jumpExhaustionMeasure := by
      apply integral_congr_ae
      filter_upwards [(ae_jumpExhaustionMeasure_iff _).mpr
        (jumpWeightedSupportedTest_ae u hS hu)] with x hx
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
