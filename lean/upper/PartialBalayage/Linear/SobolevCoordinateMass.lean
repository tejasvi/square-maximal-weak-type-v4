/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorSobolevExtension
public import PartialBalayage.Linear.SobolevDistributionGradient
public import PartialBalayage.Linear.ZeroExtensionMass

/-!
# Actual scalar coordinate masses of vector Sobolev states

The complex global value of a zero-extended genuine Dirichlet state is the complexification
of its domain indicator. Its mass is exactly the restricted scalar value mass, which is
bounded by the full vector value mass. These are actual represented functions used in the
Fourier interpolation estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The genuine complex extended coordinate is the domain indicator almost everywhere. -/
theorem complexGlobalGraphCoordinate_zeroExtend_ae (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    complexGlobalGraphCoordinateCLM 0
      (zeroExtendH01 hΩ U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) =ᵐ[volume]
      fun x ↦ ((Ω.indicator ((U : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ) := by
  have hz : zeroExtendUnivL2CLM hΩ ((U : H1amb Ω) 0) =ᵐ[volume]
      Ω.indicator ((U : H1amb Ω) 0) := by
    simpa only [Measure.restrict_univ] using
      zeroExtendUnivL2CLM_ae hΩ ((U : H1amb Ω) 0)
  filter_upwards [complexGlobalGraphCoordinateCLM_ae 0
    (zeroExtendH01 hΩ U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))), hz] with x hc hx
  change complexGlobalGraphCoordinateCLM 0
    (zeroExtendH01 hΩ U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) x =
    (zeroExtendUnivL2CLM hΩ ((U : H1amb Ω) 0) x : ℂ) at hc
  rw [hc, hx]

/-- The actual scalar mass is unchanged by complexification and zero extension. -/
theorem integral_norm_complexGlobalGraphCoordinate_zeroExtend (hΩ : MeasurableSet Ω)
    (U : H01 Ω) :
    (∫ x, ‖complexGlobalGraphCoordinateCLM 0
      (zeroExtendH01 hΩ U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) x‖) =
      ∫ x, ‖(U : H1amb Ω) 0 x‖ ∂(volume.restrict Ω) := by
  calc
    _ = ∫ x, ‖Ω.indicator ((U : H1amb Ω) 0) x‖ := by
      apply integral_congr_ae
      filter_upwards [complexGlobalGraphCoordinate_zeroExtend_ae hΩ U] with x hx
      rw [hx, Complex.norm_real, Real.norm_eq_abs]
    _ = ∫ x, Ω.indicator (fun y ↦ ‖(U : H1amb Ω) 0 y‖) x := by
      congr 1
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    _ = _ := integral_indicator hΩ

/-- A restricted integrable value gives an actual integrable complex whole-space coordinate. -/
theorem integrable_complexGlobalGraphCoordinate_zeroExtend (hΩ : MeasurableSet Ω)
    (U : H01 Ω) (hU : Integrable ((U : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      (volume.restrict Ω)) :
    Integrable (complexGlobalGraphCoordinateCLM 0
      (zeroExtendH01 hΩ U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) := by
  have hi := ((integrable_indicator_iff hΩ).mpr hU).norm
  apply hi.mono' (Lp.aestronglyMeasurable _) ?_
  filter_upwards [complexGlobalGraphCoordinate_zeroExtend_ae hΩ U] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs]

/-- Each actual scalar value is bounded by the norm of the actual vector observation. -/
theorem norm_scalarValue_le_observation_ae (U : VectorDirichletState Ω m) (j : Fin m) :
    ∀ᵐ x ∂(volume.restrict Ω), ‖(U j : H1amb Ω) 0 x‖ ≤
      ‖vectorDirichletObservation Ω U x‖ := by
  filter_upwards [vectorDirichletObservation_ae Ω U] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun k : Fin m ↦ (U k : H1amb Ω) 0 x)) j

/-- The actual scalar coordinate mass is bounded by the full vector mass. -/
theorem integral_norm_scalarValue_le_observation (U : VectorDirichletState Ω m)
    (j : Fin m)
    (hU : Integrable (vectorDirichletObservation Ω U : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin m)) (volume.restrict Ω)) :
    (∫ x, ‖(U j : H1amb Ω) 0 x‖ ∂(volume.restrict Ω)) ≤
      ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) := by
  have hj := hU.norm.mono' (Lp.aestronglyMeasurable _)
    (norm_scalarValue_le_observation_ae U j)
  exact integral_mono_ae hj.norm hU.norm (norm_scalarValue_le_observation_ae U j)

end PartialBalayage.Linear
