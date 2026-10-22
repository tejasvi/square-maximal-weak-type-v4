/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ScalarDirichletInterpolation
public import PartialBalayage.Linear.VectorStateCoercivity

/-!
# Domain-independent bounds for actual finite vector obstacles

The actual scalar Fourier interpolation applies to every coordinate of the genuine finite
Dirichlet state. Its scalar masses are bounded by the full vector mass. The resulting vector
estimate and the true energy-mass balance bound both energy and mass, then the full Sobolev
norm, uniformly over the exhaustion domains. No interpolation or mass conclusion is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Actual finite-domain vector interpolation follows from the scalar Fourier theorem. -/
theorem vectorDirichlet_interpolation (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (U : VectorDirichletState Ω m)
    {R : ℝ} (hR : 0 < R) :
    ‖vectorDirichletObservation Ω U‖ ≤
      ((m : ℝ) + 1) * Real.sqrt ((volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal) *
        (∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω)) +
      Real.sqrt (R ^ (-2 : ℝ) / (2 * Real.pi) ^ 2) * Real.sqrt (vectorDirichletEnergy U) := by
  have hM : 0 ≤ ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) :=
    integral_nonneg (fun _ ↦ norm_nonneg _)
  apply norm_observation_le_of_coordinate_bounds U hM ENNReal.toReal_nonneg
    (div_nonneg (Real.rpow_nonneg hR.le _) (sq_nonneg _))
  intro j
  have hs := scalarDirichlet_interpolation hΩ (U j)
    ((Lp.memLp ((U j : H1amb Ω) 0)).integrable one_le_two) hR
  have hm := integral_norm_scalarValue_le_observation U j
    ((Lp.memLp (vectorDirichletObservation Ω U)).integrable one_le_two)
  have hm0 : 0 ≤ ∫ x, ‖(U j : H1amb Ω) 0 x‖ ∂(volume.restrict Ω) :=
    integral_nonneg (fun _ ↦ norm_nonneg _)
  have hsq := sq_le_sq₀ hm0 hM |>.mpr hm
  have hprod := mul_le_mul_of_nonneg_left hsq
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal_nonneg
  exact hs.trans (by nlinarith)

/-- The actual weak equation and alignment yield quantitative uniform energy and mass bounds. -/
theorem vectorDirichlet_uniform_energy_mass_bounds (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (U : VectorDirichletState Ω m)
    (f ν : VectorDirichletL2 Ω m) {κ F R : ℝ} (hκ : 0 < κ) (hF : 0 ≤ F)
    (hf : ‖f‖ ≤ F) (hR : 0 < R)
    (hsmall : F * (((m : ℝ) + 1) *
      Real.sqrt ((volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal)) ≤ κ / 2)
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
        (W : H1amb Ω) 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    vectorDirichletEnergy U ≤ 4 * F ^ 2 * (R ^ (-2 : ℝ) / (2 * Real.pi) ^ 2) ∧
      (∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω)) ≤
        2 * F ^ 2 * (R ^ (-2 : ℝ) / (2 * Real.pi) ^ 2) / κ := by
  apply obstacle_sublevel_bounds_of_interpolation
    (integral_nonneg (fun _ ↦ norm_nonneg _))
    (div_nonneg (Real.rpow_nonneg hR.le _) (sq_nonneg _))
    (vectorDirichletEnergy_nonneg U) hκ hF hsmall
    (vectorDirichlet_interpolation hΩ U hR)
  exact (vectorDirichlet_functional_sublevel U f ν hpde halign).trans
    (mul_le_mul_of_nonneg_right hf (norm_nonneg (vectorDirichletObservation Ω U)))

/-- A single finite constant bounds the true states on every finite domain. -/
theorem exists_uniform_vectorDirichlet_state_bound
    (hn : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))
    {κ F : ℝ} (hκ : 0 < κ) (hF : 0 ≤ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Set (EuclideanSpace ℝ (Fin d))) (_hΩ : MeasurableSet Ω),
      volume Ω ≠ ⊤ → ∀ (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m),
      ‖f‖ ≤ F →
      (∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
          (W : H1amb Ω) 0⟫) →
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
          vectorDirichletObservation Ω U x) → ‖U‖ ≤ B := by
  obtain ⟨R, hR, hsmall⟩ := exists_small_fourier_radius
    (X := EuclideanSpace ℝ (Fin d)) hn hκ
      (mul_nonneg hF (by positivity : 0 ≤ (m : ℝ) + 1))
  let V := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal
  let D := R ^ (-2 : ℝ) / (2 * Real.pi) ^ 2
  let A := ((m : ℝ) + 1) * Real.sqrt V
  let Em := 4 * F ^ 2 * D
  let Mm := 2 * F ^ 2 * D / κ
  have hD : 0 ≤ D := div_nonneg (Real.rpow_nonneg hR.le _) (sq_nonneg _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMm : 0 ≤ Mm := div_nonneg (by dsimp [D]; positivity) hκ.le
  refine ⟨A * Mm + (Real.sqrt D + 1) * Real.sqrt Em, by positivity, ?_⟩
  intro Ω hΩ hvol U f ν hf hpde halign
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hvol
  have hsm : F * A ≤ κ / 2 := by simpa only [A, V, mul_assoc] using hsmall
  obtain ⟨hE, hM⟩ := vectorDirichlet_uniform_energy_mass_bounds hΩ U f ν
    hκ hF hf hR hsm hpde halign
  change vectorDirichletEnergy U ≤ Em at hE
  change (∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω)) ≤ Mm at hM
  have hsqrt := Real.sqrt_le_sqrt hE
  have hi := vectorDirichlet_interpolation hΩ U hR
  change ‖vectorDirichletObservation Ω U‖ ≤ A *
    (∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω)) +
      Real.sqrt D * Real.sqrt (vectorDirichletEnergy U) at hi
  have hm := mul_le_mul_of_nonneg_left hM hA
  have he := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg D)
  have hu := norm_vectorState_le_value_add_sqrt_energy U
  nlinarith

end PartialBalayage.Linear
