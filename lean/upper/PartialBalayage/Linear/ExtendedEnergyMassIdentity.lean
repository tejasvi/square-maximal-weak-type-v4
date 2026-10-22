/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WeakDirichletEnergy
public import PartialBalayage.Linear.L2DomainRestriction
public import PartialBalayage.Linear.ZeroExtensionMass

/-!
# Genuine finite obstacle balances in whole-space coordinates

The actual whole-space observation of an extended vector state is the genuine zero extension
of its finite-domain observation. Its mass is unchanged, and its pairing with the global
input equals the finite pairing with the actually restricted input. Consequently the true
finite energy-mass balance is a balance against one fixed whole-space linear functional,
as required for weak lower semicontinuity at the actual joint limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

section Pairing

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure X} {Ω : Set X}

omit [CompleteSpace E] in
/-- Genuine restriction is adjoint to zero extension in the actual L² pairing. -/
theorem inner_global_zeroExtendL2 (hΩ : MeasurableSet Ω)
    (f : Lp E 2 μ) (g : Lp E 2 (μ.restrict Ω)) :
    ⟪f, zeroExtendL2 hΩ g⟫ = ⟪restrictL2CLM Ω f, g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, Ω.indicator (fun y ↦ ⟪f y, g y⟫) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [zeroExtendL2_ae hΩ g] with x hx
      rw [hx]
      by_cases hmem : x ∈ Ω <;> simp [hmem]
    _ = ∫ x, ⟪f x, g x⟫ ∂(μ.restrict Ω) := integral_indicator hΩ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restrictL2CLM_ae Ω f] with x hx
      rw [hx]

end Pairing

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The true whole-space vector value commutes with actual Sobolev zero extension. -/
theorem globalVectorDirichletObservation_zeroExtend (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) :
    globalVectorDirichletObservation (zeroExtendVectorDirichletState hΩ U) =
      zeroExtendL2 hΩ (vectorDirichletObservation Ω U) := by
  have hobs : vectorDirichletObservation univ (zeroExtendVectorDirichletState hΩ U)
      =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun j : Fin m ↦
        (zeroExtendH01 hΩ (U j) : H1amb univ) 0 x) := by
    have ha := vectorDirichletObservation_ae univ (zeroExtendVectorDirichletState hΩ U)
    simp only [Measure.restrict_univ] at ha
    filter_upwards [ha] with x hx
    simpa only [zeroExtendVectorDirichletState_apply] using hx
  have hcoords : ∀ᵐ x ∂volume, ∀ j : Fin m,
      (zeroExtendH01 hΩ (U j) : H1amb univ) 0 x =
        Ω.indicator ((U j : H1amb Ω) 0) x := by
    apply ae_all_iff.mpr
    intro j
    have hz := zeroExtendUnivL2CLM_ae hΩ ((U j : H1amb Ω) 0)
    simp only [Measure.restrict_univ] at hz
    filter_upwards [hz] with x hx
    change zeroExtendUnivL2CLM hΩ ((U j : H1amb Ω) 0) x = _
    exact hx
  have hfinite : ∀ᵐ x ∂volume, x ∈ Ω → vectorDirichletObservation Ω U x =
      WithLp.toLp 2 (fun j : Fin m ↦ (U j : H1amb Ω) 0 x) :=
    (ae_restrict_iff' hΩ).mp (vectorDirichletObservation_ae Ω U)
  apply Lp.ext
  filter_upwards [globalVectorDirichletObservation_ae (zeroExtendVectorDirichletState hΩ U),
    hobs, hcoords, hfinite, zeroExtendL2_ae hΩ (vectorDirichletObservation Ω U)]
      with x hg ho hc hf he
  rw [hg, ho, he]
  by_cases hmem : x ∈ Ω
  · rw [Set.indicator_of_mem hmem, hf hmem]
    ext j
    exact (hc j).trans (Set.indicator_of_mem hmem _)
  · rw [Set.indicator_of_notMem hmem]
    ext j
    exact (hc j).trans (Set.indicator_of_notMem hmem _)

/-- Genuine whole-space value mass equals the actual finite-domain value mass. -/
theorem integral_norm_globalObservation_zeroExtend (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) :
    (∫ x, ‖globalVectorDirichletObservation (zeroExtendVectorDirichletState hΩ U) x‖) =
      ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) := by
  rw [globalVectorDirichletObservation_zeroExtend, integral_norm_zeroExtendL2]

/-- The actual extended energy-mass balance pairs against the fixed global input. -/
theorem extended_vectorDirichlet_energy_mass_identity (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) {κ : ℝ}
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) -
        vectorDirichletCoordinate Ω j ν, (W : H1amb Ω) 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    vectorDirichletEnergy (zeroExtendVectorDirichletState hΩ U) +
      κ * ∫ x, ‖globalVectorDirichletObservation (zeroExtendVectorDirichletState hΩ U) x‖ =
        ⟪f, globalVectorDirichletObservation (zeroExtendVectorDirichletState hΩ U)⟫ := by
  rw [vectorDirichletEnergy_zeroExtend, integral_norm_globalObservation_zeroExtend,
    globalVectorDirichletObservation_zeroExtend, inner_global_zeroExtendL2]
  exact vectorDirichlet_energy_mass_identity U (restrictL2CLM Ω f) ν hpde halign

end PartialBalayage.Linear
