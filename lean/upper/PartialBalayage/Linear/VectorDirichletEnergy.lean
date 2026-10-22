/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorBalayageFinite

/-!
# Energy and mass of the actual vector obstacle state

The genuine observation has exactly the sum of the scalar value energies. Testing the actual
weak equation with each state coordinate, and using cap alignment, gives the exact Dirichlet
energy plus cap-weighted mass identity. The resulting nonpositive functional estimate does
not use a domain-dependent Poincaré constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Taking a coordinate of the actual observation recovers that scalar value class. -/
theorem vectorDirichletCoordinate_observation (U : VectorDirichletState Ω m) (j : Fin m) :
    vectorDirichletCoordinate Ω j (vectorDirichletObservation Ω U) =
      (U j : H1amb Ω) 0 := by
  apply Lp.ext
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL
    (p := 2) (vectorDirichletObservation Ω U), vectorDirichletObservation_ae Ω U]
      with x hc hu
  change vectorDirichletCoordinate Ω j (vectorDirichletObservation Ω U) x =
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j)
      (vectorDirichletObservation Ω U x) at hc
  rw [hc, hu]
  rfl

/-- The actual observation is adjoint to the family of scalar coordinate maps. -/
theorem inner_vectorDirichletObservation (f : VectorDirichletL2 Ω m)
    (U : VectorDirichletState Ω m) :
    ⟪f, vectorDirichletObservation Ω U⟫ =
      ∑ j : Fin m, ⟪vectorDirichletCoordinate Ω j f, (U j : H1amb Ω) 0⟫ := by
  rw [vectorDirichletObservation_apply, inner_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ inner_vectorDirichletInjection_compLp Ω j f _)

/-- The norm of the actual vector value is exactly its coordinate energy sum. -/
theorem norm_vectorDirichletObservation_sq (U : VectorDirichletState Ω m) :
    ‖vectorDirichletObservation Ω U‖ ^ 2 =
      ∑ j : Fin m, ‖(U j : H1amb Ω) 0‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vectorDirichletObservation]
  simp only [vectorDirichletCoordinate_observation, real_inner_self_eq_norm_sq]

/-- The true nonnegative Dirichlet energy of the vector state. -/
def vectorDirichletEnergy (U : VectorDirichletState Ω m) : ℝ :=
  ∑ j : Fin m, laplaceBilin Ω (U j) (U j)

theorem vectorDirichletEnergy_nonneg (U : VectorDirichletState Ω m) :
    0 ≤ vectorDirichletEnergy U := by
  unfold vectorDirichletEnergy
  apply Finset.sum_nonneg
  intro j _
  rw [laplaceBilin_self]
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The actual Sobolev product norm is value energy plus Dirichlet energy. -/
theorem norm_vectorDirichletState_sq (U : VectorDirichletState Ω m) :
    ‖U‖ ^ 2 = ‖vectorDirichletObservation Ω U‖ ^ 2 + vectorDirichletEnergy U := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : Fin m, ‖U j‖ ^ 2) =
        ∑ j : Fin m, (‖(U j : H1amb Ω) 0‖ ^ 2 + laplaceBilin Ω (U j) (U j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change ‖(U j : H1amb Ω)‖ ^ 2 = _
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, laplaceBilin_self]
    _ = _ := by
      rw [Finset.sum_add_distrib, norm_vectorDirichletObservation_sq]
      rfl

/-- Testing the actual weak equation with the state yields its true energy pairing. -/
theorem vectorDirichletEnergy_eq_pairing (U : VectorDirichletState Ω m)
    (f ν : VectorDirichletL2 Ω m)
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
        (W : H1amb Ω) 0⟫) :
    vectorDirichletEnergy U = ⟪f - ν, vectorDirichletObservation Ω U⟫ := by
  rw [inner_vectorDirichletObservation]
  unfold vectorDirichletEnergy
  apply Finset.sum_congr rfl
  intro j _
  simpa only [map_sub] using hpde j (U j)

/-- Cap alignment identifies the density pairing with the full value mass. -/
theorem inner_density_observation_of_alignment (U : VectorDirichletState Ω m)
    (ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    ⟪ν, vectorDirichletObservation Ω U⟫ =
      κ * ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [halign] with x hx
  by_cases hu : vectorDirichletObservation Ω U x = 0
  · simp [hu]
  · rw [hx hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hu]

/-- The actual weak equation and cap alignment give the exact energy-mass balance. -/
theorem vectorDirichlet_energy_mass_identity (U : VectorDirichletState Ω m)
    (f ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
        (W : H1amb Ω) 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    vectorDirichletEnergy U +
      κ * ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) =
        ⟪f, vectorDirichletObservation Ω U⟫ := by
  rw [vectorDirichletEnergy_eq_pairing U f ν hpde, inner_sub_left,
    inner_density_observation_of_alignment U ν halign]
  ring

/-- The actual state lies in the nonpositive obstacle functional sublevel. -/
theorem vectorDirichlet_functional_sublevel (U : VectorDirichletState Ω m)
    (f ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
        (W : H1amb Ω) 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    vectorDirichletEnergy U / 2 +
      κ * ∫ x, ‖vectorDirichletObservation Ω U x‖ ∂(volume.restrict Ω) ≤
        ‖f‖ * ‖vectorDirichletObservation Ω U‖ := by
  have heq := vectorDirichlet_energy_mass_identity U f ν hpde halign
  have hb := real_inner_le_norm f (vectorDirichletObservation Ω U)
  linarith [vectorDirichletEnergy_nonneg U]

end PartialBalayage.Linear
