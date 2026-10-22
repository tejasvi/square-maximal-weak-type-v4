/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalCutoffZeroSet
public import PartialBalayage.Linear.VectorBalayageFinite
public import PartialBalayage.Linear.VectorActiveMass

/-!
# Genuine inactive-set locality and full mass contraction for vector Dirichlet obstacles

Interior second-order locality of the actual scalar weak equations identifies the capped
density with the input on the vector state's inactive set. The already proved active-input
comparison therefore gives full mass contraction for the actual finite-domain obstacle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- In the actual vector weak PDE, the residual vanishes on the vector value zero set. -/
theorem ae_vector_density_eq_input_on_inactive_of_weak_equation (hΩ : IsOpen Ω)
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω)
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, W.val 0⟫) :
    ∀ᵐ x ∂(volume.restrict Ω), sobolevVectorValue U x = 0 →
      l2VectorValue ν x = l2VectorValue f x := by
  have hzero (j : Fin m) : ∀ᵐ x ∂(volume.restrict Ω),
      (U j).val 0 x = 0 → (f j - ν j) x = 0 :=
    ae_forcing_eq_zero_on_value_zero_of_weak_laplacian hΩ (U j) (f j - ν j)
      (fun W ↦ by simpa only [l2Functional_apply] using hpde j W)
  have hz := ae_all_iff.mpr hzero
  have hsub := ae_all_iff.mpr (fun j : Fin m ↦ Lp.coeFn_sub (f j) (ν j))
  filter_upwards [hz, hsub] with x hx hdiff
  intro hu
  ext j
  have huj : (U j).val 0 x = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) hu
    simpa only [sobolevVectorValue, PiLp.toLp_apply, PiLp.zero_apply] using h
  have hj := hx j huj
  rw [hdiff j] at hj
  exact (sub_eq_zero.mp hj).symm

/-- Actual vector weak equations, cap alignment, and saturation imply full density mass
contraction; inactive-set locality is derived from the PDE rather than assumed. -/
theorem integral_norm_density_le_of_vector_weak_equation (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ}
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, W.val 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖)
    (hsaturation : ∀ᵐ x ∂(volume.restrict Ω),
      sobolevVectorValue U x ≠ 0 → ‖l2VectorValue ν x‖ = κ) :
    (∫ x, ‖l2VectorValue ν x‖ ∂(volume.restrict Ω)) ≤
      ∫ x, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) :=
  integral_norm_density_le_of_vector_weak_equation_and_locality U f ν hpde hpair hsaturation
    (ae_vector_density_eq_input_on_inactive_of_weak_equation hΩ U f ν hpde)

/-- The actual vector observation's inactive set has density equal to input almost everywhere. -/
theorem ae_vectorDirichlet_density_eq_input_on_inactive (hΩ : IsOpen Ω)
    (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m)
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫) :
    ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x = 0 → ν x = f x := by
  have hlocal := ae_vector_density_eq_input_on_inactive_of_weak_equation hΩ (fun j ↦ U j)
    (fun j ↦ vectorDirichletCoordinate Ω j f) (fun j ↦ vectorDirichletCoordinate Ω j ν) hpde
  filter_upwards [hlocal, vectorDirichletObservation_ae Ω U,
    l2VectorValue_vectorDirichletCoordinate_ae Ω f,
    l2VectorValue_vectorDirichletCoordinate_ae Ω ν] with x hx hu hf hν
  intro hz
  change vectorDirichletObservation Ω U x = sobolevVectorValue (fun j ↦ U j) x at hu
  exact hν.symm.trans ((hx (hu.symm.trans hz)).trans hf)

/-- Full mass contraction for the actual vector obstacle follows from its actual PDE and
alignment, with genuine interior locality discharged. -/
theorem integral_norm_density_le_of_vectorDirichlet (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x)
    (hsat : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) :
    (∫ x, ‖ν x‖ ∂(volume.restrict Ω)) ≤ ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have hs : ∀ᵐ x ∂(volume.restrict Ω), sobolevVectorValue (fun j ↦ U j) x ≠ 0 →
      ‖l2VectorValue (fun j ↦ vectorDirichletCoordinate Ω j ν) x‖ = κ := by
    filter_upwards [hsat, vectorDirichletObservation_ae Ω U,
      l2VectorValue_vectorDirichletCoordinate_ae Ω ν] with x hx hu hν
    change vectorDirichletObservation Ω U x = sobolevVectorValue (fun j ↦ U j) x at hu
    rw [← hu, hν]
    exact hx
  have h := integral_norm_density_le_of_vector_weak_equation hΩ (fun j ↦ U j)
    (fun j ↦ vectorDirichletCoordinate Ω j f) (fun j ↦ vectorDirichletCoordinate Ω j ν)
    hpde (vectorDirichlet_pairing_of_alignment Ω U ν halign) hs
  have hνint : (∫ x, ‖l2VectorValue (fun j ↦ vectorDirichletCoordinate Ω j ν) x‖
      ∂(volume.restrict Ω)) = ∫ x, ‖ν x‖ ∂(volume.restrict Ω) :=
    integral_congr_ae ((l2VectorValue_vectorDirichletCoordinate_ae Ω ν).fun_comp norm)
  have hfint : (∫ x, ‖l2VectorValue (fun j ↦ vectorDirichletCoordinate Ω j f) x‖
      ∂(volume.restrict Ω)) = ∫ x, ‖f x‖ ∂(volume.restrict Ω) :=
    integral_congr_ae ((l2VectorValue_vectorDirichletCoordinate_ae Ω f).fun_comp norm)
  rwa [hνint, hfint] at h

/-- The actual capped density's squared `L²` norm is bounded by cap times input mass. -/
theorem norm_sq_density_le_of_vectorDirichlet (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcap : ν ∈ normCap (volume.restrict Ω) κ)
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x)
    (hsat : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) :
    ‖ν‖ ^ (2 : ℕ) ≤ κ * ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have hνnorm : Integrable (fun x ↦ ‖ν x‖) (volume.restrict Ω) :=
    ((Lp.memLp ν).integrable one_le_two).norm
  have hνsq : Integrable (fun x ↦ ‖ν x‖ ^ (2 : ℕ)) (volume.restrict Ω) :=
    (Lp.memLp ν).norm.integrable_sq
  calc
    ‖ν‖ ^ (2 : ℕ) = ∫ x, ‖ν x‖ ^ (2 : ℕ) ∂(volume.restrict Ω) := by
      rw [← real_inner_self_eq_norm_sq ν, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ ≤ ∫ x, κ * ‖ν x‖ ∂(volume.restrict Ω) := by
      apply integral_mono_ae hνsq (hνnorm.const_mul κ)
      filter_upwards [hcap] with x hx
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hx (norm_nonneg (ν x))
    _ = κ * ∫ x, ‖ν x‖ ∂(volume.restrict Ω) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_norm_density_le_of_vectorDirichlet hΩ U f ν hpde halign hsat) hκ

set_option synthInstance.maxHeartbeats 80000 in
/-- Every bounded open domain admits the actual vector obstacle with full mass contraction,
inactive equality, and cap-energy bound, with all locality hypotheses discharged. -/
theorem exists_vectorBalayage_finite_mass {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (f : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : VectorDirichletL2 Ω m) (U : VectorDirichletState Ω m),
      ν ∈ normCap (volume.restrict Ω) κ ∧
      (∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x = 0 → ν x = f x) ∧
      (∫ x, ‖ν x‖ ∂(volume.restrict Ω)) ≤ ∫ x, ‖f x‖ ∂(volume.restrict Ω) ∧
      ‖ν‖ ^ (2 : ℕ) ≤ κ * ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr (hΩb.measure_lt_top (μ := volume)).ne
  obtain ⟨ν, U, hν, hpde, halign, hsat⟩ := exists_vectorDirichlet_dual_obstacle hΩb f hκ
  exact ⟨ν, U, hν, hpde, halign, hsat,
    ae_vectorDirichlet_density_eq_input_on_inactive hΩ U f ν hpde,
    integral_norm_density_le_of_vectorDirichlet hΩ U f ν hpde halign hsat,
    norm_sq_density_le_of_vectorDirichlet hΩ U f ν hκ hν hpde halign hsat⟩

end PartialBalayage.Linear
