/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorInactiveLocality

/-!
# Positivity of the genuine scalar Dirichlet obstacle

The negative part of the actual zero-boundary Sobolev state is an admissible weak test.
The input is nonnegative, and alignment makes the capped density nonpositive where the
state is negative. The resulting weak pairing is nonnegative and is also the negative
of the negative part's gradient energy. Coercivity therefore removes the negative part.
Interior locality then proves nonnegativity of the density on the inactive set as well.

No positivity assumption on the solution, or on its capped density, is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The concrete scalar coordinate map has its actual pointwise coordinate almost everywhere. -/
theorem vectorDirichletCoordinate_coeFn_ae {m : ℕ}
    (f : VectorDirichletL2 Ω m) (j : Fin m) :
    (vectorDirichletCoordinate Ω j f : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x ↦ f x j := by
  simpa only [vectorDirichletCoordinate, PiLp.proj_apply] using
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL (p := 2) f

/-- A genuine weak Dirichlet equation with the correct sign on the negative set has a
nonnegative state, proved by testing with its actual Sobolev negative part. -/
theorem ae_nonneg_of_scalarDirichlet_weak_equation {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (U : H01 Ω) (f ν : L2D Ω)
    (hf : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ f x)
    (hν : ∀ᵐ x ∂(volume.restrict Ω), U.val 0 x < 0 → ν x ≤ 0)
    (hpde : ∀ W : H01 Ω, laplaceBilin Ω U W = ⟪f - ν, W.val 0⟫) :
    ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ U.val 0 x := by
  obtain ⟨P, hP⟩ := exists_isPositivePartGraph U
  obtain ⟨N, hN⟩ := exists_isPositivePartGraph (-U)
  have hdecomp := H01_eq_positive_sub_negative hΩ U P N hP hN
  have horth := laplaceBilin_positive_negative_eq_zero_of_graph U P N hP hN
  have henergy : laplaceBilin Ω U N = -laplaceBilin Ω N N := by
    rw [hdecomp]
    simp only [map_sub, sub_apply, horth, zero_sub]
  have hpair : 0 ≤ ⟪f - ν, N.val 0⟫ := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hν, hN.1, Lp.coeFn_neg (U.val 0), Lp.coeFn_sub f ν]
      with x hfx hνx hnx hneg hsub
    simp only [Submodule.coe_neg, PiLp.neg_apply, hneg, Pi.neg_apply] at hnx
    simp only [Real.inner_apply, hsub, Pi.sub_apply, hnx]
    by_cases hu : U.val 0 x < 0
    · exact mul_nonneg (sub_nonneg.mpr ((hνx hu).trans hfx)) (le_max_right _ _)
    · have hmax : max (-U.val 0 x) 0 = 0 :=
        max_eq_right (neg_nonpos.mpr (not_lt.mp hu))
      simp only [hmax, mul_zero]
      exact le_rfl
  have hnonpos : laplaceBilin Ω N N ≤ 0 := by
    have heq := hpde N
    rw [henergy] at heq
    linarith
  obtain ⟨c, hc, hcoercive⟩ := laplaceBilin_coercive_of_bounded hΩb
  have hnorm : ‖N‖ = 0 := by
    have hbound : c * (‖N‖ * ‖N‖) ≤ 0 := by
      simpa only [mul_assoc] using (hcoercive N).trans hnonpos
    have hnormsq : ‖N‖ * ‖N‖ ≤ 0 :=
      (mul_le_mul_iff_of_pos_left hc).mp (by simpa only [mul_zero] using hbound)
    nlinarith [norm_nonneg N]
  have hzero : N = 0 := norm_eq_zero.mp hnorm
  have hvalue : N.val 0 = 0 := by simp only [hzero, Submodule.coe_zero, PiLp.zero_apply]
  filter_upwards [hN.1, Lp.coeFn_neg (U.val 0), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x hnx hneg hz
  simp only [Submodule.coe_neg, PiLp.neg_apply, hneg, Pi.neg_apply] at hnx
  rw [hvalue, hz] at hnx
  have hle := le_max_left (-U.val 0 x) 0
  rw [← hnx] at hle
  simpa only [Pi.zero_apply] using neg_nonpos.mp hle

/-- Alignment of the one-coordinate obstacle gives the sign required by its negative-part
test. This proves positivity of its actual observation from positivity of the input. -/
theorem ae_scalar_vectorDirichlet_nonneg {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (U : VectorDirichletState Ω 1)
    (f ν : VectorDirichletL2 Ω 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hf : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ f x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ vectorDirichletObservation Ω U x 0 := by
  have hfcoord : ∀ᵐ x ∂(volume.restrict Ω),
      0 ≤ vectorDirichletCoordinate Ω (0 : Fin 1) f x := by
    filter_upwards [hf, vectorDirichletCoordinate_coeFn_ae f 0] with x hx hcoord
    rwa [hcoord]
  have hsign : ∀ᵐ x ∂(volume.restrict Ω), (U 0).val 0 x < 0 →
      vectorDirichletCoordinate Ω (0 : Fin 1) ν x ≤ 0 := by
    filter_upwards [halign, vectorDirichletObservation_ae Ω U,
      vectorDirichletCoordinate_coeFn_ae ν 0] with x hx hu hν
    intro hneg
    have hu0 : vectorDirichletObservation Ω U x 0 = (U 0).val 0 x := by
      simpa only [PiLp.toLp_apply] using
        congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hu
    have hactive : vectorDirichletObservation Ω U x ≠ 0 := by
      intro hz
      have hz0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hz
      simp only [PiLp.zero_apply, hu0] at hz0
      linarith
    have hν0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (hx hactive)
    simp only [PiLp.smul_apply, smul_eq_mul, hu0] at hν0
    rw [hν, hν0]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hκ (norm_nonneg _)) hneg.le
  have hstate := ae_nonneg_of_scalarDirichlet_weak_equation hΩ hΩb (U 0)
    (vectorDirichletCoordinate Ω 0 f) (vectorDirichletCoordinate Ω 0 ν)
    hfcoord hsign (hpde 0)
  filter_upwards [hstate, vectorDirichletObservation_ae Ω U] with x hx hu
  simpa only [hu, PiLp.toLp_apply] using hx

/-- The genuine scalar capped density is nonnegative on both active and inactive sets. -/
theorem ae_scalar_vectorDirichlet_density_nonneg {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (U : VectorDirichletState Ω 1)
    (f ν : VectorDirichletL2 Ω 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hf : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ f x 0)
    (hpde : ∀ j : Fin 1, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
        vectorDirichletObservation Ω U x) :
    ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ν x 0 := by
  filter_upwards [hf, ae_scalar_vectorDirichlet_nonneg hΩ hΩb U f ν hκ hf hpde halign,
    halign, ae_vectorDirichlet_density_eq_input_on_inactive hΩ U f ν hpde]
    with x hfx hu hx hi
  by_cases ha : vectorDirichletObservation Ω U x = 0
  · rw [hi ha]
    exact hfx
  · have hν0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (hx ha)
    simp only [PiLp.smul_apply, smul_eq_mul] at hν0
    rw [hν0]
    exact mul_nonneg (div_nonneg hκ (norm_nonneg _)) hu

/-- Nonnegative scalar input admits the actual finite obstacle with nonnegative state and
density, together with cap saturation, inactive equality, and full mass contraction. -/
theorem exists_scalarPositiveBalayage_finite_mass {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (f : VectorDirichletL2 Ω 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hf : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ f x 0) :
    ∃ (ν : VectorDirichletL2 Ω 1) (U : VectorDirichletState Ω 1),
      ν ∈ normCap (volume.restrict Ω) κ ∧
      (∀ j : Fin 1, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν, W.val 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
          vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω),
        vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x = 0 → ν x = f x) ∧
      (∫ x, ‖ν x‖ ∂(volume.restrict Ω)) ≤ ∫ x, ‖f x‖ ∂(volume.restrict Ω) ∧
      ‖ν‖ ^ (2 : ℕ) ≤ κ * ∫ x, ‖f x‖ ∂(volume.restrict Ω) ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ vectorDirichletObservation Ω U x 0) ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ν x 0) := by
  obtain ⟨ν, U, hν, hpde, halign, hsat, hi, hmass, henergy⟩ :=
    exists_vectorBalayage_finite_mass hΩ hΩb f hκ
  exact ⟨ν, U, hν, hpde, halign, hsat, hi, hmass, henergy,
    ae_scalar_vectorDirichlet_nonneg hΩ hΩb U f ν hκ hf hpde halign,
    ae_scalar_vectorDirichlet_density_nonneg hΩ hΩb U f ν hκ hf hpde halign⟩

end PartialBalayage.Linear
