/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.DirichletDual
public import CenteredMaximal.Ball.DirichletPoincareBounded

/-!
# The actual vector Dirichlet dual obstacle on a bounded domain

The state space is the finite Hilbert product of the existing scalar `H₀¹` graph spaces. Its
Dirichlet operator is the coordinatewise Riesz representative of the Laplace bilinear form.
Boundedness of the domain supplies coercivity through the proved Poincaré inequality. A bounded
observation map reads the scalar function values as one Euclidean-vector-valued `L²` function.

These concrete operators instantiate the dual obstacle theorem. Its state equation becomes the
coordinatewise weak Laplace equation, and the capped density aligns with the state's vector value.
No whole-space mass estimate is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- The finite Hilbert product of actual scalar zero-boundary Sobolev spaces. -/
abbrev VectorDirichletState (Ω : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ) : Type :=
  PiLp 2 (fun _ : Fin m ↦ H01 Ω)

/-- The genuine Euclidean-vector-valued `L²` observation space on the domain. -/
abbrev VectorDirichletL2 (Ω : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ) : Type :=
  Lp (EuclideanSpace ℝ (Fin m)) 2 (volume.restrict Ω)

/-- The Riesz representative of the actual scalar Dirichlet bilinear form. -/
def scalarDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω →L[ℝ] H01 Ω :=
  continuousLinearMapOfBilin (laplaceBilin Ω)

/-- Pairing the scalar Dirichlet operator gives the gradient energy bilinear form. -/
theorem inner_scalarDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    ⟪scalarDirichletOperator Ω U, V⟫ = laplaceBilin Ω U V :=
  continuousLinearMapOfBilin_apply _ _ _

/-- The scalar Dirichlet operator is symmetric and positive. -/
theorem isPositive_scalarDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (scalarDirichletOperator Ω).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨?_, ?_⟩
  · intro U V
    change ⟪scalarDirichletOperator Ω U, V⟫ = ⟪U, scalarDirichletOperator Ω V⟫
    rw [inner_scalarDirichletOperator, real_inner_comm,
      inner_scalarDirichletOperator]
    simp only [laplaceBilin_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ real_inner_comm _ _)
  · intro U
    change 0 ≤ ⟪scalarDirichletOperator Ω U, U⟫
    rw [inner_scalarDirichletOperator, laplaceBilin_self]
    exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)

/-- The actual vector Dirichlet operator applies the scalar Laplace operator coordinatewise. -/
def vectorDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    VectorDirichletState Ω m →L[ℝ] VectorDirichletState Ω m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ H01 Ω)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j ↦ scalarDirichletOperator Ω ∘L
      PiLp.proj 2 (fun _ : Fin m ↦ H01 Ω) j)

/-- The vector Dirichlet operator's coordinate is the corresponding scalar Dirichlet operator. -/
theorem vectorDirichletOperator_apply (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (j : Fin m) :
    vectorDirichletOperator Ω U j = scalarDirichletOperator Ω (U j) := rfl

/-- The vector Dirichlet pairing is the sum of the actual scalar gradient pairings. -/
theorem inner_vectorDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U V : VectorDirichletState Ω m) :
    ⟪vectorDirichletOperator Ω U, V⟫ = ∑ j : Fin m, laplaceBilin Ω (U j) (V j) := by
  rw [PiLp.inner_apply]
  simp only [vectorDirichletOperator_apply, inner_scalarDirichletOperator]

set_option synthInstance.maxHeartbeats 80000 in
/-- The coordinatewise actual vector Dirichlet operator is symmetric and positive. -/
theorem isPositive_vectorDirichletOperator (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    ContinuousLinearMap.IsPositive (𝕜 := ℝ) (E := VectorDirichletState Ω m)
      (vectorDirichletOperator Ω) := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨?_, ?_⟩
  · intro U V
    change ⟪vectorDirichletOperator Ω U, V⟫ = ⟪U, vectorDirichletOperator Ω V⟫
    rw [inner_vectorDirichletOperator, real_inner_comm,
      inner_vectorDirichletOperator]
    apply Finset.sum_congr rfl
    intro j _
    rw [← inner_scalarDirichletOperator, ← inner_scalarDirichletOperator]
    exact (isPositive_scalarDirichletOperator Ω).inner_left_eq_inner_right _ _ |>.trans
      (real_inner_comm _ _)
  · intro U
    change 0 ≤ ⟪vectorDirichletOperator Ω U, U⟫
    rw [inner_vectorDirichletOperator]
    apply Finset.sum_nonneg
    intro j _
    rw [← inner_scalarDirichletOperator]
    exact (isPositive_scalarDirichletOperator Ω).inner_nonneg_left _

/-- Boundedness of a nonzero-dimensional domain gives coercivity of the actual vector operator. -/
theorem exists_coercive_vectorDirichletOperator {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩb : Bornology.IsBounded Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ U : VectorDirichletState Ω m,
      c * ‖U‖ ^ (2 : ℕ) ≤ ⟪vectorDirichletOperator Ω U, U⟫ := by
  obtain ⟨c, hc, hcoercive⟩ := laplaceBilin_coercive_of_bounded hΩb
  refine ⟨c, hc, fun U ↦ ?_⟩
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, inner_vectorDirichletOperator]
  apply Finset.sum_le_sum
  intro j _
  simpa only [pow_two, mul_assoc] using hcoercive (U j)

/-- The actual scalar value coordinate of a zero-boundary Sobolev graph. -/
def scalarDirichletValueCLM (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω →L[ℝ] L2D Ω :=
  PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) 0 ∘L (H01 Ω).subtypeL

/-- The scalar observation map reads the value, rather than a derivative, of the graph. -/
theorem scalarDirichletValueCLM_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    scalarDirichletValueCLM Ω U = (U : H1amb Ω) 0 := rfl

/-- A scalar is inserted in the indicated coordinate of the Euclidean output space. -/
def vectorDirichletInjection (j : Fin m) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j 1)

/-- The observation map combines the actual scalar Sobolev values as one `L²` vector field. -/
def vectorDirichletObservation (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    VectorDirichletState Ω m →L[ℝ] VectorDirichletL2 Ω m :=
  ∑ j : Fin m, (vectorDirichletInjection j).compLpL 2 (volume.restrict Ω) ∘L
    scalarDirichletValueCLM Ω ∘L PiLp.proj 2 (fun _ : Fin m ↦ H01 Ω) j

/-- Applying the observation map sums its actual scalar `L²` coordinate injections. -/
theorem vectorDirichletObservation_apply (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) :
    vectorDirichletObservation Ω U = ∑ j : Fin m,
      (vectorDirichletInjection j).compLp ((U j : H1amb Ω) 0) := by
  simp only [vectorDirichletObservation, sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, scalarDirichletValueCLM_apply]
  rfl

/-- The scalar injection is exactly the corresponding single-coordinate vector. -/
theorem vectorDirichletInjection_apply (j : Fin m) (a : ℝ) :
    vectorDirichletInjection j a = EuclideanSpace.single j a := by
  ext k
  simp only [vectorDirichletInjection, ContinuousLinearMap.toSpanSingleton_apply,
    PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  by_cases h : k = j <;> simp [h]

/-- The observation is almost everywhere the Euclidean vector of actual Sobolev values. -/
theorem vectorDirichletObservation_ae (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) :
    ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x =
      WithLp.toLp 2 (fun j : Fin m ↦ (U j : H1amb Ω) 0 x) := by
  rw [vectorDirichletObservation_apply]
  have hcoords : ∀ᵐ x ∂(volume.restrict Ω), ∀ j : Fin m,
      (vectorDirichletInjection j).compLp ((U j : H1amb Ω) 0) x =
        vectorDirichletInjection j ((U j : H1amb Ω) 0 x) :=
    ae_all_iff.mpr (fun j ↦ (vectorDirichletInjection j).coeFn_compLp _)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin m ↦ (vectorDirichletInjection j).compLp ((U j : H1amb Ω) 0)), hcoords]
    with x hsum hx
  rw [hsum]
  rw [Finset.sum_apply]
  have heq : (∑ j : Fin m, (vectorDirichletInjection j).compLp ((U j : H1amb Ω) 0) x) =
      ∑ j : Fin m, EuclideanSpace.single j ((U j : H1amb Ω) 0 x) := by
    exact Finset.sum_congr rfl (fun j _ ↦ (hx j).trans (vectorDirichletInjection_apply _ _))
  rw [heq]
  ext j
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j)
    (∑ k : Fin m, EuclideanSpace.single k ((U k : H1amb Ω) 0 x)) = _
  rw [map_sum]
  simp [PiLp.proj_apply, PiLp.single_apply]

/-- The actual scalar `L²` coordinate of a Euclidean-vector-valued `L²` function. -/
def vectorDirichletCoordinate (Ω : Set (EuclideanSpace ℝ (Fin d))) (j : Fin m) :
    VectorDirichletL2 Ω m →L[ℝ] L2D Ω :=
  (PiLp.proj 2 (fun _ : Fin m ↦ ℝ) j).compLpL 2 (volume.restrict Ω)

/-- In the `L²` pairing, injecting a scalar is adjoint to taking that coordinate. -/
theorem inner_vectorDirichletInjection_compLp (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (j : Fin m) (r : VectorDirichletL2 Ω m) (v : L2D Ω) :
    ⟪r, (vectorDirichletInjection j).compLp v⟫ =
      ⟪vectorDirichletCoordinate Ω j r, v⟫ := by
  unfold vectorDirichletCoordinate
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(vectorDirichletInjection j).coeFn_compLp v,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL (p := 2) r]
      with x hinj hcoord
  rw [hinj, hcoord, vectorDirichletInjection_apply]
  simp [EuclideanSpace.inner_single_right, PiLp.proj_apply]

/-- A single-coordinate Sobolev state has only that coordinate in its vector observation. -/
theorem vectorDirichletObservation_single (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (j : Fin m) (W : H01 Ω) :
    vectorDirichletObservation Ω (PiLp.single 2 j W) =
      (vectorDirichletInjection j).compLp ((W : H1amb Ω) 0) := by
  rw [vectorDirichletObservation_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro k _ hkj
    rw [PiLp.single_eq_of_ne 2 hkj]
    simp only [Submodule.coe_zero, PiLp.zero_apply]
    change (vectorDirichletInjection k).compLpL 2 (volume.restrict Ω) 0 = 0
    exact map_zero _
  · simp

/-- Testing one coordinate of the actual vector Dirichlet operator gives its scalar weak form. -/
theorem inner_vectorDirichletOperator_single (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (j : Fin m) (W : H01 Ω) :
    ⟪vectorDirichletOperator Ω U, PiLp.single 2 j W⟫ = laplaceBilin Ω (U j) W := by
  rw [inner_vectorDirichletOperator, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro k _ hkj
    rw [PiLp.single_eq_of_ne 2 hkj]
    exact map_zero _
  · simp

set_option synthInstance.maxHeartbeats 80000 in
/-- The concrete state equation is the actual coordinatewise weak Laplace equation. -/
theorem vectorDirichlet_weak_equation (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (r : VectorDirichletL2 Ω m)
    (heq : vectorDirichletOperator Ω U = ContinuousLinearMap.adjoint (𝕜 := ℝ)
      (vectorDirichletObservation (m := m) Ω) r)
    (j : Fin m) (W : H01 Ω) :
    laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j r, (W : H1amb Ω) 0⟫ := by
  have h := congrArg (fun V : VectorDirichletState Ω m ↦ ⟪V, PiLp.single 2 j W⟫) heq
  rw [inner_vectorDirichletOperator_single, ContinuousLinearMap.adjoint_inner_left,
    vectorDirichletObservation_single, inner_vectorDirichletInjection_compLp] at h
  exact h

set_option synthInstance.maxHeartbeats 80000 in
/-- The bounded-domain vector obstacle has an actual zero-boundary weak Laplace state,
with a capped density aligned with that state's vector value on its active set. -/
theorem exists_vectorDirichlet_dual_obstacle {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩb : Bornology.IsBounded Ω)
    (f : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : VectorDirichletL2 Ω m) (U : VectorDirichletState Ω m),
      ν ∈ normCap (volume.restrict Ω) κ ∧
      (∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
          (W : H1amb Ω) 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr (hΩb.measure_lt_top (μ := volume)).ne
  obtain ⟨c, hc, hcoercive⟩ := exists_coercive_vectorDirichletOperator (m := m) hΩb
  obtain ⟨ν, U, hν, _, heq, halign, hsat⟩ := exists_dirichlet_dual_obstacle
    (H := VectorDirichletState Ω m) (E := EuclideanSpace ℝ (Fin m))
    (volume.restrict Ω) (vectorDirichletOperator (m := m) Ω)
    (isPositive_vectorDirichletOperator (m := m) Ω)
    hc hcoercive (vectorDirichletObservation (m := m) Ω) f hκ
  refine ⟨ν, U, hν, ?_, halign, hsat⟩
  intro j W
  simpa only [map_sub] using vectorDirichlet_weak_equation Ω U (f - ν) heq j W

end PartialBalayage.Linear
