/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorDirichlet
public import PartialBalayage.Linear.VectorSobolevComposition

/-!
# Actual vector partial balayage on a bounded domain

The concrete coercive vector Dirichlet obstacle supplies a capped density and a genuine
zero-boundary weak Laplace state. Actual regularized Sobolev norm tests bound the volume of
the state's active set by the input mass. This construction includes no mass estimate among
its hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d m : ℕ}

/-- The actual scalar `L²` coordinates reconstruct the original vector almost everywhere. -/
theorem l2VectorValue_vectorDirichletCoordinate_ae (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : VectorDirichletL2 Ω m) :
    l2VectorValue (fun j ↦ vectorDirichletCoordinate Ω j f) =ᵐ[volume.restrict Ω] f := by
  have hcoords : ∀ᵐ x ∂(volume.restrict Ω), ∀ j : Fin m,
      vectorDirichletCoordinate Ω j f x = f x j := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL
      (p := 2) f] with x hx
    exact hx
  filter_upwards [hcoords] with x hx
  ext j
  exact hx j

/-- Alignment of the actual state observation yields the vector Sobolev mass pairing. -/
theorem vectorDirichlet_pairing_of_alignment (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue (fun j ↦ U j) x,
        l2VectorValue (fun j ↦ vectorDirichletCoordinate Ω j ν) x⟫ =
      κ * ‖sobolevVectorValue (fun j ↦ U j) x‖ := by
  filter_upwards [halign, vectorDirichletObservation_ae Ω U,
    l2VectorValue_vectorDirichletCoordinate_ae Ω ν] with x hx hu hν
  change vectorDirichletObservation Ω U x = sobolevVectorValue (fun j ↦ U j) x at hu
  rw [← hu, hν]
  by_cases hzero : vectorDirichletObservation Ω U x = 0
  · simp only [hzero, inner_zero_left, norm_zero, mul_zero]
  · rw [hx hzero, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hzero]

/-- The actual vector weak equation and its cap alignment imply the active-volume estimate. -/
theorem cap_mul_volume_observation_active_le_of_vectorDirichlet
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure (volume.restrict Ω)]
    (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m) {κ : ℝ}
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
        (W : H1amb Ω) 0⟫)
    (halign : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
      ν x = (κ / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) :
    κ * ((volume.restrict Ω) {x | vectorDirichletObservation Ω U x ≠ 0}).toReal ≤
      ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have h := cap_mul_volume_active_le_of_vector_weak_equation (fun j ↦ U j)
    (fun j ↦ vectorDirichletCoordinate Ω j f) (fun j ↦ vectorDirichletCoordinate Ω j ν)
    hpde (vectorDirichlet_pairing_of_alignment Ω U ν halign)
  have hs : {x | vectorDirichletObservation Ω U x ≠ 0} =ᵐ[volume.restrict Ω]
      {x | sobolevVectorValue (fun j ↦ U j) x ≠ 0} := by
    filter_upwards [vectorDirichletObservation_ae Ω U] with x hx
    change (vectorDirichletObservation Ω U x ≠ 0) =
      (sobolevVectorValue (fun j ↦ U j) x ≠ 0)
    change vectorDirichletObservation Ω U x = sobolevVectorValue (fun j ↦ U j) x at hx
    rw [hx]
  rw [measure_congr hs]
  exact h.trans_eq (integral_congr_ae
    ((l2VectorValue_vectorDirichletCoordinate_ae Ω f).fun_comp norm))

/-- The active set of the actual `L²` state observation is null measurable. -/
theorem nullMeasurableSet_vectorDirichlet_active (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) :
    NullMeasurableSet {x | vectorDirichletObservation Ω U x ≠ 0} (volume.restrict Ω) := by
  have hnorm := (Lp.aestronglyMeasurable (vectorDirichletObservation Ω U)).norm
  have hzero := hnorm.nullMeasurableSet_eq_fun (aestronglyMeasurable_const (b := (0 : ℝ)))
  simpa only [norm_eq_zero, Set.compl_ofPred] using hzero.compl

/-- Restricting the actual density to the active set preserves its `L²` membership. -/
theorem memLp_vectorDirichlet_activeDensity (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m) :
    MemLp ({x | vectorDirichletObservation Ω U x ≠ 0}.indicator ν) 2
      (volume.restrict Ω) := by
  apply (Lp.memLp ν).of_le
    ((Lp.aestronglyMeasurable ν).indicator₀ (nullMeasurableSet_vectorDirichlet_active Ω U))
  exact Eventually.of_forall (fun x ↦ norm_indicator_le_norm_self ν x)

/-- The active part of the actual capped density, as a genuine vector `L²` element. -/
def vectorDirichletActiveDensity (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m) : VectorDirichletL2 Ω m :=
  (memLp_vectorDirichlet_activeDensity Ω U ν).toLp
    ({x | vectorDirichletObservation Ω U x ≠ 0}.indicator ν)

/-- The actual active `L²` density agrees almost everywhere with the active-set indicator. -/
theorem vectorDirichletActiveDensity_ae (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m) :
    vectorDirichletActiveDensity Ω U ν =ᵐ[volume.restrict Ω]
      {x | vectorDirichletObservation Ω U x ≠ 0}.indicator ν :=
  MemLp.coeFn_toLp _

/-- Saturation and the active-volume bound control the energy of the actual active density. -/
theorem vectorDirichletActiveDensity_energy_le (Ω : Set (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : VectorDirichletState Ω m) (f ν : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsat : ∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ)
    (hmass : κ * ((volume.restrict Ω)
      {x | vectorDirichletObservation Ω U x ≠ 0}).toReal ≤
        ∫ x, ‖f x‖ ∂(volume.restrict Ω)) :
    ‖vectorDirichletActiveDensity Ω U ν‖ ^ (2 : ℕ) ≤
      κ * ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have heq : (fun x ↦ ‖vectorDirichletActiveDensity Ω U ν x‖ ^ (2 : ℕ)) =ᵐ[
      volume.restrict Ω]
      {x | vectorDirichletObservation Ω U x ≠ 0}.indicator (fun _ ↦ κ ^ (2 : ℕ)) := by
    filter_upwards [vectorDirichletActiveDensity_ae Ω U ν, hsat] with x hx hnorm
    rw [hx]
    by_cases hactive : vectorDirichletObservation Ω U x ≠ 0
    · rw [Set.indicator_of_mem hactive, Set.indicator_of_mem hactive, hnorm hactive]
    · rw [Set.indicator_of_notMem hactive, Set.indicator_of_notMem hactive, norm_zero,
        zero_pow two_ne_zero]
  rw [← real_inner_self_eq_norm_sq (vectorDirichletActiveDensity Ω U ν), L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  rw [integral_congr_ae heq,
    integral_indicator₀ (nullMeasurableSet_vectorDirichlet_active Ω U), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change ((volume.restrict Ω) {x | vectorDirichletObservation Ω U x ≠ 0}).toReal * κ ^ 2 ≤ _
  calc
    _ = κ * (κ * ((volume.restrict Ω)
        {x | vectorDirichletObservation Ω U x ≠ 0}).toReal) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hκ

set_option synthInstance.maxHeartbeats 80000 in
/-- Bounded domains admit an actual vector partial balayage with its active-volume bound. -/
theorem exists_vectorBalayage_finite {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩb : Bornology.IsBounded Ω)
    (f : VectorDirichletL2 Ω m) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : VectorDirichletL2 Ω m) (U : VectorDirichletState Ω m),
      ν ∈ normCap (volume.restrict Ω) κ ∧
      (∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j f - vectorDirichletCoordinate Ω j ν,
          (W : H1amb Ω) 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = (κ / ‖vectorDirichletObservation Ω U x‖) •
          vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = κ) ∧
      κ * ((volume.restrict Ω) {x | vectorDirichletObservation Ω U x ≠ 0}).toReal ≤
        ∫ x, ‖f x‖ ∂(volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr (hΩb.measure_lt_top (μ := volume)).ne
  obtain ⟨ν, U, hν, hpde, halign, hsat⟩ := exists_vectorDirichlet_dual_obstacle hΩb f hκ
  exact ⟨ν, U, hν, hpde, halign, hsat,
    cap_mul_volume_observation_active_le_of_vectorDirichlet Ω U f ν hpde halign⟩

end PartialBalayage.Linear
