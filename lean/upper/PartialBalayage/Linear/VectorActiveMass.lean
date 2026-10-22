/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorSobolevComposition

/-!
# Active-set mass comparison for the actual vector Dirichlet equation

The regularized direction vanishes on the inactive set. Consequently the norm-test argument
bounds active mass by active input mass. Together with genuine inactive-set locality and cap
saturation, this sharper comparison implies contraction of the total density mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace Classical

namespace PartialBalayage.Linear

section IntegralMass

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure X}

omit [InnerProductSpace ℝ E] in
/-- Null-measurable indicators preserve genuine integrability. -/
theorem integrable_indicator_null {a : X → E} (ha : Integrable a μ)
    {s : Set X} (hs : NullMeasurableSet s μ) : Integrable (s.indicator a) μ := by
  apply ha.norm.mono' (ha.aestronglyMeasurable.indicator₀ hs)
  filter_upwards with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

/-- Only the active part of the source contributes to the regularized norm tests. -/
theorem active_mass_le_active_input_of_regularized_tests {u f ν : X → E} {κ : ℝ}
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ n : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ) :
    (∫ x, if u x ≠ 0 then κ else 0 ∂μ) ≤ ∫ x in {x | u x ≠ 0}, ‖f x‖ ∂μ := by
  let s : Set X := {x | u x ≠ 0}
  have hs : NullMeasurableSet s μ := by
    have hzero := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hzero.compl
  have hp : ∀ᵐ x ∂μ, ⟪u x, s.indicator ν x⟫ = κ * ‖u x‖ := by
    filter_upwards [hpair] with x hx
    by_cases hux : u x ≠ 0
    · rw [Set.indicator_of_mem (show x ∈ s from hux)]
      exact hx
    · simp [s, not_not.mp hux]
  have ht (n : ℕ) : 0 ≤ ∫ x, ⟪s.indicator f x - s.indicator ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ := by
    convert! htest n using 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases hux : u x ≠ 0
    · rw [Set.indicator_of_mem (show x ∈ s from hux),
        Set.indicator_of_mem (show x ∈ s from hux)]
    · simp [s, not_not.mp hux, regularizedDirection]
  have h := active_mass_le_of_regularized_tests hu
    (integrable_indicator_null hf hs) (integrable_indicator_null hν hs) hp ht
  have hnorm : (fun x ↦ ‖s.indicator f x‖) = s.indicator (fun x ↦ ‖f x‖) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hnorm, integral_indicator₀ hs] at h
  exact h

/-- The sharp active-volume estimate uses only input mass on that same active set. -/
theorem cap_mul_measure_active_le_active_input_of_regularized_tests [IsFiniteMeasure μ]
    {u f ν : X → E} {κ : ℝ}
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ n : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ) :
    κ * (μ {x | u x ≠ 0}).toReal ≤ ∫ x in {x | u x ≠ 0}, ‖f x‖ ∂μ := by
  have hs : NullMeasurableSet {x | u x ≠ 0} μ := by
    have hzero := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hzero.compl
  have h := active_mass_le_active_input_of_regularized_tests hu hf hν hpair htest
  have heq : (fun x ↦ if u x ≠ 0 then κ else 0) =
      {x | u x ≠ 0}.indicator (fun _ ↦ κ) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator₀ hs, integral_const] at h
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using h

/-- Active-input mass comparison, true cap saturation, and inactive-set locality give
contraction of the total density mass. No mass bound is assumed. -/
theorem integral_norm_density_le_of_regularized_tests_and_locality
    {u f ν : X → E} {κ : ℝ}
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ n : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ)
    (hsaturation : ∀ᵐ x ∂μ, u x ≠ 0 → ‖ν x‖ = κ)
    (hlocality : ∀ᵐ x ∂μ, u x = 0 → ν x = f x) :
    (∫ x, ‖ν x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
  let s : Set X := {x | u x ≠ 0}
  have hs : NullMeasurableSet s μ := by
    have hzero := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hzero.compl
  have hmass := active_mass_le_active_input_of_regularized_tests hu hf hν hpair htest
  have ha : (∫ x in s, ‖ν x‖ ∂μ) = ∫ x, if u x ≠ 0 then κ else 0 ∂μ := by
    rw [← integral_indicator₀ hs]
    apply integral_congr_ae
    filter_upwards [hsaturation] with x hx
    by_cases hux : u x ≠ 0
    · rw [Set.indicator_of_mem (show x ∈ s from hux), ite_eq_left hux]
      exact hx hux
    · rw [Set.indicator_of_notMem (show x ∉ s from hux), ite_eq_right hux]
  have hc : (∫ x in sᶜ, ‖ν x‖ ∂μ) = ∫ x in sᶜ, ‖f x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hlocality, ae_restrict_mem₀ hs.compl] with x hx hxs
    have hux : u x = 0 := by
      simpa only [s, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hxs
    rw [hx hux]
  calc
    (∫ x, ‖ν x‖ ∂μ) = (∫ x in s, ‖ν x‖ ∂μ) + ∫ x in sᶜ, ‖ν x‖ ∂μ :=
      (integral_add_compl₀ hs hν.norm).symm
    _ = (∫ x, if u x ≠ 0 then κ else 0 ∂μ) + ∫ x in sᶜ, ‖f x‖ ∂μ := by rw [ha, hc]
    _ ≤ (∫ x in s, ‖f x‖ ∂μ) + ∫ x in sᶜ, ‖f x‖ ∂μ := add_le_add hmass le_rfl
    _ = ∫ x, ‖f x‖ ∂μ := integral_add_compl₀ hs hf.norm

end IntegralMass

section ActualEquation

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The actual vector Sobolev weak equation implies the sharp active-input comparison. -/
theorem cap_mul_volume_active_le_active_input_of_vector_weak_equation
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ}
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, (W : H1amb Ω) 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖) :
    κ * ((volume.restrict Ω) {x | sobolevVectorValue U x ≠ 0}).toReal ≤
      ∫ x in {x | sobolevVectorValue U x ≠ 0}, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) := by
  apply cap_mul_measure_active_le_active_input_of_regularized_tests
    (memLp_l2VectorValue (fun j ↦ (U j : H1amb Ω) 0)).aestronglyMeasurable
    (integrable_l2VectorValue f) (integrable_l2VectorValue ν) hpair
  intro n
  obtain ⟨V, hV⟩ := exists_regularizedDirectionGraph (by positivity : 0 < 1 / (n + 1 : ℝ)) U
  exact regularized_residual_pairing_nonneg_of_weak_equation (by positivity) U V f ν hpde hV

/-- The actual vector Sobolev equation gives density mass contraction once the true
inactive-set locality and active saturation properties have been established. -/
theorem integral_norm_density_le_of_vector_weak_equation_and_locality
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ}
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, (W : H1amb Ω) 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖)
    (hsaturation : ∀ᵐ x ∂(volume.restrict Ω),
      sobolevVectorValue U x ≠ 0 → ‖l2VectorValue ν x‖ = κ)
    (hlocality : ∀ᵐ x ∂(volume.restrict Ω),
      sobolevVectorValue U x = 0 → l2VectorValue ν x = l2VectorValue f x) :
    (∫ x, ‖l2VectorValue ν x‖ ∂(volume.restrict Ω)) ≤
      ∫ x, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) := by
  apply integral_norm_density_le_of_regularized_tests_and_locality
    (memLp_l2VectorValue (fun j ↦ (U j : H1amb Ω) 0)).aestronglyMeasurable
    (integrable_l2VectorValue f) (integrable_l2VectorValue ν) hpair _ hsaturation hlocality
  intro n
  obtain ⟨V, hV⟩ := exists_regularizedDirectionGraph (by positivity : 0 < 1 / (n + 1 : ℝ)) U
  exact regularized_residual_pairing_nonneg_of_weak_equation (by positivity) U V f ν hpde hV

end ActualEquation

end PartialBalayage.Linear
