/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WeakDirichletEnergy
public import PartialBalayage.Linear.DirichletTestClosure
public import PartialBalayage.Linear.L2DomainRestriction
public import PartialBalayage.Linear.CapComplementarity
public import PartialBalayage.Linear.ExhaustionWeakEquation

/-!
# Genuine complementarity from the weak equation and limit energy inequality

Testing the actual whole-space PDE with the true state identifies its physical energy.
The limit energy-mass inequality then makes the density pairing attain the support bound.
The nonnegative pointwise deficit has zero integral, giving actual alignment and saturation.
No compactness of derivatives, locality certificate, or further regularity is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace Topology

namespace PartialBalayage.Linear

section GeneralSupport

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {μ : Measure X}

/-- A capped density attaining the full support pairing aligns pointwise almost everywhere. -/
theorem ae_inner_eq_cap_mul_norm_of_pairing_ge {κ : ℝ}
    (ν w : Lp E 2 μ) (hν : ν ∈ normCap μ κ)
    (hw : Integrable (w : X → E) μ)
    (hpair : κ * ∫ x, ‖w x‖ ∂μ ≤ inner ℝ ν w) :
    ∀ᵐ x ∂μ, inner ℝ (w x) (ν x) = κ * ‖w x‖ := by
  have hint : Integrable (fun x ↦ κ * ‖w x‖ - inner ℝ (w x) (ν x)) μ :=
    (hw.norm.const_mul κ).sub (L2.integrable_inner (𝕜 := ℝ) w ν)
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ κ * ‖w x‖ - inner ℝ (w x) (ν x)) := by
    filter_upwards [hν] with x hx
    have h := (real_inner_le_norm (w x) (ν x)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg (w x)))
    simpa only [Pi.zero_apply, mul_comm, sub_nonneg] using h
  have hle : (∫ x, κ * ‖w x‖ - inner ℝ (w x) (ν x) ∂μ) ≤ 0 := by
    rw [integral_sub (hw.norm.const_mul κ) (L2.integrable_inner (𝕜 := ℝ) w ν),
      integral_const_mul, ← L2.inner_def, real_inner_comm]
    exact sub_nonpos.mpr hpair
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp
    (le_antisymm hle (integral_nonneg_of_ae hnonneg))
  filter_upwards [hz] with x hx
  exact (sub_eq_zero.mp hx).symm

/-- Full support pairing forces genuine alignment and cap saturation on the active set. -/
theorem ae_alignment_saturation_of_pairing_ge {κ : ℝ} (hκ : 0 ≤ κ)
    (ν w : Lp E 2 μ) (hν : ν ∈ normCap μ κ)
    (hw : Integrable (w : X → E) μ)
    (hpair : κ * ∫ x, ‖w x‖ ∂μ ≤ inner ℝ ν w) :
    (∀ᵐ x ∂μ, w x ≠ 0 → ν x = (κ / ‖w x‖) • w x) ∧
      (∀ᵐ x ∂μ, w x ≠ 0 → ‖ν x‖ = κ) := by
  have hi := ae_inner_eq_cap_mul_norm_of_pairing_ge ν w hν hw hpair
  have ha : ∀ᵐ x ∂μ, w x ≠ 0 → ν x = (κ / ‖w x‖) • w x := by
    filter_upwards [hν, hi] with x hx hinner
    intro hwx
    exact eq_capSupportVector_of_inner_eq hκ hwx hx hinner
  refine ⟨ha, ?_⟩
  filter_upwards [ha] with x hx
  intro hwx
  rw [hx hwx]
  exact norm_capSupportVector hκ hwx

end GeneralSupport

variable {d m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin m)
local notation "H" => VectorDirichletState (univ : Set X) m
local notation "L²" => Lp V 2 (volume : Measure X)

/-- Pairing the actual global value equals pairing its existing restricted-univ convention. -/
theorem inner_restrict_univ_globalObservation (f : L²) (U : H) :
    inner ℝ (restrictL2CLM univ f) (vectorDirichletObservation univ U) =
      inner ℝ f (globalVectorDirichletObservation U) := by
  rw [L2.inner_def, L2.inner_def]
  simp only [Measure.restrict_univ]
  have hr : restrictL2CLM univ f =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using restrictL2CLM_ae univ f
  apply integral_congr_ae
  filter_upwards [hr, globalVectorDirichletObservation_ae U] with x hx hu
  rw [hx, hu]

/-- Testing the genuine global scalar-coordinate PDE identifies the actual vector energy. -/
theorem global_vectorDirichletEnergy_eq_pairing (U : H) (f ν : L²)
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      inner ℝ (vectorDirichletCoordinate univ j (restrictL2CLM univ f) -
        vectorDirichletCoordinate univ j (restrictL2CLM univ ν)) ((W : H1amb univ) 0)) :
    vectorDirichletEnergy U = inner ℝ (f - ν) (globalVectorDirichletObservation U) := by
  rw [vectorDirichletEnergy_eq_pairing U (restrictL2CLM univ f) (restrictL2CLM univ ν) hpde,
    ← map_sub, inner_restrict_univ_globalObservation]

/-- The true global PDE and limit energy inequality force actual alignment and saturation. -/
theorem global_vectorDirichlet_alignment_saturation (U : H) (f ν : L²) {κ : ℝ}
    (hκ : 0 ≤ κ) (hν : ν ∈ normCap volume κ)
    (hU : Integrable (globalVectorDirichletObservation U : X → V))
    (hpde : ∀ j : Fin m, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      inner ℝ (vectorDirichletCoordinate univ j (restrictL2CLM univ f) -
        vectorDirichletCoordinate univ j (restrictL2CLM univ ν)) ((W : H1amb univ) 0))
    (henergy : vectorDirichletEnergy U + κ * ∫ x, ‖globalVectorDirichletObservation U x‖ ≤
      inner ℝ f (globalVectorDirichletObservation U)) :
    (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 →
      ν x = (κ / ‖globalVectorDirichletObservation U x‖) •
        globalVectorDirichletObservation U x) ∧
    (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 → ‖ν x‖ = κ) := by
  have he := global_vectorDirichletEnergy_eq_pairing U f ν hpde
  rw [inner_sub_left] at he
  apply ae_alignment_saturation_of_pairing_ge hκ ν (globalVectorDirichletObservation U) hν hU
  linarith

/-- Actual global compact-test equations extend to all genuine H01 coordinate tests. -/
theorem global_vectorDirichletPDE_of_compactTests (U : H) (f ν : L²)
    (htest : ∀ (j : Fin m) (φ : X → ℝ) (hφ : IsTestFn univ φ),
      laplaceBilin univ (U j) hφ.toH01 =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) hφ.testCls) :
    ∀ j : Fin m, ∀ W : H01 (univ : Set X), laplaceBilin univ (U j) W =
      inner ℝ (vectorDirichletCoordinate univ j (restrictL2CLM univ f) -
        vectorDirichletCoordinate univ j (restrictL2CLM univ ν)) ((W : H1amb univ) 0) := by
  intro j
  apply laplaceBilin_eq_inner_of_test_equation
  intro φ hφ
  exact htest j φ hφ

/-- The true compact-test PDE and weak-limit energy inequality force actual complementarity. -/
theorem global_vectorDirichlet_alignment_saturation_of_compactTests
    (U : H) (f ν : L²) {κ : ℝ} (hκ : 0 ≤ κ) (hν : ν ∈ normCap volume κ)
    (hU : Integrable (globalVectorDirichletObservation U : X → V))
    (htest : ∀ (j : Fin m) (φ : X → ℝ) (hφ : IsTestFn univ φ),
      laplaceBilin univ (U j) hφ.toH01 =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) hφ.testCls)
    (henergy : vectorDirichletEnergy U + κ * ∫ x, ‖globalVectorDirichletObservation U x‖ ≤
      inner ℝ f (globalVectorDirichletObservation U)) :
    (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 →
      ν x = (κ / ‖globalVectorDirichletObservation U x‖) •
        globalVectorDirichletObservation U x) ∧
    (∀ᵐ x ∂volume, globalVectorDirichletObservation U x ≠ 0 → ‖ν x‖ = κ) :=
  global_vectorDirichlet_alignment_saturation U f ν hκ hν hU
    (global_vectorDirichletPDE_of_compactTests U f ν htest) henergy

/-- True finite energy balances, weak convergence, cap, and compact-test PDE give full
integrability and genuine complementarity of the same limit state. -/
theorem global_vectorDirichlet_complementarity_of_weak_limit
    {ι : Type*} {l : Filter ι} [l.NeBot] {κ : ℝ} (hκ : 0 < κ)
    {U : ι → H} {Ulimit : H} (f ν : L²) (hν : ν ∈ normCap volume κ)
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (hU : ∀ᶠ k in l, Integrable (globalVectorDirichletObservation (U k) : X → V))
    (heq : ∀ᶠ k in l, vectorDirichletEnergy (U k) +
      κ * ∫ x, ‖globalVectorDirichletObservation (U k) x‖ =
        inner ℝ f (globalVectorDirichletObservation (U k)))
    (htest : ∀ (j : Fin m) (φ : X → ℝ) (hφ : IsTestFn univ φ),
      laplaceBilin univ (Ulimit j) hφ.toH01 =
        inner ℝ (univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν) hφ.testCls) :
    Integrable (globalVectorDirichletObservation Ulimit : X → V) ∧
      (∀ᵐ x ∂volume, globalVectorDirichletObservation Ulimit x ≠ 0 →
        ν x = (κ / ‖globalVectorDirichletObservation Ulimit x‖) •
          globalVectorDirichletObservation Ulimit x) ∧
      (∀ᵐ x ∂volume,
        globalVectorDirichletObservation Ulimit x ≠ 0 → ‖ν x‖ = κ) := by
  have hb := vectorDirichlet_energy_mass_le_of_weak_tendsto hκ hUt
    (innerSL ℝ f ∘L globalVectorDirichletObservation) hU heq
  exact ⟨hb.1, global_vectorDirichlet_alignment_saturation_of_compactTests
    Ulimit f ν hκ.le hν hb.1 htest hb.2⟩

end PartialBalayage.Linear
