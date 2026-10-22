/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorSobolevExtension
public import PartialBalayage.Linear.WholeSpaceL1Norm
public import Mathlib.Analysis.Convex.Mul

/-!
# Weak lower semicontinuity of actual Dirichlet energy and full vector mass

The true gradient coordinates define a bounded map into a finite Hilbert product whose squared
norm is exactly the physical energy. The actual whole-space vector value map is bounded and
linear. Convexity and the full norm integral therefore give weak lower semicontinuity of the
extended energy-mass functional, including states whose value mass is infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The actual family of physical gradient coordinates in its finite Hilbert product. -/
def vectorDirichletGradientCLM (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    VectorDirichletState Ω m →L[ℝ] PiLp 2 (fun _ : Fin m × Fin d ↦ L2D Ω) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m × Fin d ↦ L2D Ω)).symm.toContinuousLinearMap
    ∘L ContinuousLinearMap.pi (fun ji ↦ PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) ji.2.succ
      ∘L (H01 Ω).subtypeL ∘L PiLp.proj 2 (fun _ : Fin m ↦ H01 Ω) ji.1)

/-- The gradient product norm is exactly the actual physical vector Dirichlet energy. -/
theorem norm_vectorDirichletGradientCLM_sq (U : VectorDirichletState Ω m) :
    ‖vectorDirichletGradientCLM Ω U‖ ^ 2 = vectorDirichletEnergy U := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  unfold vectorDirichletEnergy
  simp only [laplaceBilin_self]
  rfl

/-- The actual physical vector Dirichlet energy is convex. -/
theorem convexOn_vectorDirichletEnergy :
    ConvexOn ℝ univ (vectorDirichletEnergy : VectorDirichletState Ω m → ℝ) := by
  have h := ((convexOn_norm (E := PiLp 2 (fun _ : Fin m × Fin d ↦ L2D Ω))
    convex_univ).pow (fun x _ ↦ norm_nonneg x) 2).comp_linearMap
      (vectorDirichletGradientCLM (m := m) Ω).toLinearMap
  convert! h using 1
  ext U
  exact (norm_vectorDirichletGradientCLM_sq U).symm

/-- The actual physical vector Dirichlet energy is continuous in the Sobolev norm. -/
theorem continuous_vectorDirichletEnergy :
    Continuous (vectorDirichletEnergy : VectorDirichletState Ω m → ℝ) := by
  exact ((vectorDirichletGradientCLM Ω).continuous.norm.pow 2).congr
    (fun U ↦ norm_vectorDirichletGradientCLM_sq U)

/-- The actual physical vector Dirichlet energy is lower semicontinuous for weak convergence. -/
theorem lowerSemicontinuous_vectorDirichletEnergy_weak :
    LowerSemicontinuous (vectorDirichletEnergy ∘
      (toWeakSpace ℝ (VectorDirichletState Ω m)).symm) :=
  convexOn_vectorDirichletEnergy.lowerSemicontinuous_comp_toWeakSpace_symm
    continuous_vectorDirichletEnergy.lowerSemicontinuous

/-- Every genuine bounded real linear map induces a continuous map between weak spaces. -/
theorem continuous_weakMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    Continuous (fun x : WeakSpace ℝ E ↦
      toWeakSpace ℝ F (L ((toWeakSpace ℝ E).symm x))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro ℓ
  change Continuous (fun x : WeakSpace ℝ E ↦ ℓ (L ((toWeakSpace ℝ E).symm x)))
  exact (ℓ.comp L).continuous_comp_toWeakSpace_symm

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin m)
local notation "H" => VectorDirichletState (univ : Set X) m

/-- The actual whole-space `L²` vector observation of a genuine global Dirichlet state. -/
def globalVectorDirichletObservation : H →L[ℝ] Lp V 2 (volume : Measure X) :=
  zeroExtendL2CLM MeasurableSet.univ ∘L vectorDirichletObservation univ

/-- The global observation is the actual original represented value almost everywhere. -/
theorem globalVectorDirichletObservation_ae (U : H) :
    globalVectorDirichletObservation U =ᵐ[volume] vectorDirichletObservation univ U := by
  change zeroExtendL2 MeasurableSet.univ (vectorDirichletObservation univ U) =ᵐ[volume] _
  simpa only [indicator_univ] using
    zeroExtendL2_ae MeasurableSet.univ (vectorDirichletObservation univ U)

/-- The extended functional uses the true physical energy and the full vector norm integral. -/
def vectorDirichletEnergyMass (κ : ℝ) (U : H) : ℝ≥0∞ :=
  ENNReal.ofReal (vectorDirichletEnergy U) +
    ENNReal.ofReal κ * ∫⁻ x, ‖globalVectorDirichletObservation U x‖ₑ

/-- The full vector mass of the actual observation is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_globalVectorDirichletMass_weak :
    LowerSemicontinuous (fun U : WeakSpace ℝ H ↦
      ∫⁻ x, ‖globalVectorDirichletObservation ((toWeakSpace ℝ H).symm U) x‖ₑ) := by
  have hw : Continuous (fun U : WeakSpace ℝ H ↦ toWeakSpace ℝ (Lp V 2 (volume : Measure X))
      (globalVectorDirichletObservation ((toWeakSpace ℝ H).symm U))) := by
    apply WeakBilin.continuous_of_continuous_eval
    intro ℓ
    change Continuous (fun U : WeakSpace ℝ H ↦
      ℓ (globalVectorDirichletObservation ((toWeakSpace ℝ H).symm U)))
    exact (ℓ.comp globalVectorDirichletObservation).continuous_comp_toWeakSpace_symm
  have h := (lowerSemicontinuous_lintegral_norm_weak (E := V) (μ := (volume : Measure X))).comp hw
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h

/-- The actual extended energy plus cap-weighted full mass is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_vectorDirichletEnergyMass_weak (κ : ℝ) :
    LowerSemicontinuous (vectorDirichletEnergyMass κ ∘ (toWeakSpace ℝ H).symm) := by
  apply LowerSemicontinuous.add
  · exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous
      lowerSemicontinuous_vectorDirichletEnergy_weak
      (fun _ _ h ↦ ENNReal.ofReal_le_ofReal h)
  · exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      lowerSemicontinuous_globalVectorDirichletMass_weak (fun _ _ h ↦ mul_le_mul_right h _)

/-- For integrable actual values, the extended functional is the ordinary energy-mass sum. -/
theorem vectorDirichletEnergyMass_of_integrable {κ : ℝ} (hκ : 0 ≤ κ) (U : H)
    (hU : Integrable (globalVectorDirichletObservation U : X → V)) :
    vectorDirichletEnergyMass κ U = ENNReal.ofReal (vectorDirichletEnergy U +
      κ * ∫ x, ‖globalVectorDirichletObservation U x‖) := by
  rw [vectorDirichletEnergyMass, ← ofReal_integral_norm_eq_lintegral_enorm hU,
    ← ENNReal.ofReal_mul hκ, ENNReal.ofReal_add (vectorDirichletEnergy_nonneg U)
      (mul_nonneg hκ (integral_nonneg (fun _ ↦ norm_nonneg _)))]

/-- A genuine weak limit preserves the finite-state upper bound on the energy-mass functional. -/
theorem vectorDirichletEnergyMass_le_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (κ : ℝ) {U : ι → H} {Ulimit : H}
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (ℓ : H →L[ℝ] ℝ)
    (hbound : ∀ᶠ k in l, vectorDirichletEnergyMass κ (U k) ≤ ENNReal.ofReal (ℓ (U k))) :
    vectorDirichletEnergyMass κ Ulimit ≤ ENNReal.ofReal (ℓ Ulimit) := by
  have hpair : Tendsto (fun k ↦ ENNReal.ofReal (ℓ (U k))) l
      (𝓝 (ENNReal.ofReal (ℓ Ulimit))) := by
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp
      ((ℓ.continuous_comp_toWeakSpace_symm.tendsto _).comp hUt)
  by_contra hn
  obtain ⟨r, hpairr, hrenergy⟩ := exists_between (lt_of_not_ge hn)
  have hlo : ∀ᶠ k in l, r < vectorDirichletEnergyMass κ (U k) :=
    hUt.eventually ((lowerSemicontinuous_vectorDirichletEnergyMass_weak κ)
      (toWeakSpace ℝ H Ulimit) r hrenergy)
  have hhi : ∀ᶠ k in l, ENNReal.ofReal (ℓ (U k)) < r :=
    hpair.eventually (eventually_lt_nhds hpairr)
  obtain ⟨k, hklo, hkhi, hkbound⟩ := (hlo.and (hhi.and hbound)).exists
  exact (not_lt_of_ge (hklo.le.trans hkbound)) hkhi

/-- Positive cap weight and a finite energy-mass bound imply actual whole-space integrability. -/
theorem integrable_globalVectorDirichletObservation_of_energyMass_le
    {κ b : ℝ} (hκ : 0 < κ) (U : H)
    (hbound : vectorDirichletEnergyMass κ U ≤ ENNReal.ofReal b) :
    Integrable (globalVectorDirichletObservation U : X → V) := by
  have hc : ENNReal.ofReal κ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hκ
  have hm : ENNReal.ofReal κ * (∫⁻ x, ‖globalVectorDirichletObservation U x‖ₑ) ≤
      ENNReal.ofReal b := (le_add_of_nonneg_left zero_le).trans hbound
  have hfin : (∫⁻ x, ‖globalVectorDirichletObservation U x‖ₑ) ≠ ⊤ := by
    intro ht
    have hmul := ENNReal.mul_eq_top.mpr (Or.inl ⟨hc, ht⟩)
    exact ENNReal.ofReal_ne_top (top_unique (hmul ▸ hm))
  exact ⟨Lp.aestronglyMeasurable _, hasFiniteIntegral_iff_enorm.mpr hfin.lt_top⟩

/-- Actual finite energy-mass balances pass to a genuine weak limit as a real inequality. -/
theorem vectorDirichlet_energy_mass_le_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {κ : ℝ} (hκ : 0 < κ) {U : ι → H} {Ulimit : H}
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (ℓ : H →L[ℝ] ℝ)
    (hU : ∀ᶠ k in l, Integrable (globalVectorDirichletObservation (U k) : X → V))
    (heq : ∀ᶠ k in l, vectorDirichletEnergy (U k) +
      κ * ∫ x, ‖globalVectorDirichletObservation (U k) x‖ = ℓ (U k)) :
    Integrable (globalVectorDirichletObservation Ulimit : X → V) ∧
      vectorDirichletEnergy Ulimit + κ * ∫ x, ‖globalVectorDirichletObservation Ulimit x‖ ≤
        ℓ Ulimit := by
  have he : ∀ᶠ k in l, vectorDirichletEnergyMass κ (U k) ≤ ENNReal.ofReal (ℓ (U k)) := by
    filter_upwards [hU, heq] with k hkint hkeq
    rw [vectorDirichletEnergyMass_of_integrable hκ.le (U k) hkint, hkeq]
  have hb := vectorDirichletEnergyMass_le_of_weak_tendsto κ hUt ℓ he
  have hi := integrable_globalVectorDirichletObservation_of_energyMass_le hκ Ulimit hb
  have hpair : Tendsto (fun k ↦ ℓ (U k)) l (𝓝 (ℓ Ulimit)) :=
    (ℓ.continuous_comp_toWeakSpace_symm.tendsto _).comp hUt
  have hp0 : 0 ≤ ℓ Ulimit := ge_of_tendsto hpair (heq.mono fun k hk ↦ by
    rw [← hk]
    exact add_nonneg (vectorDirichletEnergy_nonneg _)
      (mul_nonneg hκ.le (integral_nonneg (fun _ ↦ norm_nonneg _))))
  refine ⟨hi, ?_⟩
  rw [vectorDirichletEnergyMass_of_integrable hκ.le Ulimit hi] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hp0).mp hb

end PartialBalayage.Linear
