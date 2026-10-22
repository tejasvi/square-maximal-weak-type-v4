/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpEnergyMassExhaustion
public import PartialBalayage.Linear.WeakDirichletComplementarity

/-!
# Actual jump energy and full mass under weak convergence

The genuine squared increment norm is convex and weakly lower semicontinuous.
The actual whole-space value observation carries the full mass semicontinuity.
Their sum retains true finite obstacle balances as a real limit inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open PartialBalayage.Linear
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual stable energy is convex on the genuine singular graph. -/
theorem convexOn_stableJumpForm_self (α : ℝ) :
    ConvexOn ℝ univ (fun U : StableJumpEnergySpace α ↦ stableJumpForm α U U) := by
  have hp := (convexOn_norm («E» := PiLp 2 (fun _ : Fin 2 ↦
    Lp ℝ 2 (spatialJumpMeasure α))) convex_univ).pow (fun x _ ↦ norm_nonneg x) 2
  have h := hp.comp_linearMap (stableJumpData α).toLinearMap
  convert! h using 1
  ext U
  exact stableJumpForm_self α U

/-- The actual stable energy is continuous for the genuine graph norm. -/
theorem continuous_stableJumpForm_self (α : ℝ) :
    Continuous (fun U : StableJumpEnergySpace α ↦ stableJumpForm α U U) :=
  ((stableJumpData α).continuous.norm.pow 2).congr
    (fun U ↦ (stableJumpForm_self α U).symm)

/-- The actual stable energy is lower semicontinuous for genuine weak graph limits. -/
theorem lowerSemicontinuous_stableJumpForm_self_weak (α : ℝ) :
    LowerSemicontinuous ((fun U : StableJumpEnergySpace α ↦ stableJumpForm α U U) ∘
      (toWeakSpace ℝ (StableJumpEnergySpace α)).symm) :=
  (convexOn_stableJumpForm_self α).lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_stableJumpForm_self α).lowerSemicontinuous

/-- The actual full mass of a jump state's represented value is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_stableJumpValue_mass_weak (α : ℝ) :
    LowerSemicontinuous (fun U : WeakSpace ℝ (StableJumpEnergySpace α) ↦
      ∫⁻ x : E, ‖stableJumpValue α ((toWeakSpace ℝ _).symm U) x‖ₑ) := by
  have h := (lowerSemicontinuous_lintegral_norm_weak
    («E» := ℝ) (μ := (volume : Measure E))).comp (continuous_weakMap (stableJumpValue α))
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h

/-- The genuine extended stable energy plus the original cap-weighted full mass. -/
def stableJumpEnergyMass (α κ : ℝ) (U : StableJumpEnergySpace α) : ℝ≥0∞ :=
  ENNReal.ofReal (stableJumpForm α U U) +
    ENNReal.ofReal κ * ∫⁻ x : E, ‖stableJumpValue α U x‖ₑ

/-- The true stable energy and full state mass are jointly weakly lower semicontinuous. -/
theorem lowerSemicontinuous_stableJumpEnergyMass_weak (α κ : ℝ) :
    LowerSemicontinuous (stableJumpEnergyMass α κ ∘
      (toWeakSpace ℝ (StableJumpEnergySpace α)).symm) := by
  apply LowerSemicontinuous.add
  · exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous
      (lowerSemicontinuous_stableJumpForm_self_weak α)
      (fun _ _ h ↦ ENNReal.ofReal_le_ofReal h)
  · exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      (lowerSemicontinuous_stableJumpValue_mass_weak α) (fun _ _ h ↦ mul_le_mul_right h _)

/-- For a genuine L¹ state, the extended functional is the original real energy-mass sum. -/
theorem stableJumpEnergyMass_of_integrable {κ : ℝ} (hκ : 0 ≤ κ) (α : ℝ)
    (U : StableJumpEnergySpace α) (hu : Integrable (stableJumpValue α U : E → ℝ) volume) :
    stableJumpEnergyMass α κ U = ENNReal.ofReal (stableJumpForm α U U +
      κ * ∫ x : E, ‖stableJumpValue α U x‖) := by
  rw [stableJumpEnergyMass, ← ofReal_integral_norm_eq_lintegral_enorm hu,
    ← ENNReal.ofReal_mul hκ,
    ENNReal.ofReal_add (by rw [stableJumpForm_self]; positivity)
      (mul_nonneg hκ (integral_nonneg (fun _ ↦ norm_nonneg _)))]

set_option maxHeartbeats 600000 in
/-- True finite extended energy-mass inequalities pass to a genuine cofinal weak limit. -/
theorem stableJumpEnergyMass_le_of_weak_tendsto {α : ℝ} {ι : Type*}
    {l : Filter ι} [l.NeBot] (κ : ℝ) {U : ι → StableJumpEnergySpace α}
    {Ulimit : StableJumpEnergySpace α}
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (L : StableJumpEnergySpace α →L[ℝ] ℝ)
    (hbound : ∀ᶠ k in l, stableJumpEnergyMass α κ (U k) ≤ ENNReal.ofReal (L (U k))) :
    stableJumpEnergyMass α κ Ulimit ≤ ENNReal.ofReal (L Ulimit) := by
  have hpair : Tendsto (fun k ↦ ENNReal.ofReal (L (U k))) l
      (𝓝 (ENNReal.ofReal (L Ulimit))) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ENNReal.continuous_ofReal.tendsto _ |>.comp
        ((L.continuous_comp_toWeakSpace_symm.tendsto _).comp hUt)
  by_contra hn
  obtain ⟨r, hpairr, hrenergy⟩ := exists_between (lt_of_not_ge hn)
  have hlo : ∀ᶠ k in l, r < stableJumpEnergyMass α κ (U k) :=
    hUt.eventually ((lowerSemicontinuous_stableJumpEnergyMass_weak α κ)
      (toWeakSpace ℝ _ Ulimit) r hrenergy)
  have hhi : ∀ᶠ k in l, ENNReal.ofReal (L (U k)) < r :=
    hpair.eventually (eventually_lt_nhds hpairr)
  obtain ⟨k, hklo, hkhi, hkbound⟩ := (hlo.and (hhi.and hbound)).exists
  exact (not_lt_of_ge (hklo.le.trans hkbound)) hkhi

set_option maxHeartbeats 600000 in
/-- True finite energy-mass equalities give the actual real inequality at an L¹ weak limit. -/
theorem stableJump_energy_mass_le_of_weak_tendsto {α : ℝ} {ι : Type*}
    {l : Filter ι} [l.NeBot] {κ : ℝ} (hκ : 0 ≤ κ)
    {U : ι → StableJumpEnergySpace α} {Ulimit : StableJumpEnergySpace α}
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (L : StableJumpEnergySpace α →L[ℝ] ℝ)
    (hu : Integrable (stableJumpValue α Ulimit : E → ℝ) volume)
    (hi : ∀ᶠ k in l, Integrable (stableJumpValue α (U k) : E → ℝ) volume)
    (heq : ∀ᶠ k in l, stableJumpForm α (U k) (U k) +
      κ * (∫ x : E, ‖stableJumpValue α (U k) x‖) = L (U k)) :
    stableJumpForm α Ulimit Ulimit +
      κ * (∫ x : E, ‖stableJumpValue α Ulimit x‖) ≤ L Ulimit := by
  have hb : stableJumpEnergyMass α κ Ulimit ≤ ENNReal.ofReal (L Ulimit) := by
    apply stableJumpEnergyMass_le_of_weak_tendsto κ hUt L
    filter_upwards [hi, heq] with k hik hek
    rw [stableJumpEnergyMass_of_integrable hκ α (U k) hik, hek]
  have hpair : Tendsto (fun k ↦ L (U k)) l (𝓝 (L Ulimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (L.continuous_comp_toWeakSpace_symm.tendsto _).comp hUt
  have hp : 0 ≤ L Ulimit := ge_of_tendsto hpair (by
    filter_upwards [heq] with k hk
    rw [← hk, stableJumpForm_self]
    positivity)
  rw [stableJumpEnergyMass_of_integrable hκ α Ulimit hu] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hp).mp hb

end PartialBalayage.Maximal.Square
