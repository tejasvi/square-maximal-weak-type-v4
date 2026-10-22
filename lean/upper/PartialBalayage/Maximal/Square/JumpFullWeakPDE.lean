/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpSupportedPairing

/-!
# The genuine whole-space weak equation on all jump-energy tests

Actual supported L² dual tests retain the finite equations under joint weak
convergence. Genuine strong cutoff approximation then permits every energy
test, including the original limiting state itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Ω" k => closedBall (0 : E) ((k : ℝ) + 1)

private theorem finite_jump_pairing (k : ℕ) (α : ℝ)
    (f : Lp ℝ 2 (volume : Measure E)) (ν : Lp ℝ 2 (volume.restrict (Ω k)))
    (W : StableJumpDirichletSpace α (Ω k)) :
    ⟪restrictL2CLM (Ω k) f - ν, stableJumpDirichletValue α (Ω k) W⟫ =
      ⟪f, stableJumpValue α W.val⟫ -
        ⟪zeroExtendL2 measurableSet_closedBall ν, stableJumpValue α W.val⟫ := by
  rw [inner_sub_left]
  have he := stableJumpBall_globalValue_eq_zeroExtend α ((k : ℝ) + 1) W
  change stableJumpValue α W.val =
    zeroExtendL2 measurableSet_closedBall (stableJumpDirichletValue α (Ω k) W) at he
  have h1 : ⟪restrictL2CLM (Ω k) f, stableJumpDirichletValue α (Ω k) W⟫ =
      ⟪f, stableJumpValue α W.val⟫ := by
    rw [he, inner_global_zeroExtendL2]
  have h2 : ⟪ν, stableJumpDirichletValue α (Ω k) W⟫ =
      ⟪zeroExtendL2 measurableSet_closedBall ν, stableJumpValue α W.val⟫ := by
    rw [real_inner_comm (stableJumpValue α W.val) (zeroExtendL2 measurableSet_closedBall ν),
      inner_global_zeroExtendL2, real_inner_comm]
    rfl
  rw [h1, h2]

set_option maxHeartbeats 600000 in
/-- Genuine finite equations pass to every actual compactly supported jump-energy test. -/
theorem stableJump_supported_equation_of_joint_limit {α : ℝ}
    (ν : (k : ℕ) → Lp ℝ 2 (volume.restrict (Ω k)))
    (U : (k : ℕ) → StableJumpDirichletSpace α (Ω k))
    (f : Lp ℝ 2 (volume : Measure E))
    (νlimit : Lp ℝ 2 jumpExhaustionMeasure) (Ulimit : StableJumpEnergySpace α)
    (hpde : ∀ k : ℕ, ∀ W : StableJumpDirichletSpace α (Ω k),
      stableJumpForm α (U k).val W.val =
        ⟪restrictL2CLM (Ω k) f - ν k, stableJumpDirichletValue α (Ω k) W⟫)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (jumpWeightedL2CLM
      (zeroExtendL2 measurableSet_closedBall (ν k)))) l (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k).val) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (V : StableJumpEnergySpace α) {S : Set E} (hS : IsCompact S)
    (hVs : V ∈ stableJumpSupported α S) :
    stableJumpForm α Ulimit V = ⟪f, stableJumpValue α V⟫ -
      ∫ x : E, νlimit x * stableJumpValue α V x := by
  have hVzero := (mem_stableJumpSupported_iff α hS.measurableSet V).mp hVs
  let T := jumpWeightedSupportedTest (stableJumpValue α V) hS hVzero
  let Lν : Lp ℝ 2 jumpExhaustionMeasure →L[ℝ] ℝ := innerSL ℝ T
  let LU : StableJumpEnergySpace α →L[ℝ] ℝ :=
    (innerSL ℝ (stableJumpData α V)).comp (stableJumpData α)
  have hLν (v : Lp ℝ 2 jumpExhaustionMeasure) :
      Lν v = ∫ x : E, v x * stableJumpValue α V x := by
    change ⟪jumpWeightedSupportedTest (stableJumpValue α V) hS hVzero, v⟫ = _
    rw [real_inner_comm, inner_jumpWeightedSupportedTest_eq_integral]
  have hLU (W : StableJumpEnergySpace α) : LU W = stableJumpForm α W V := by
    change ⟪stableJumpData α V, stableJumpData α W⟫ =
      ⟪stableJumpData α W, stableJumpData α V⟫
    exact real_inner_comm _ _
  have hcontained : ∀ᶠ k : ℕ in atTop, S ⊆ Ω k :=
    (eventually_compact_subset_expanding_balls hS).mono
      (fun _ hk ↦ hk.trans ball_subset_closedBall)
  have heq : ∀ᶠ k in l, LU (U k).val = ⟪f, stableJumpValue α V⟫ -
      Lν (jumpWeightedL2CLM (zeroExtendL2 measurableSet_closedBall (ν k))) := by
    filter_upwards [hcontained.filter_mono hl] with k hk
    have hVk : V ∈ stableJumpSupported α (Ω k) := by
      rw [mem_stableJumpSupported_iff α measurableSet_closedBall]
      filter_upwards [hVzero] with x hx
      exact fun hxo ↦ hx (fun hxs ↦ hxo (hk hxs))
    let W : StableJumpDirichletSpace α (Ω k) := ⟨V, hVk⟩
    rw [hLU, hpde k W, finite_jump_pairing, hLν]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [jumpWeightedL2CLM_ae
      (zeroExtendL2 measurableSet_closedBall (ν k))] with x hx
    simp only [Real.inner_apply, hx]
    rfl
  have hνeval : Tendsto (fun k ↦ Lν (jumpWeightedL2CLM
      (zeroExtendL2 measurableSet_closedBall (ν k)))) l (𝓝 (Lν νlimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (Lν.continuous_comp_toWeakSpace_symm.tendsto (toWeakSpace ℝ _ νlimit)).comp hνt
  have hUeval : Tendsto (fun k ↦ LU (U k).val) l (𝓝 (LU Ulimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (LU.continuous_comp_toWeakSpace_symm.tendsto (toWeakSpace ℝ _ Ulimit)).comp hUt
  have he := tendsto_nhds_unique_of_eventuallyEq hUeval
    (tendsto_const_nhds.sub hνeval) heq
  simpa only [hLU, hLν] using he

set_option maxHeartbeats 600000 in
/-- Genuine joint weak limits with ordinary L² density satisfy the actual form equation
against every state of the full singular jump graph. -/
theorem stableJump_equation_of_joint_limit {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (ν : (k : ℕ) → Lp ℝ 2 (volume.restrict (Ω k)))
    (U : (k : ℕ) → StableJumpDirichletSpace α (Ω k))
    (f v : Lp ℝ 2 (volume : Measure E))
    (νlimit : Lp ℝ 2 jumpExhaustionMeasure) (Ulimit : StableJumpEnergySpace α)
    (hv : (νlimit : E → ℝ) =ᵐ[volume] v)
    (hpde : ∀ k : ℕ, ∀ W : StableJumpDirichletSpace α (Ω k),
      stableJumpForm α (U k).val W.val =
        ⟪restrictL2CLM (Ω k) f - ν k, stableJumpDirichletValue α (Ω k) W⟫)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (jumpWeightedL2CLM
      (zeroExtendL2 measurableSet_closedBall (ν k)))) l (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k).val) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (V : StableJumpEnergySpace α) :
    stableJumpForm α Ulimit V = ⟪f - v, stableJumpValue α V⟫ := by
  have heq (k : ℕ) : stableJumpForm α Ulimit (stableJumpLargeCutoff hα0 hα2 V k) =
      ⟪f - v, stableJumpValue α (stableJumpLargeCutoff hα0 hα2 V k)⟫ := by
    rw [stableJump_supported_equation_of_joint_limit ν U f νlimit Ulimit hpde hl hνt hUt
      (stableJumpLargeCutoff hα0 hα2 V k) (jumpSourceCutoff_hasCompactSupport k).isCompact
      (stableJumpLargeCutoff_mem_supported hα0 hα2 V k), inner_sub_left]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [Real.inner_apply, hx]
  have hleft : Tendsto (fun k : ℕ ↦
      stableJumpForm α Ulimit (stableJumpLargeCutoff hα0 hα2 V k)) atTop
        (𝓝 (stableJumpForm α Ulimit V)) := by
    exact (continuous_const.inner (stableJumpData α).continuous).tendsto V |>.comp
      (tendsto_stableJumpLargeCutoff hα0 hα2 V)
  have hright : Tendsto (fun k : ℕ ↦
      ⟪f - v, stableJumpValue α (stableJumpLargeCutoff hα0 hα2 V k)⟫) atTop
        (𝓝 ⟪f - v, stableJumpValue α V⟫) :=
    (continuous_const.inner (stableJumpValue α).continuous).tendsto V |>.comp
      (tendsto_stableJumpLargeCutoff hα0 hα2 V)
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright (Eventually.of_forall heq)

end PartialBalayage.Maximal.Square
