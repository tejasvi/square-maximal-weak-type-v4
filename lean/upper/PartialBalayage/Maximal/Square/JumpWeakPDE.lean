/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpWeightedPairing
public import PartialBalayage.Linear.ExtendedEnergyMassIdentity

/-!
# The actual whole-space coordinate-stable weak equation

The genuine finite-ball equations pass to one joint cofinal weak limit through
actual compact physical pairings. The jump form then gives the original
normalized singular-integral generator equation for every genuine compact C² test.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Ω" k => closedBall (0 : E) ((k : ℝ) + 1)

private theorem finite_jump_test_pairing (k : ℕ) (α : ℝ)
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

private def jumpDensityPairingCLM (φ : E → ℝ) (hφ : Continuous φ)
    (hs : HasCompactSupport φ) : Lp ℝ 2 jumpExhaustionMeasure →L[ℝ] ℝ :=
  innerSL ℝ (jumpWeightedTest φ hφ hs)

private theorem jumpDensityPairingCLM_apply (φ : E → ℝ) (hφ : Continuous φ)
    (hs : HasCompactSupport φ) (v : Lp ℝ 2 jumpExhaustionMeasure) :
    jumpDensityPairingCLM φ hφ hs v = ∫ x : E, v x * φ x := by
  change ⟪jumpWeightedTest φ hφ hs, v⟫ = _
  rw [real_inner_comm, inner_jumpWeightedTest_eq_integral]

private def jumpEnergyPairingCLM (α : ℝ) (V : StableJumpEnergySpace α) :
    StableJumpEnergySpace α →L[ℝ] ℝ :=
  (innerSL ℝ (stableJumpData α V)).comp (stableJumpData α)

private theorem jumpEnergyPairingCLM_apply (α : ℝ) (V W : StableJumpEnergySpace α) :
    jumpEnergyPairingCLM α V W = stableJumpForm α W V := by
  change ⟪stableJumpData α V, stableJumpData α W⟫ =
    ⟪stableJumpData α W, stableJumpData α V⟫
  exact real_inner_comm _ _

set_option maxHeartbeats 600000 in
private theorem jumpForm_equation_of_joint_tendsto {α : ℝ}
    {ν : ℕ → Lp ℝ 2 jumpExhaustionMeasure} {U : ℕ → StableJumpEnergySpace α}
    {νlimit : Lp ℝ 2 jumpExhaustionMeasure} {Ulimit : StableJumpEnergySpace α}
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (V : StableJumpEnergySpace α) (b : ℝ)
    (heq : ∀ᶠ k in atTop, stableJumpForm α (U k) V = b - ∫ x : E, ν k x * φ x) :
    stableJumpForm α Ulimit V = b - ∫ x : E, νlimit x * φ x := by
  have hνeval : Tendsto (fun k ↦ jumpDensityPairingCLM φ hφ hs (ν k)) l
      (𝓝 (jumpDensityPairingCLM φ hφ hs νlimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((jumpDensityPairingCLM φ hφ hs).continuous_comp_toWeakSpace_symm.tendsto
        (toWeakSpace ℝ _ νlimit)).comp hνt
  have hUeval : Tendsto (fun k ↦ jumpEnergyPairingCLM α V (U k)) l
      (𝓝 (jumpEnergyPairingCLM α V Ulimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((jumpEnergyPairingCLM α V).continuous_comp_toWeakSpace_symm.tendsto
        (toWeakSpace ℝ _ Ulimit)).comp hUt
  have he : jumpEnergyPairingCLM α V Ulimit = b - jumpDensityPairingCLM φ hφ hs νlimit :=
    tendsto_nhds_unique_of_eventuallyEq hUeval (tendsto_const_nhds.sub hνeval)
      (by
        filter_upwards [heq.filter_mono hl] with k hk
        simpa only [jumpEnergyPairingCLM_apply, jumpDensityPairingCLM_apply] using hk)
  simpa only [jumpEnergyPairingCLM_apply, jumpDensityPairingCLM_apply] using he

set_option maxHeartbeats 600000 in
/-- Genuine finite equations pass through actual weighted-density and jump-state weak limits. -/
theorem stableJump_test_equation_of_joint_limit {α : ℝ}
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
    (φ : E → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (V : StableJumpEnergySpace α) (hV : (stableJumpValue α V : E → ℝ) =ᵐ[volume] φ)
    (hVs : ∀ S : Set E, MeasurableSet S → tsupport φ ⊆ S →
      V ∈ stableJumpSupported α S) :
    stableJumpForm α Ulimit V = ∫ x : E, (f x - νlimit x) * φ x := by
  have hcontained : ∀ᶠ k : ℕ in atTop, tsupport φ ⊆ Ω k :=
    (eventually_compact_subset_expanding_balls hs.isCompact).mono
      (fun _ hk ↦ hk.trans ball_subset_closedBall)
  have heq : ∀ᶠ k in atTop, stableJumpForm α (U k).val V =
      ⟪f, stableJumpValue α V⟫ - ∫ x : E,
        jumpWeightedL2CLM (zeroExtendL2 measurableSet_closedBall (ν k)) x * φ x := by
    filter_upwards [hcontained] with k hk
    let W : StableJumpDirichletSpace α (Ω k) :=
      ⟨V, hVs (Ω k) measurableSet_closedBall hk⟩
    rw [hpde k W, finite_jump_test_pairing]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hV, jumpWeightedL2CLM_ae
      (zeroExtendL2 measurableSet_closedBall (ν k))] with x hx he
    simp only [Real.inner_apply]
    dsimp only [W]
    rw [hx, he]
  have he := jumpForm_equation_of_joint_tendsto hl hνt hUt φ hφ hs V
    ⟪f, stableJumpValue α V⟫ heq
  rw [L2.inner_def] at he
  have hif : Integrable (fun x : E ↦ f x * φ x) volume := by
    have hi : Integrable (fun x : E ↦ f x * stableJumpValue α V x) volume :=
      (Lp.memLp f).integrable_mul (Lp.memLp (stableJumpValue α V))
    apply hi.congr
    filter_upwards [hV] with x hx
    rw [hx]
  have hinu := integrable_weightedDensity_mul_compactTest νlimit φ hφ hs
  have hfV : (∫ x : E, ⟪f x, stableJumpValue α V x⟫) = ∫ x : E, f x * φ x := by
    apply integral_congr_ae
    filter_upwards [hV] with x hx
    simp only [Real.inner_apply, hx]
  rw [hfV] at he
  have hint := integral_sub hif hinu
  rw [he, ← hint]
  congr 1
  funext x
  ring

set_option maxHeartbeats 800000 in
/-- Nonnegative L² input admits an actual global positive jump state and capped nonnegative
weighted density satisfying the original physical equation on every genuine compact C² test. -/
theorem exists_positive_stableJumpCompactWeak_solution {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (κ : ℝ≥0) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : ∀ᵐ x, 0 ≤ f x) :
    ∃ (ν : Lp ℝ 2 jumpExhaustionMeasure) (U : StableJumpEnergySpace α),
      (∀ᵐ x ∂volume, 0 ≤ ν x ∧ ν x ≤ (κ : ℝ)) ∧
      (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α U x) ∧
      Integrable (stableJumpValue α U : E → ℝ) volume ∧
      (∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        (∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) =
          ∫ x : E, (ν x - f x) * φ x) := by
  obtain ⟨ν, U, νlimit, Ulimit, l, hdata, hνbound, hUpos, hUint, hlne, hl, hνt, hUt⟩ :=
    exists_positive_stableJumpBall_joint_weak_limit hα0 hα2 κ hκ f hf
  let : l.NeBot := hlne
  refine ⟨νlimit, Ulimit, hνbound, hUpos, hUint, ?_⟩
  intro φ hφ hs
  obtain ⟨V, hV, hVs⟩ := exists_stableJumpCompactC1Test hα0 hα2 (hφ.of_le (by norm_num)) hs
  have he := stableJump_test_equation_of_joint_limit ν U f νlimit Ulimit
    (fun k ↦ (hdata k).2.1) hl hνt hUt φ hφ.continuous hs V hV hVs
  rw [stableJumpForm_eq_neg_integral_coordinateStableGenerator
    hα0 hα2 Ulimit V hUint φ hφ hs hV] at he
  calc
    _ = -(∫ x : E, (f x - νlimit x) * φ x) := by linarith
    _ = _ := by
      rw [← integral_neg]
      congr 1
      funext x
      ring

end PartialBalayage.Maximal.Square
