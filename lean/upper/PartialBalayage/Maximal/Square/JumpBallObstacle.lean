/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpDirichletSpace
public import PartialBalayage.Linear.ScalarIntervalCap
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# The actual positive stable obstacle on a ball

The true singular coordinate-jump form defines a positive coercive bounded operator on
its complete zero-exterior Hilbert space. The actual interval-cap variational problem
therefore constructs a nonnegative capped density. Testing its genuine state equation
with the negative part proves nonnegativity of the state. No positivity of a proposed
solution is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open PartialBalayage.Linear
open scoped RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Ω" R:arg => closedBall (0 : E) R
local notation "H" α:arg R:arg => StableJumpDirichletSpace α (Ω R)
local notation "L²" R:arg => Lp ℝ 2 (volume.restrict (Ω R))
local notation "D²" α:arg => PiLp 2 (fun _ : Fin 2 ↦ Lp ℝ 2 (spatialJumpMeasure α))

instance (α : ℝ) (S : Set E) : InnerProductSpace ℝ (StableJumpDirichletSpace α S) :=
  @Submodule.innerProductSpace ℝ (StableJumpEnergySpace α) _ _ _ (stableJumpSupported α S)

/-- The actual Riesz operator of the full singular jump form on a zero-exterior ball. -/
def stableJumpBallOperator (α R : ℝ) : H α R →L[ℝ] H α R :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) («E» := H α R) (F := D² α)
    (stableJumpDirichletData α (Ω R))) ∘L stableJumpDirichletData α (Ω R)

theorem isPositive_stableJumpBallOperator (α R : ℝ) :
    ContinuousLinearMap.IsPositive (𝕜 := ℝ) («E» := H α R) (stableJumpBallOperator α R) :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (𝕜 := ℝ) («E» := H α R) (F := D² α) _

/-- The actual Hilbert operator represents precisely the genuine jump Dirichlet form. -/
theorem inner_stableJumpBallOperator_eq (α R : ℝ) (U V : H α R) :
    ⟪stableJumpBallOperator α R U, V⟫ = stableJumpForm α U.val V.val := by
  rw [stableJumpBallOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- The concrete positive coercivity constant supplied by the genuine long-jump mass. -/
def stableJumpBallCoercivity (α R : ℝ) : ℝ :=
  (stableJumpMeasure α (longJumpBand R)).toReal /
    (1 + (stableJumpMeasure α (longJumpBand R)).toReal)

theorem stableJumpBallCoercivity_pos {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) : 0 < stableJumpBallCoercivity α R := by
  have hc := stableJumpMeasure_longJumpBand_toReal_pos hα0 hα2 hR
  exact div_pos hc (by linarith)

theorem stableJumpBallOperator_coercive {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : H α R) :
    stableJumpBallCoercivity α R * ‖U‖ ^ 2 ≤ ⟪stableJumpBallOperator α R U, U⟫ := by
  rw [inner_stableJumpBallOperator_eq]
  exact stableJumpForm_ball_coercive hα0 hα2 hR U

/-- The genuine negative-part test is the actual negative part of the global value class. -/
theorem stableJumpDirichletNegativePart_globalValue_ae (α R : ℝ) (U : H α R) :
    (stableJumpDirichletGlobalValue α (Ω R)
      (stableJumpDirichletNegativePart α measurableSet_closedBall U) : E → ℝ) =ᵐ[volume]
        fun x ↦ max (-stableJumpDirichletGlobalValue α (Ω R) U x) 0 :=
  lipschitzWith_negative_part.coeFn_compLp (by simp) (stableJumpValue α U.val)

/-- Restriction of the actual negative-part test agrees with the negative part on the ball. -/
theorem stableJumpDirichletNegativePart_value_ae (α R : ℝ) (U : H α R) :
    (stableJumpDirichletValue α (Ω R)
      (stableJumpDirichletNegativePart α measurableSet_closedBall U) : E → ℝ)
        =ᵐ[volume.restrict (Ω R)]
      fun x ↦ max (-stableJumpDirichletValue α (Ω R) U x) 0 := by
  filter_upwards [restrictL2CLM_ae (Ω R) (stableJumpDirichletGlobalValue α (Ω R) U),
    restrictL2CLM_ae (Ω R) (stableJumpDirichletGlobalValue α (Ω R)
      (stableJumpDirichletNegativePart α measurableSet_closedBall U)),
    ae_restrict_of_ae (stableJumpDirichletNegativePart_globalValue_ae α R U)]
    with x hU hN hx
  exact hN.trans (hx.trans (congrArg (fun r : ℝ ↦ max (-r) 0) hU.symm))

/-- Testing the actual stable equation with the genuine negative part removes it. -/
theorem ae_nonneg_of_stableJumpBall_weak_equation {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : H α R) (f ν : L² R)
    (hf : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ f x)
    (hν : ∀ᵐ x ∂volume.restrict (Ω R),
      stableJumpDirichletValue α (Ω R) U x < 0 → ν x ≤ 0)
    (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫) :
    ∀ᵐ x, 0 ≤ stableJumpDirichletGlobalValue α (Ω R) U x := by
  let N := stableJumpDirichletNegativePart α measurableSet_closedBall U
  have hp : 0 ≤ ⟪f - ν, stableJumpDirichletValue α (Ω R) N⟫ := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hν, stableJumpDirichletNegativePart_value_ae α R U,
      Lp.coeFn_sub f ν] with x hfx hνx hnx hs
    change stableJumpDirichletValue α (Ω R) N x = _ at hnx
    simp only [Real.inner_apply, hs, Pi.sub_apply, hnx, Pi.zero_apply]
    by_cases hu : stableJumpDirichletValue α (Ω R) U x < 0
    · exact mul_nonneg (sub_nonneg.mpr ((hνx hu).trans hfx)) (le_max_right _ _)
    · rw [max_eq_right (neg_nonpos.mpr (not_lt.mp hu)), mul_zero]
  have hm : stableJumpForm α U.val N.val ≤ -stableJumpForm α N.val N.val :=
    stableJumpForm_negativePart_le α U.val
  have hn : stableJumpForm α N.val N.val ≤ 0 := by
    rw [hpde N] at hm
    linarith
  have hc := stableJumpBallCoercivity_pos hα0 hα2 hR
  have hco := stableJumpForm_ball_coercive hα0 hα2 hR N
  have hzero : N = 0 := by
    have hsq : ‖N‖ ^ 2 ≤ 0 := (mul_le_mul_iff_of_pos_left hc).mp
      (by simpa only [stableJumpBallCoercivity, mul_zero] using hco.trans hn)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))
  have hvalue : stableJumpDirichletGlobalValue α (Ω R) N = 0 :=
    (congrArg (stableJumpDirichletGlobalValue α (Ω R)) hzero).trans
      (stableJumpDirichletGlobalValue α (Ω R)).toLinearMap.map_zero
  filter_upwards [stableJumpDirichletNegativePart_globalValue_ae α R U,
    Lp.coeFn_zero ℝ 2 (volume : Measure E)] with x hx hz
  change stableJumpDirichletGlobalValue α (Ω R) N x = _ at hx
  rw [hvalue, hz, Pi.zero_apply] at hx
  have hle := le_max_left (-stableJumpDirichletGlobalValue α (Ω R) U x) 0
  rw [← hx] at hle
  exact neg_nonpos.mp hle

set_option maxHeartbeats 600000 in
/-- The true stable ball obstacle exists with a positive state and positive capped density. -/
theorem exists_positive_stableJumpBall_obstacle {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (f : L² R) (hf : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ f x)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : L² R) (U : H α R),
      (∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ ν x ∧ ν x ≤ κ) ∧
      (∀ᵐ x, 0 ≤ stableJumpDirichletGlobalValue α (Ω R) U x) ∧
      (∀ W : H α R, stableJumpForm α U.val W.val =
        ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫) ∧
      (∀ᵐ x ∂volume.restrict (Ω R),
        0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) := by
  let : IsFiniteMeasure (volume.restrict (Ω R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hc : 0 < stableJumpBallCoercivity α R :=
    stableJumpBallCoercivity_pos hα0 hα2 hR
  have hco : ∀ U : H α R,
      stableJumpBallCoercivity α R * ‖U‖ ^ 2 ≤ ⟪stableJumpBallOperator α R U, U⟫ :=
    stableJumpBallOperator_coercive hα0 hα2 hR
  obtain ⟨ν, U, hν, heq, hcomp⟩ := exists_scalarInterval_dirichlet_dual_obstacle
    («H» := H α R) (c := stableJumpBallCoercivity α R)
    (volume.restrict (Ω R)) (stableJumpBallOperator α R)
    (isPositive_stableJumpBallOperator α R) hc hco
    (stableJumpDirichletValue α (Ω R)) f hκ
  have hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫ := by
    intro W
    rw [← inner_stableJumpBallOperator_eq, heq, ContinuousLinearMap.adjoint_inner_left]
  have hsign : ∀ᵐ x ∂volume.restrict (Ω R),
      stableJumpDirichletValue α (Ω R) U x < 0 → ν x ≤ 0 := by
    filter_upwards [hcomp] with x hx
    exact fun hn ↦ (hx.2 hn).le
  exact ⟨ν, U, scalarIntervalCap_ae_bounds _ hν,
    ae_nonneg_of_stableJumpBall_weak_equation hα0 hα2 hR U f ν hf hsign hpde,
    hpde, hcomp.mono (fun _ hx ↦ hx.1)⟩

end PartialBalayage.Maximal.Square
