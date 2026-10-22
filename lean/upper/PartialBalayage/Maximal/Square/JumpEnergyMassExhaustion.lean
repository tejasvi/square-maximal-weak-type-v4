/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpFullWeakPDE

/-!
# Genuine joint exhaustion retaining the finite jump energy and mass balances

The positive finite obstacles selected by the actual uniform construction
retain their genuine energy-mass equalities in one cofinal joint weak family.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

set_option maxHeartbeats 800000 in
/-- Actual positive finite jump obstacles have a genuine joint cofinal weak limit, with
nonnegative state and capped density and true whole-space state integrability. -/
theorem exists_positive_stableJumpBall_joint_energy_limit {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (κ : ℝ≥0) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : ∀ᵐ x, 0 ≤ f x) :
    ∃ (ν : (k : ℕ) → Lp ℝ 2 (volume.restrict (closedBall (0 : E) ((k : ℝ) + 1))))
      (U : (k : ℕ) → StableJumpDirichletSpace α (closedBall (0 : E) ((k : ℝ) + 1)))
      (νlimit : Lp ℝ 2 jumpExhaustionMeasure) (Ulimit : StableJumpEnergySpace α)
      (l : Filter ℕ),
      (∀ k,
        (∀ᵐ x ∂volume.restrict (closedBall (0 : E) ((k : ℝ) + 1)),
          0 ≤ ν k x ∧ ν k x ≤ (κ : ℝ)) ∧
        (∀ W : StableJumpDirichletSpace α (closedBall (0 : E) ((k : ℝ) + 1)),
          stableJumpForm α (U k).val W.val =
            ⟪restrictL2CLM (closedBall (0 : E) ((k : ℝ) + 1)) f - ν k,
              stableJumpDirichletValue α (closedBall (0 : E) ((k : ℝ) + 1)) W⟫) ∧
        (∀ᵐ x ∂volume.restrict (closedBall (0 : E) ((k : ℝ) + 1)),
          0 < stableJumpDirichletValue α (closedBall (0 : E) ((k : ℝ) + 1)) (U k) x →
            ν k x = (κ : ℝ)) ∧
        (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α (U k).val x) ∧
        (stableJumpForm α (U k).val (U k).val + (κ : ℝ) *
          (∫ x : E, ‖stableJumpValue α (U k).val x‖) =
            ⟪f, stableJumpValue α (U k).val⟫)) ∧
      (∀ᵐ x ∂volume, 0 ≤ νlimit x ∧ νlimit x ≤ (κ : ℝ)) ∧
      (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α Ulimit x) ∧
      Integrable (stableJumpValue α Ulimit : E → ℝ) volume ∧
      l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (jumpWeightedL2CLM
        (zeroExtendL2 measurableSet_closedBall (ν k)))) l
          (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (U k).val) l (𝓝 (toWeakSpace ℝ _ Ulimit)) := by
  have hκr : 0 < (κ : ℝ) := by exact_mod_cast hκ
  obtain ⟨B, hB, hfamily⟩ :=
    exists_uniform_positive_stableJumpBall_obstacles hα0 hα2 hκr f hf
  let Ω : ℕ → Set E := fun k ↦ closedBall 0 ((k : ℝ) + 1)
  have hΩ : ∀ k, MeasurableSet (Ω k) := fun _ ↦ measurableSet_closedBall
  have hdata (k : ℕ) : ∃ (ν : Lp ℝ 2 (volume.restrict (Ω k)))
      (U : StableJumpDirichletSpace α (Ω k)),
      (∀ᵐ x ∂volume.restrict (Ω k), 0 ≤ ν x ∧ ν x ≤ (κ : ℝ)) ∧
      (∀ᵐ x, 0 ≤ stableJumpDirichletGlobalValue α (Ω k) U x) ∧
      (∀ W : StableJumpDirichletSpace α (Ω k), stableJumpForm α U.val W.val =
        ⟪restrictL2CLM (Ω k) f - ν, stableJumpDirichletValue α (Ω k) W⟫) ∧
      (∀ᵐ x ∂volume.restrict (Ω k),
        0 < stableJumpDirichletValue α (Ω k) U x → ν x = (κ : ℝ)) ∧
      ‖U‖ ≤ B ∧ (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω k) U x‖) ≤ B :=
    hfamily ((k : ℝ) + 1) (by positivity)
  choose ν U hν hUpos hpde hcomp hUB hUM using hdata
  let N : ℕ → Lp ℝ 2 (volume : Measure E) := fun k ↦ zeroExtendL2 (hΩ k) (ν k)
  let G : ℕ → StableJumpEnergySpace α := fun k ↦ (U k).val
  have hNcap (k : ℕ) : N k ∈ normCap volume (κ : ℝ) := by
    have hn : ∀ᵐ x ∂volume, x ∈ Ω k → 0 ≤ ν k x ∧ ν k x ≤ (κ : ℝ) :=
      (ae_restrict_iff' (hΩ k)).mp (hν k)
    filter_upwards [zeroExtendL2_ae (hΩ k) (ν k), hn] with x he hx
    change ‖zeroExtendL2 (hΩ k) (ν k) x‖ ≤ (κ : ℝ)
    rw [he]
    by_cases hxo : x ∈ Ω k
    · rw [indicator_of_mem hxo, Real.norm_eq_abs, abs_of_nonneg (hx hxo).1]
      exact (hx hxo).2
    · simp only [indicator_of_notMem hxo, norm_zero]
      exact κ.coe_nonneg
  have hNpos (k : ℕ) : ∀ᵐ x ∂volume, 0 ≤ N k x := by
    have hn : ∀ᵐ x ∂volume, x ∈ Ω k → 0 ≤ ν k x :=
      (ae_restrict_iff' (hΩ k)).mp ((hν k).mono (fun _ h ↦ h.1))
    filter_upwards [zeroExtendL2_ae (hΩ k) (ν k), hn] with x he hx
    change 0 ≤ zeroExtendL2 (hΩ k) (ν k) x
    rw [he]
    by_cases hxo : x ∈ Ω k
    · simpa only [indicator_of_mem hxo] using hx hxo
    · simp only [indicator_of_notMem hxo, le_refl]
  obtain ⟨νlimit, Ulimit, l, hνlimit, _, hlne, hl, hνt, hUt⟩ :=
    exists_joint_weak_filter_normMassCap κ κ B (fun k ↦ jumpWeightedL2CLM (N k)) G
      (fun k ↦ jumpWeightedL2CLM_mem_normMassCap (N k) (hNcap k)) (fun k ↦ hUB k)
  let : l.NeBot := hlne
  have hνpos : ∀ᵐ x ∂jumpExhaustionMeasure, 0 ≤ νlimit x := by
    apply ae_nonneg_of_weak_scalarLp_tendsto hνt
    apply Eventually.of_forall
    intro k
    apply (ae_jumpExhaustionMeasure_iff _).mpr
    filter_upwards [hNpos k, jumpWeightedL2CLM_ae (N k)] with x hx he
    rwa [he]
  have hνbound : ∀ᵐ x ∂volume, 0 ≤ νlimit x ∧ νlimit x ≤ (κ : ℝ) := by
    apply (ae_jumpExhaustionMeasure_iff _).mp
    filter_upwards [hνpos, hνlimit.1] with x hp hc
    rw [Real.norm_eq_abs, abs_of_nonneg hp] at hc
    exact ⟨hp, hc⟩
  have hUlimitpos : ∀ᵐ x ∂volume, 0 ≤ stableJumpValue α Ulimit x := by
    apply ae_nonneg_CLM_of_weak_tendsto (stableJumpValue α) hUt
    exact Eventually.of_forall hUpos
  have hUint : Integrable (stableJumpValue α Ulimit : E → ℝ) volume :=
    (integrable_stableJumpValue_of_weak_limit_bound hB hUt
      (Eventually.of_forall fun k ↦
        integrable_stableJumpBall_globalValue α ((k : ℝ) + 1) (U k))
      (Eventually.of_forall hUM)).1
  refine ⟨ν, U, νlimit, Ulimit, l, ?_, hνbound, hUlimitpos, hUint, hlne, hl, hνt, hUt⟩
  intro k
  have hupos : ∀ᵐ x ∂volume.restrict (Ω k),
      0 ≤ stableJumpDirichletValue α (Ω k) (U k) x := by
    have hr := restrictL2CLM_ae (Ω k) (stableJumpDirichletGlobalValue α (Ω k) (U k))
    filter_upwards [hr, ae_restrict_of_ae (hUpos k)] with x hx hp
    change 0 ≤ restrictL2CLM (Ω k) (stableJumpDirichletGlobalValue α (Ω k) (U k)) x
    rw [hx]
    exact hp
  have he := stableJumpBall_energy_mass_balance α ((k : ℝ) + 1) (U k)
    (restrictL2CLM (Ω k) f) (ν k) (hpde k) hupos (hcomp k)
  have hpair := inner_global_zeroExtendL2 (hΩ k) f
    (stableJumpDirichletValue α (Ω k) (U k))
  rw [← stableJumpBall_globalValue_eq_zeroExtend α ((k : ℝ) + 1) (U k)] at hpair
  rw [← hpair] at he
  exact ⟨hν k, hpde k, hcomp k, hUpos k, he⟩

end PartialBalayage.Maximal.Square
