/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpBallUniformBounds
public import PartialBalayage.Maximal.HeatKernel
public import PartialBalayage.Maximal.SemigroupTimeContinuity
public import PartialBalayage.Linear.JointWeakCompactness
public import PartialBalayage.Linear.ScalarStateExhaustion
public import PartialBalayage.Linear.WholeSpaceL1Norm

/-!
# Genuine weighted joint weak compactness for expanding jump obstacles

A fixed strictly positive Gaussian probability density provides one finite
measure for the capped finite-ball densities. Actual state bounds come from the
physical jump Nash inequality. Joint compactness therefore uses genuine bounded
states and densities, while global state mass passes by weak lower semicontinuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual fixed heat density used solely to select a joint weak limit. -/
def jumpExhaustionWeight (x : E) : ℝ := heatKernel 2 1 x

/-- The fixed genuine Gaussian probability measure for capped densities. -/
def jumpExhaustionMeasure : Measure E :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (jumpExhaustionWeight x))

theorem jumpExhaustionWeight_pos (x : E) : 0 < jumpExhaustionWeight x :=
  heatKernel_pos 2 (by norm_num) x

theorem continuous_jumpExhaustionWeight : Continuous jumpExhaustionWeight :=
  continuous_heatKernel_space 2 1

/-- The fixed measure is a genuine probability measure. -/
theorem jumpExhaustionMeasure_univ : jumpExhaustionMeasure univ = 1 := by
  unfold jumpExhaustionMeasure jumpExhaustionWeight
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel 2 (by norm_num))
      (Eventually.of_forall (fun x ↦ (jumpExhaustionWeight_pos x).le)),
    integral_heatKernel 2 (by norm_num)]
  norm_num

instance : IsProbabilityMeasure jumpExhaustionMeasure := ⟨jumpExhaustionMeasure_univ⟩

/-- Strict positivity makes the weighted and ordinary volume almost-everywhere notions equal. -/
theorem ae_jumpExhaustionMeasure_iff (p : E → Prop) :
    (∀ᵐ x ∂jumpExhaustionMeasure, p x) ↔ ∀ᵐ x ∂volume, p x := by
  unfold jumpExhaustionMeasure
  rw [ae_withDensity_iff continuous_jumpExhaustionWeight.measurable.ennreal_ofReal]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le,
    jumpExhaustionWeight_pos, true_implies]

/-- The actual fixed heat weight is bounded by its value at the origin. -/
theorem jumpExhaustionWeight_le_zero (x : E) :
    jumpExhaustionWeight x ≤ jumpExhaustionWeight 0 := by
  unfold jumpExhaustionWeight heatKernel
  simp only [norm_zero, zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  have he : Real.exp (-‖x‖ ^ 2 / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  exact mul_le_of_le_one_right (by positivity) he

/-- The genuine weighted measure is dominated by a finite multiple of volume. -/
theorem jumpExhaustionMeasure_le_smul_volume :
    jumpExhaustionMeasure ≤ ENNReal.ofReal (jumpExhaustionWeight 0) • volume := by
  unfold jumpExhaustionMeasure
  rw [← withDensity_const]
  apply withDensity_mono
  exact Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal (jumpExhaustionWeight_le_zero x)

/-- The actual volume L² representative viewed in the fixed weighted L² space. -/
def jumpWeightedL2CLM : Lp ℝ 2 (volume : Measure E) →L[ℝ]
    Lp ℝ 2 jumpExhaustionMeasure :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top jumpExhaustionMeasure_le_smul_volume

theorem jumpWeightedL2CLM_ae (f : Lp ℝ 2 (volume : Measure E)) :
    (jumpWeightedL2CLM f : E → ℝ) =ᵐ[volume] f := by
  apply (ae_jumpExhaustionMeasure_iff _).mp
  exact Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- The genuine capped volume density has a uniform weighted cap and weighted mass. -/
theorem jumpWeightedL2CLM_mem_normMassCap {κ : ℝ≥0}
    (ν : Lp ℝ 2 (volume : Measure E)) (hν : ν ∈ normCap volume (κ : ℝ)) :
    jumpWeightedL2CLM ν ∈ normMassCap jumpExhaustionMeasure κ κ := by
  have hcap : ∀ᵐ x ∂jumpExhaustionMeasure, ‖jumpWeightedL2CLM ν x‖ ≤ (κ : ℝ) := by
    apply (ae_jumpExhaustionMeasure_iff _).mpr
    filter_upwards [hν, jumpWeightedL2CLM_ae ν] with x hx he
    rwa [he]
  refine ⟨hcap, ?_⟩
  calc
    _ ≤ ∫⁻ _ : E, (κ : ℝ≥0∞) ∂jumpExhaustionMeasure := by
      apply lintegral_mono_ae
      filter_upwards [hcap] with x hx
      simpa only [← ofReal_norm, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hx
    _ = _ := by simp

/-- Genuine global state L¹ bounds pass to weak jump-graph limits by actual value observation. -/
theorem integrable_stableJumpValue_of_weak_limit_bound {α B : ℝ} (hB : 0 ≤ B)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → StableJumpEnergySpace α} {Ulimit : StableJumpEnergySpace α}
    (ht : Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ Ulimit)))
    (hi : ∀ᶠ k in l, Integrable (stableJumpValue α (U k) : E → ℝ) volume)
    (hm : ∀ᶠ k in l, (∫ x : E, ‖stableJumpValue α (U k) x‖) ≤ B) :
    Integrable (stableJumpValue α Ulimit : E → ℝ) volume ∧
      (∫ x : E, ‖stableJumpValue α Ulimit x‖) ≤ B := by
  have hv : Tendsto (fun k ↦ toWeakSpace ℝ _ (stableJumpValue α (U k))) l
      (𝓝 (toWeakSpace ℝ _ (stableJumpValue α Ulimit))) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((continuous_weakMap (stableJumpValue α)).tendsto (toWeakSpace ℝ _ Ulimit)).comp ht
  have hmem : ∀ᶠ k in l, toWeakSpace ℝ _ (stableJumpValue α (U k)) ∈
      {v : WeakSpace ℝ (Lp ℝ 2 (volume : Measure E)) |
        ∫⁻ x, ‖((toWeakSpace ℝ _).symm v) x‖ₑ ≤ ENNReal.ofReal B} := by
    filter_upwards [hi, hm] with k hik hmk
    simp only [LinearEquiv.symm_apply_apply]
    rw [← ofReal_integral_norm_eq_lintegral_enorm hik]
    exact ENNReal.ofReal_le_ofReal hmk
  have hmass : (∫⁻ x, ‖stableJumpValue α Ulimit x‖ₑ) ≤ ENNReal.ofReal B := by
    simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
      (isClosed_lintegral_norm_sublevel_weak («E» := ℝ) (μ := (volume : Measure E))
        (ENNReal.ofReal B)).mem_of_tendsto hv hmem
  have hUint : Integrable (stableJumpValue α Ulimit : E → ℝ) volume :=
    ⟨Lp.aestronglyMeasurable _,
      hasFiniteIntegral_iff_enorm.mpr (hmass.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hUint, ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hUint] at hmass
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hmass

set_option maxHeartbeats 800000 in
/-- Actual positive finite jump obstacles have a genuine joint cofinal weak limit, with
nonnegative state and capped density and true whole-space state integrability. -/
theorem exists_positive_stableJumpBall_joint_weak_limit {α : ℝ}
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
            ν k x = (κ : ℝ))) ∧
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
  exact fun k ↦ ⟨hν k, hpde k, hcomp k⟩

end PartialBalayage.Maximal.Square
