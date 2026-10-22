/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TranslationJumpContact
public import PartialBalayage.Linear.WeakDirichletEnergy
public import Mathlib.Topology.Ultrafilter

/-!
# The genuine full-vector source energy graph

Actual full source increments form a closed Hilbert graph. Bounded true graph
states therefore have cofinal weak limits retaining strong value limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology Metric
open PartialBalayage.Linear
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)
local notation "J²" μ => Lp ℝ 2 (Measure.prod (volume : Measure E) μ)
local notation "H" μ => WithLp 2 (L² × J² μ)

/-- The graph of the actual full-vector source increments. -/
def translationJumpGraph (μ : Measure E) [SigmaFinite μ] : Submodule ℝ (H μ) where
  carrier := {U | ∀ᵐ p ∂volume.prod μ, U.snd p = translationJump (U.fst : E → ℝ) p}
  zero_mem' := by
    have hz := Lp.coeFn_zero ℝ 2 (volume : Measure E)
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.prod μ),
      (quasiMeasurePreserving_translationJumpPoint μ).ae hz,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hz]
        with p hj hx hy
    simp only [WithLp.zero_fst, WithLp.zero_snd, translationJump, hj, hx, hy,
      Pi.zero_apply, sub_self]
  add_mem' := by
    intro U V hU hV
    have ha := Lp.coeFn_add U.fst V.fst
    filter_upwards [hU, hV, Lp.coeFn_add U.snd V.snd,
      (quasiMeasurePreserving_translationJumpPoint μ).ae ha,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae ha]
        with p hu hv hj hx hy
    simp only [WithLp.add_fst, WithLp.add_snd, translationJump]
    rw [hj, hx, hy]
    simp only [Pi.add_apply]
    rw [hu, hv]
    unfold translationJump
    ring
  smul_mem' := by
    intro c U hU
    have hc := Lp.coeFn_smul c U.fst
    filter_upwards [hU, Lp.coeFn_smul c U.snd,
      (quasiMeasurePreserving_translationJumpPoint μ).ae hc,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hc]
        with p hu hj hx hy
    simp only [WithLp.smul_fst, WithLp.smul_snd, translationJump]
    rw [hj, hx, hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu]
    unfold translationJump
    ring

/-- The actual full-vector graph is closed over the entire infinite source measure. -/
theorem isClosed_translationJumpGraph (μ : Measure E) [SigmaFinite μ] :
    IsClosed (translationJumpGraph μ : Set (H μ)) := by
  apply IsSeqClosed.isClosed
  intro U V hU hUV
  have h0 : Tendsto (fun n ↦ (U n).fst) atTop (𝓝 V.fst) :=
    (WithLp.continuous_fst 2 L² (J² μ)).tendsto V |>.comp hUV
  obtain ⟨s, hs, h0s⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  have h1 : Tendsto (fun n ↦ (U (s n)).snd) atTop (𝓝 V.snd) :=
    (WithLp.continuous_snd 2 L² (J² μ)).tendsto V |>.comp
      (hUV.comp hs.tendsto_atTop)
  obtain ⟨r, hr, h1r⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  filter_upwards [h1r, (quasiMeasurePreserving_translationJumpPoint μ).ae h0s,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae h0s,
    ae_all_iff.mpr (fun n ↦ hU (s (r n)))] with p hp hx hy hg
  have hj := (hx.comp hr.tendsto_atTop).sub (hy.comp hr.tendsto_atTop)
  exact tendsto_nhds_unique hp
    (hj.congr' (Eventually.of_forall fun n ↦ (hg n).symm))

/-- The genuine complete Hilbert source-energy space. -/
abbrev TranslationJumpEnergySpace (μ : Measure E) [SigmaFinite μ] :=
  ↥(translationJumpGraph μ)

instance (μ : Measure E) [SigmaFinite μ] : CompleteSpace (TranslationJumpEnergySpace μ) :=
  (isClosed_translationJumpGraph μ).completeSpace_coe

/-- The true value observation of a full source-energy state. -/
def translationJumpValue (μ : Measure E) [SigmaFinite μ] :
    TranslationJumpEnergySpace μ →L[ℝ] L² :=
  WithLp.fstL 2 ℝ L² (J² μ) ∘L (translationJumpGraph μ).subtypeL

/-- The true source increment data of a full source-energy state. -/
def translationJumpData (μ : Measure E) [SigmaFinite μ] :
    TranslationJumpEnergySpace μ →L[ℝ] J² μ :=
  WithLp.sndL 2 ℝ L² (J² μ) ∘L (translationJumpGraph μ).subtypeL

/-- The actual increment class represents the full spatial increments almost everywhere. -/
theorem translationJumpData_ae (μ : Measure E) [SigmaFinite μ]
    (U : TranslationJumpEnergySpace μ) :
    translationJumpData μ U =ᵐ[volume.prod μ]
      translationJump (translationJumpValue μ U : E → ℝ) := U.property

/-- A true finite-energy value defines its actual graph state. -/
def translationJumpState (μ : Measure E) [SigmaFinite μ] (u : L²)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ)) :
    TranslationJumpEnergySpace μ :=
  ⟨WithLp.toLp 2 (u, hu.toLp (translationJump (u : E → ℝ))), hu.coeFn_toLp⟩

@[simp]
theorem translationJumpValue_state (μ : Measure E) [SigmaFinite μ] (u : L²)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ)) :
    translationJumpValue μ (translationJumpState μ u hu) = u := rfl

/-- The actual graph norm consists exactly of the ordinary value and source increment norms. -/
theorem translationJumpEnergy_norm_sq (μ : Measure E) [SigmaFinite μ]
    (U : TranslationJumpEnergySpace μ) :
    ‖U‖ ^ 2 = ‖translationJumpValue μ U‖ ^ 2 + ‖translationJumpData μ U‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (U : H μ)

set_option maxHeartbeats 600000 in
/-- A genuinely bounded source-energy sequence has a cofinal weak graph limit. -/
theorem exists_weak_translationJump_graph_limit
    (μ : Measure E) [SigmaFinite μ] (U : ℕ → TranslationJumpEnergySpace μ)
    (R : ℝ) (hb : ∀ k, ‖U k‖ ≤ R) {u : L²}
    (ht : Tendsto (fun k ↦ translationJumpValue μ (U k)) atTop (𝓝 u)) :
    ∃ (V : TranslationJumpEnergySpace μ) (l : Filter ℕ),
      l.NeBot ∧ l ≤ atTop ∧ translationJumpValue μ V = u ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (U k)) l (𝓝 (toWeakSpace ℝ _ V)) := by
  have hc := isCompact_toWeakSpace_image_closedBall
    (0 : TranslationJumpEnergySpace μ) R
  have hm : ∀ᶠ k in atTop, toWeakSpace ℝ _ (U k) ∈
      toWeakSpace ℝ _ '' closedBall (0 : TranslationJumpEnergySpace μ) R := by
    exact Eventually.of_forall fun k ↦ ⟨U k,
      by simpa only [mem_closedBall, dist_zero_right] using hb k, rfl⟩
  obtain ⟨_, ⟨V, _, rfl⟩, hp⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  obtain ⟨l, hl, hlt⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have hvalue : Tendsto (fun k ↦ toWeakSpace ℝ L² (translationJumpValue μ (U k))) l
      (𝓝 (toWeakSpace ℝ L² (translationJumpValue μ V))) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((continuous_weakMap (translationJumpValue μ)).tendsto _).comp hlt
  have hstrong : Tendsto (fun k ↦ toWeakSpace ℝ L² (translationJumpValue μ (U k))) l
      (𝓝 (toWeakSpace ℝ L² u)) :=
    (((toWeakSpaceCLM ℝ L²).continuous.tendsto u).comp ht).mono_left hl
  exact ⟨V, l, inferInstance, hl,
    (toWeakSpace ℝ L²).injective (tendsto_nhds_unique hvalue hstrong), hlt⟩

end PartialBalayage.Maximal.Square
