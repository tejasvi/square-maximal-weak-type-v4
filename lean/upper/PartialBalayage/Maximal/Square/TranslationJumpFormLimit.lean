/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TranslationJumpGraph
public import PartialBalayage.Maximal.Square.CompensatedSourceTests

/-!
# True full-source weak equations survive mollification limits

Uniform actual increment norms and strong value convergence give a genuine
cofinal weak graph limit. Its weak equations against all actual integrable
energy tests retain strongly convergent L² forcing.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- The genuine full-source form is half the actual increment Hilbert pairing. -/
theorem translationJumpForm_eq_half_inner_data
    (μ : Measure E) [SigmaFinite μ] (U : TranslationJumpEnergySpace μ) (v : L²)
    (hv : MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ)) :
    translationJumpForm μ (translationJumpValue μ U) v = (1 / 2 : ℝ) *
      ⟪translationJumpData μ U, hv.toLp (translationJump (v : E → ℝ))⟫ := by
  rw [L2.inner_def]
  unfold translationJumpForm
  congr 1
  apply integral_congr_ae
  filter_upwards [translationJumpData_ae μ U, hv.coeFn_toLp] with p hp hvp
  simp only [hp, hvp, Real.inner_apply]

set_option maxHeartbeats 600000 in
/-- Genuine strong value limits retain true full-source equations against integrable tests. -/
theorem translationJumpForm_equation_of_L2_tendsto
    (μ : Measure E) [SigmaFinite μ] (U G : ℕ → L²) (u g : L²)
    (hU : ∀ k, MemLp (translationJump (U k : E → ℝ)) 2 (volume.prod μ))
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hvalue : ∀ k, ‖U k‖ ≤ A)
    (hdata : ∀ k, ‖(hU k).toLp (translationJump (U k : E → ℝ))‖ ≤ C)
    (htU : Tendsto U atTop (𝓝 u)) (htG : Tendsto G atTop (𝓝 g))
    (heq : ∀ k (v : L²), Integrable (v : E → ℝ) volume →
      MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
        translationJumpForm μ (U k) v = -(∫ x, G k x * v x)) :
    ∃ _hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ),
      ∀ v : L², Integrable (v : E → ℝ) volume →
        MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
          translationJumpForm μ u v = -(∫ x, g x * v x) := by
  let S (k : ℕ) := translationJumpState μ (U k) (hU k)
  have hb (k : ℕ) : ‖S k‖ ≤ A + C := by
    have he := translationJumpEnergy_norm_sq μ (S k)
    have hd : ‖translationJumpData μ (S k)‖ ≤ C := hdata k
    have hv : ‖translationJumpValue μ (S k)‖ ≤ A := hvalue k
    have hds := (sq_le_sq₀ (norm_nonneg _) hC).mpr hd
    have hvs := (sq_le_sq₀ (norm_nonneg _) hA).mpr hv
    have hpos := mul_nonneg hA hC
    have hn : 0 ≤ ‖S k‖ := norm_nonneg _
    nlinarith
  have hvalues : Tendsto (fun k ↦ translationJumpValue μ (S k)) atTop (𝓝 u) := htU
  obtain ⟨V, l, hNe, hl, hVu, hweak⟩ :=
    exists_weak_translationJump_graph_limit μ S (A + C) hb hvalues
  let : l.NeBot := hNe
  have hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ) := by
    have hd := (Lp.memLp (translationJumpData μ V)).ae_eq (translationJumpData_ae μ V)
    rwa [hVu] at hd
  refine ⟨hu, fun v hv1 hvJ ↦ ?_⟩
  let Dv := hvJ.toLp (translationJump (v : E → ℝ))
  let L : TranslationJumpEnergySpace μ →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (innerSL ℝ Dv).comp (translationJumpData μ)
  have hLe (W : TranslationJumpEnergySpace μ) :
      L W = translationJumpForm μ (translationJumpValue μ W) v := by
    rw [translationJumpForm_eq_half_inner_data μ W v hvJ]
    change (1 / 2 : ℝ) * ⟪Dv, translationJumpData μ W⟫ = _
    rw [real_inner_comm]
  have hleft : Tendsto (fun k ↦ L (S k)) l (𝓝 (L V)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (L.continuous_comp_toWeakSpace_symm.tendsto _).comp hweak
  have hright : Tendsto (fun k ↦ -(∫ x, G k x * v x)) l
      (𝓝 (-(∫ x, g x * v x))) := by
    have h := (((innerSL ℝ v).continuous.tendsto g).comp htG).neg.mono_left hl
    simpa only [Function.comp_def, Pi.neg_apply, innerSL_apply_apply, L2.inner_def,
      Real.inner_apply, mul_comm] using h
  have he : L V = -(∫ x, g x * v x) :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright
      (Eventually.of_forall fun k ↦ by
        change L (S k) = _
        rw [hLe]
        exact heq k v hv1 hvJ)
  rw [hLe, hVu] at he
  exact he

end PartialBalayage.Maximal.Square
