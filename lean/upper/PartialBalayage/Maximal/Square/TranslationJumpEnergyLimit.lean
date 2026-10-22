/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.TranslationJumpTests
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Genuine energy-domain passage for full source jumps

Strong convergence of actual L² values and a uniform bound on their true full
jump increments imply that the limit has square-integrable source increments.
The proof uses an actual AE subsequence and Fatou over the infinite jump measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology

namespace PartialBalayage.Maximal.Square

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- Fatou retains the true full jump seminorm under strong convergence of actual L² values. -/
theorem eLpNorm_translationJump_le_of_L2_tendsto (μ : Measure E) [SigmaFinite μ]
    {U : ℕ → L²} {u : L²} (ht : Tendsto U atTop (𝓝 u)) {C : ℝ≥0∞}
    (hb : ∀ k, eLpNorm (translationJump (U k : E → ℝ)) 2 (volume.prod μ) ≤ C) :
    eLpNorm (translationJump (u : E → ℝ)) 2 (volume.prod μ) ≤ C := by
  obtain ⟨s, hs, hsu⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hp : ∀ᵐ p ∂volume.prod μ, Tendsto
      (fun k ↦ translationJump (U (s k) : E → ℝ) p) atTop
      (𝓝 (translationJump (u : E → ℝ) p)) := by
    filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae hsu,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae hsu]
        with p hx hy
    exact hx.sub hy
  exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun k ↦ hb (s k))
    (fun k ↦ aestronglyMeasurable_translationJump μ (U (s k)))
    (aestronglyMeasurable_translationJump μ u) hp

/-- A finite actual increment bound puts the true strong limit in the full source energy domain. -/
theorem memLp_translationJump_of_L2_tendsto (μ : Measure E) [SigmaFinite μ]
    {U : ℕ → L²} {u : L²} (ht : Tendsto U atTop (𝓝 u)) {C : ℝ≥0∞} (hC : C < ∞)
    (hb : ∀ k, eLpNorm (translationJump (U k : E → ℝ)) 2 (volume.prod μ) ≤ C) :
    MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ) := by
  exact (eLpNorm_translationJump_le_of_L2_tendsto μ ht hb).trans_lt hC

/-- The actual full-source energy is half the square norm of its genuine increment class. -/
theorem translationJumpForm_self_eq_norm_sq (μ : Measure E) [SigmaFinite μ] (u : L²)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ)) :
    translationJumpForm μ u u =
      (1 / 2 : ℝ) * ‖hu.toLp (translationJump (u : E → ℝ))‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold translationJumpForm
  congr 1
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with p hp
  simp only [Real.inner_apply, hp]

/-- Ordinary uniform increment norms pass to the true limit, with actual source integrability. -/
theorem memLp_translationJump_and_norm_le_of_L2_tendsto
    (μ : Measure E) [SigmaFinite μ] {U : ℕ → L²} {u : L²}
    (ht : Tendsto U atTop (𝓝 u)) (hU : ∀ k,
      MemLp (translationJump (U k : E → ℝ)) 2 (volume.prod μ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k, ‖(hU k).toLp (translationJump (U k : E → ℝ))‖ ≤ C) :
    ∃ hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ),
      ‖hu.toLp (translationJump (u : E → ℝ))‖ ≤ C := by
  have he (k : ℕ) : eLpNorm (translationJump (U k : E → ℝ)) 2 (volume.prod μ) ≤
      ENNReal.ofReal C := by
    rw [← Lp.enorm_toLp (hU k), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb k)
  have hu := memLp_translationJump_of_L2_tendsto μ ht ENNReal.ofReal_lt_top he
  refine ⟨hu, ?_⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNorm_translationJump_le_of_L2_tendsto μ ht he)).trans_eq
      (ENNReal.toReal_ofReal hC)

end PartialBalayage.Maximal.Square
