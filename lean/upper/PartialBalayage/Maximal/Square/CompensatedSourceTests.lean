/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourcePairing
public import PartialBalayage.Maximal.Square.TranslationJumpL1Contact

/-!
# Genuine compact tests for the full infinite source contact argument

The compact tests and their actual source-generator images belong to L². Their
source equations are proved against every actual integrable energy test.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- Actual value equality almost everywhere preserves the full-vector increments. -/
theorem translationJump_congr_ae (μ : Measure E) [SigmaFinite μ]
    {f g : E → ℝ} (he : f =ᵐ[volume] g) :
    translationJump f =ᵐ[volume.prod μ] translationJump g := by
  filter_upwards [(quasiMeasurePreserving_translationJumpPoint μ).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E)) (ν := μ)).ae he]
      with p hx hy
  simp only [translationJump, hx, hy]

/-- Every genuine compact C² test has its true L² source image and full weak-form equation. -/
theorem exists_compensatedSource_compactC2Test_pairing
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ (hφm : MemLp φ 2 volume) (b : L²),
      MemLp (translationJump (hφm.toLp φ : E → ℝ)) 2 (volume.prod μ) ∧
      b =ᵐ[volume] compensatedSourceGenerator μ φ ∧
      ∀ v : L², Integrable (v : E → ℝ) volume →
        MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
          translationJumpForm μ (hφm.toLp φ) v = -(∫ x, b x * v x) := by
  obtain ⟨hφm, hφJ⟩ := exists_translationJump_compactC2Test μ hm hφ hs
  let hb := memLp_compensatedSourceGenerator_compactC2 μ hm hφ hs
  let b := hb.toLp (compensatedSourceGenerator μ φ)
  refine ⟨hφm, b, hφJ, hb.coeFn_toLp, fun v hv1 hvJ ↦ ?_⟩
  obtain ⟨C, _, hC⟩ := exists_compactC2_symmetricSecondDifference_bound hφ hs
  have hrawJ := hφJ.ae_eq (translationJump_congr_ae μ hφm.coeFn_toLp)
  have he := integral_translationJump_mul_eq_neg_source μ hm hφ.continuous hφm
    hv1 (Lp.memLp v) hrawJ hvJ hC
  unfold translationJumpForm
  calc
    _ = (1 / 2 : ℝ) * ∫ p, translationJump φ p *
        translationJump (v : E → ℝ) p ∂volume.prod μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [translationJump_congr_ae μ hφm.coeFn_toLp] with p hp
      rw [hp]
    _ = -(∫ x, v x * compensatedSourceGenerator μ φ x) := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hb.coeFn_toLp] with x hx
      rw [hx, mul_comm]

/-- The actual full-source weak generator is nonnegative on the state zero set. -/
theorem ae_nonneg_on_contact_of_compensatedSource_form
    (μ : Measure E) [SigmaFinite μ] (hm : Integrable compensatedJumpMoment μ)
    (u g : L²) (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hu : MemLp (translationJump (u : E → ℝ)) 2 (volume.prod μ))
    (hequ : ∀ v : L², Integrable (v : E → ℝ) volume →
      MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
        translationJumpForm μ u v = -(∫ x, g x * v x)) :
    ∀ᵐ x ∂volume, u x = 0 → 0 ≤ g x := by
  apply ae_nonneg_on_contact_of_L1_translationJumpForm μ u g hu0 hu hequ
  intro φ hφ hs
  obtain ⟨hφm, b, hφJ, _, hφeq⟩ :=
    exists_compensatedSource_compactC2Test_pairing μ hm hφ hs
  exact ⟨hφm, b, hφJ, hφeq⟩

end PartialBalayage.Maximal.Square
