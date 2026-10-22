/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DilatedKernelSource

/-!
# Sigma finiteness of the genuinely dilated singular sources

Positive dilation is a genuine measurable equivalence. Its pushforward
preserves sigma finiteness, and the real nonnegative scalar is finite.
The actual source may still have infinite total mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Every positive-radius actual source dilation is sigma finite. -/
theorem sigmaFinite_dilatedSourceMeasure (α : ℝ) {r : ℝ} (hr : 0 < r)
    (μ : Measure E) [SigmaFinite μ] : SigmaFinite (dilatedSourceMeasure α r μ) := by
  have he : MeasurableEmbedding (fun x : E ↦ r • x) :=
    (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv.measurableEmbedding
  let : SigmaFinite (Measure.map (fun x : E ↦ r • x) μ) := he.sigmaFinite_map
  let c : ℝ≥0 := ⟨r ^ 2 * r ^ (-α), by positivity⟩
  have hcoef : ENNReal.ofReal (r ^ 2 * r ^ (-α)) = (c : ℝ≥0∞) := by
    change ENNReal.ofReal (c : ℝ) = (c : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  rw [dilatedSourceMeasure, hcoef]
  change SigmaFinite (c • Measure.map (fun x : E ↦ r • x) μ)
  infer_instance

end PartialBalayage.Maximal.Square
