/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.MollifierL2Convergence

/-!
# Almost-everywhere positivity from genuine smooth tests

Actual normalized nonnegative mollifiers turn positivity against compact smooth
tests into positivity of an `L²` function. Strong convergence and the closed
positive cone then give the almost-everywhere conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Convolution Topology

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- Positivity against every actual nonnegative compact C² test detects `L²` positivity. -/
theorem ae_nonneg_of_integral_compactC2_nonneg
    (g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (htest : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 φ →
      HasCompactSupport φ → (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, φ x * g x) :
    ∀ᵐ x ∂volume, 0 ≤ g x := by
  have hp (n : ℕ) : 0 ≤ graphMollifierL2 n g := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [graphMollifierL2_ae n g] with x hx
    rw [hx, convolution_eq_swap]
    exact htest (fun y ↦ (graphMollifierBump d n).normed volume (x - y))
      (((graphMollifierBump d n).contDiff_normed (n := 2)).comp
        (contDiff_const.sub contDiff_id))
      ((graphMollifierBump d n).hasCompactSupport_normed.comp_homeomorph
        (Homeomorph.subLeft x))
      (fun y ↦ (graphMollifierBump d n).nonneg_normed (x - y))
  have hg : (0 : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) ≤ g :=
    (isClosed_Ici : IsClosed
      (Ici (0 : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))))).mem_of_tendsto
      (tendsto_graphMollifierL2 g) (Eventually.of_forall hp)
  exact (Lp.coeFn_nonneg g).mpr hg

end PartialBalayage.Linear
