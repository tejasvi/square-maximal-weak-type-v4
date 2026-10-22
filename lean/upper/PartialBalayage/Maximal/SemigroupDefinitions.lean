/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import PartialBalayage.Maximal.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Poisson and heat operators

These are the ordinary convolution maximal operators in the published table.
The parameterized exact bound formulas do not assert an inequality: constructing the
article's unique parameters and proving the operator bounds are separate outstanding tasks.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PartialBalayage

theorem poissonKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < poissonKernel n t x := by
  have hΓ : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hx : 0 < t ^ 2 + ‖x‖ ^ 2 := by positivity
  unfold poissonKernel
  positivity

theorem heatKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < heatKernel n t x := by
  unfold heatKernel
  positivity

end PartialBalayage
