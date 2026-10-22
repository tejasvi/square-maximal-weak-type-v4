/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.GeneratorCutoff
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of the actual coordinate-stable generator

The untruncated half-line integral is a strongly measurable function of its
spatial center. Bounded genuine generator tests therefore pair with every
integrable kernel, including kernels that are not square integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem stronglyMeasurable_coordinateStableGenerator (α : ℝ) {φ : E → ℝ}
    (hφ : Continuous φ) : StronglyMeasurable (coordinateStableGenerator α φ) := by
  have hi (i : Fin 2) : StronglyMeasurable
      (fun x ↦ stableGeneratorIntegral α (coordinateLine φ x i)) := by
    have hm : Measurable (fun p : E × ℝ ↦ p.2 ^ (-1 - α) •
        stableSecondDifference (coordinateLine φ p.1 i) p.2) := by
      unfold stableSecondDifference coordinateLine
      fun_prop
    exact hm.stronglyMeasurable.integral_prod_right'
  unfold coordinateStableGenerator
  simp only [Fin.sum_univ_two]
  exact ((hi 0).add (hi 1)).const_mul _

/-- Genuine bounded stable-generator tests pair integrably with arbitrary `L¹` kernels. -/
theorem integrable_kernel_mul_coordinateStableGenerator {K φ : E → ℝ} {α C : ℝ}
    (hK : Integrable K volume) (hφ : Continuous φ)
    (hb : ∀ x, ‖coordinateStableGenerator α φ x‖ ≤ C) :
    Integrable (fun x ↦ K x * coordinateStableGenerator α φ x) volume :=
  hK.mul_bdd (stronglyMeasurable_coordinateStableGenerator α hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- Every genuine compact C² test pairs integrably with an arbitrary integrable kernel. -/
theorem integrable_kernel_mul_coordinateStableGenerator_compactC2
    {K φ : E → ℝ} {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hK : Integrable K volume) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    Integrable (fun x ↦ K x * coordinateStableGenerator α φ x) volume := by
  obtain ⟨M, C, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds φ hφ hs
  exact integrable_kernel_mul_coordinateStableGenerator hK hφ.continuous
    (norm_coordinateStableGenerator_le hα0 hα2 φ hM hd hLip)

end PartialBalayage.Maximal.Square
