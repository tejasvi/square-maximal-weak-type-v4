/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondStripVolume

/-!
# The actual diamond support boundary is a planar null set

The determinant-two diamond transformation sends the boundary to a genuine sup-norm
sphere. Haar sphere nullity and actual Euclidean volume preservation give its nullity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin 2 → ℝ

private theorem volume_pi_diamondBoundary (R : ℝ) :
    volume {x : P | diamondRadius (x 0) (x 1) = R} = 0 := by
  have hm := congrArg (fun μ : Measure P ↦ μ (sphere (0 : P) R))
    map_volume_diamondSquareMap
  rw [Measure.map_apply
    (show Measurable diamondSquareMap from diamondSquareEquiv.continuous.measurable)
      isClosed_sphere.measurableSet, Measure.smul_apply, Measure.addHaar_sphere, smul_zero] at hm
  have he : diamondSquareMap ⁻¹' sphere (0 : P) R =
      {x : P | diamondRadius (x 0) (x 1) = R} := by
    ext x
    simp only [mem_preimage, mem_sphere, dist_zero_right, norm_diamondSquareMap, mem_ofPred_eq]
  rw [he] at hm
  exact hm

/-- The genuine Euclidean diamond boundary has Lebesgue measure zero at every radius. -/
theorem volume_euclidean_diamondBoundary (R : ℝ) :
    volume {x : E | diamondRadius (x 0) (x 1) = R} = 0 := by
  have hs : MeasurableSet {x : P | diamondRadius (x 0) (x 1) = R} :=
    (isClosed_eq (by unfold diamondRadius; fun_prop) continuous_const).measurableSet
  have hp := PiLp.volume_preserving_ofLp (ι := Fin 2)
  have he := congrArg (fun μ : Measure P ↦ μ {x | diamondRadius (x 0) (x 1) = R}) hp.map_eq
  rw [Measure.map_apply hp.measurable hs] at he
  exact he.trans (volume_pi_diamondBoundary R)

theorem ae_diamondRadius_ne (R : ℝ) :
    ∀ᵐ x : E ∂volume, diamondRadius (x 0) (x 1) ≠ R :=
  compl_mem_ae_iff.mpr (volume_euclidean_diamondBoundary R)

end PartialBalayage.Maximal.Square
