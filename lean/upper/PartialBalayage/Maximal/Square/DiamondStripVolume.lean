/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondSquareTransport
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Actual planar volumes of coordinate and diamond boundary strips

The coordinate boxes use genuine Euclidean volume preservation. The diamond
annulus uses the actual determinant-two map and exact sup-norm ball volumes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin 2 → ℝ

private theorem volume_euclidean_preimage (s : Set P) (hs : MeasurableSet s) :
    volume {x : E | (fun i ↦ x i) ∈ s} = volume s := by
  have hp := PiLp.volume_preserving_ofLp (ι := Fin 2)
  have he := congrArg (fun μ : Measure P ↦ μ s) hp.map_eq
  rw [Measure.map_apply hp.measurable hs] at he
  exact he

/-- The actual Euclidean coordinate box has the ordinary product volume. -/
theorem volume_euclidean_coordinateBox (r : P) :
    volume {x : E | ∀ i, |x i| ≤ r i} =
      ∏ i, ENNReal.ofReal (2 * r i) := by
  have he : {x : E | ∀ i, |x i| ≤ r i} =
      {x : E | (fun i ↦ x i) ∈ Icc (-r) r} := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, Pi.le_def, Pi.neg_apply, abs_le]
    aesop
  rw [he, volume_euclidean_preimage _ measurableSet_Icc, Real.volume_Icc_pi]
  congr 1
  ext i
  congr 1
  simp only [Pi.neg_apply]
  ring

/-- A genuine coordinate strip in a bounded Euclidean region has volume at most `4Lt`. -/
theorem volume_coordinateStrip_le (i : Fin 2) {L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) :
    volume {x : E | |x i| < t ∧ ‖x‖ ≤ L} ≤ ENNReal.ofReal (4 * L * t) := by
  let r : P := fun j ↦ if j = i then t else L
  have hs : {x : E | |x i| < t ∧ ‖x‖ ≤ L} ⊆ {x : E | ∀ j, |x j| ≤ r j} := by
    intro x hx j
    dsimp only [r]
    split_ifs with h
    · simpa only [h] using hx.1.le
    · have hn : |x j| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      exact hn.trans hx.2
  calc
    _ ≤ volume {x : E | ∀ j, |x j| ≤ r j} := measure_mono hs
    _ = _ := by
      rw [volume_euclidean_coordinateBox, Fin.prod_univ_two]
      fin_cases i <;> dsimp [r]
      all_goals rw [← ENNReal.ofReal_mul (by positivity)]
      all_goals (congr 1; ring)

private theorem volume_pi_diamond_closed {r : ℝ} (hr : 0 ≤ r) :
    volume {x : P | diamondRadius (x 0) (x 1) ≤ r} = ENNReal.ofReal (2 * r ^ 2) := by
  have hm := congrArg (fun μ : Measure P ↦ μ (closedBall (0 : P) r))
    map_volume_diamondSquareMap
  rw [Measure.map_apply
    (show Measurable diamondSquareMap from diamondSquareEquiv.continuous.measurable)
      measurableSet_closedBall, Measure.smul_apply] at hm
  have he : diamondSquareMap ⁻¹' closedBall (0 : P) r =
      {x : P | diamondRadius (x 0) (x 1) ≤ r} := by
    ext x
    exact diamondSquareMap_mem_closedBall_iff x r
  rw [he, Real.volume_pi_closedBall _ hr] at hm
  simpa only [Fintype.card_fin, smul_eq_mul,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show (1 / 2 : ℝ) * (2 * r) ^ 2 = 2 * r ^ 2 by ring] using hm

/-- The actual Euclidean closed diamond has area twice its radius squared. -/
theorem volume_euclidean_diamond_closed {r : ℝ} (hr : 0 ≤ r) :
    volume {x : E | diamondRadius (x 0) (x 1) ≤ r} = ENNReal.ofReal (2 * r ^ 2) := by
  have hs : MeasurableSet {x : P | diamondRadius (x 0) (x 1) ≤ r} := by
    apply IsClosed.measurableSet
    exact isClosed_le (by unfold diamondRadius; fun_prop) continuous_const
  exact (volume_euclidean_preimage _ hs).trans (volume_pi_diamond_closed hr)

/-- The genuine thin diamond boundary strip has volume at most `8Rt`. -/
theorem volume_diamondBoundaryStrip_le {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (htR : t < R) :
    volume {x : E | |R - diamondRadius (x 0) (x 1)| < t} ≤
      ENNReal.ofReal (8 * R * t) := by
  let outer : Set E := {x | diamondRadius (x 0) (x 1) ≤ R + t}
  let inner : Set E := {x | diamondRadius (x 0) (x 1) ≤ R - t}
  have hi : MeasurableSet inner := by
    dsimp only [inner]
    apply IsClosed.measurableSet
    exact isClosed_le (by unfold diamondRadius; fun_prop) continuous_const
  have hsub : inner ⊆ outer := by
    intro x hx
    change diamondRadius (x 0) (x 1) ≤ R - t at hx
    change diamondRadius (x 0) (x 1) ≤ R + t
    linarith
  have hstrip : {x : E | |R - diamondRadius (x 0) (x 1)| < t} ⊆ outer \ inner := by
    intro x hx
    rw [mem_ofPred_eq, abs_lt] at hx
    exact ⟨by change diamondRadius (x 0) (x 1) ≤ R + t; linarith,
      by change ¬diamondRadius (x 0) (x 1) ≤ R - t; linarith⟩
  have hoVol := volume_euclidean_diamond_closed (show 0 ≤ R + t by positivity)
  have hiVol := volume_euclidean_diamond_closed (show 0 ≤ R - t by linarith)
  calc
    _ ≤ volume (outer \ inner) := measure_mono hstrip
    _ = volume outer - volume inner :=
      measure_sdiff hsub hi.nullMeasurableSet (by rw [hiVol]; exact ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (2 * (R + t) ^ 2 - 2 * (R - t) ^ 2) := by
      rw [hoVol, hiVol]
      exact (ENNReal.ofReal_sub (2 * (R + t) ^ 2) (by positivity)).symm
    _ = _ := by congr 1; ring

end PartialBalayage.Maximal.Square
