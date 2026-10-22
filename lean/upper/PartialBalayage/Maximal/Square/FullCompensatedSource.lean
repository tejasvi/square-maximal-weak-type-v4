/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SymmetricSourceRepresentation

/-!
# Full compensated source identity for actual even kernels

Symmetrizing a genuine compact C² test gives zero first derivative at the origin.
The compensated source identity therefore applies to every compact test, without
any finite-mass hypothesis on its actual punctured source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine even part of a compact test. -/
def sourceEvenPart (φ : E → ℝ) (x : E) : ℝ := (φ x + φ (-x)) / 2

theorem sourceEvenPart_contDiff {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (sourceEvenPart φ) :=
  (hφ.add (hφ.comp contDiff_id.neg)).div_const 2

theorem sourceEvenPart_hasCompactSupport {φ : E → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport (sourceEvenPart φ) := by
  have hm : HasCompactSupport (fun x : E ↦ φ x + φ (-x)) :=
    hs.add (hs.comp_homeomorph (Homeomorph.neg E))
  exact hm.comp_left (g := fun r : ℝ ↦ r / 2) (by simp)

theorem sourceEvenPart_fderiv_zero (φ : E → ℝ) : fderiv ℝ (sourceEvenPart φ) 0 = 0 := by
  apply fderiv_even_zero
  intro x
  simp only [sourceEvenPart, neg_neg, add_comm]

theorem coordinateStableGenerator_sourceEvenPart {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (x : E) :
    coordinateStableGenerator α (sourceEvenPart φ) x =
      (coordinateStableGenerator α φ x + coordinateStableGenerator α φ (-x)) / 2 := by
  let ψ := fun y : E ↦ φ (-y)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp contDiff_id.neg
  have hψs : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.neg E)
  have hneg : ContDiff ℝ 2 (fun y ↦ (-1 : ℝ) * ψ y) := contDiff_const.mul hψ
  have hnegs : HasCompactSupport (fun y ↦ (-1 : ℝ) * ψ y) := hψs.mul_left
  have hf : sourceEvenPart φ = fun y ↦ (1 / 2 : ℝ) * (φ y - (-1 : ℝ) * ψ y) := by
    funext y
    dsimp [sourceEvenPart, ψ]
    ring
  rw [hf, coordinateStableGenerator_const_mul,
    coordinateStableGenerator_sub hα0 hα2 hφ hs hneg hnegs,
    coordinateStableGenerator_const_mul]
  change (1 / 2 : ℝ) * (coordinateStableGenerator α φ x -
    (-1 : ℝ) * coordinateStableGenerator α (fun y ↦ φ (-y)) x) = _
  rw [coordinateStableGenerator_reflect]
  ring

theorem integral_kernel_generator_sourceEvenPart {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {K φ : E → ℝ} (hK : Integrable K volume)
    (hKeven : ∀ x, K (-x) = K x) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, K x * coordinateStableGenerator α (sourceEvenPart φ) x) =
      ∫ x, K x * coordinateStableGenerator α φ x := by
  have hI := integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hφ hs
  have hψ : ContDiff ℝ 2 (fun x : E ↦ φ (-x)) := hφ.comp contDiff_id.neg
  have hψs : HasCompactSupport (fun x : E ↦ φ (-x)) :=
    hs.comp_homeomorph (Homeomorph.neg E)
  have hJ : Integrable (fun x ↦ K x * coordinateStableGenerator α φ (-x)) volume := by
    simpa only [coordinateStableGenerator_reflect] using
      integrable_kernel_mul_coordinateStableGenerator_compactC2 hα0 hα2 hK hψ hψs
  have href : (∫ x, K x * coordinateStableGenerator α φ (-x)) =
      ∫ x, K x * coordinateStableGenerator α φ x := by
    calc
      _ = ∫ x, K (-x) * coordinateStableGenerator α φ (-x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hKeven]
      _ = _ := integral_neg_eq_self
        (fun x : E ↦ K x * coordinateStableGenerator α φ x) volume
  calc
    _ = (1 / 2 : ℝ) * ((∫ x, K x * coordinateStableGenerator α φ x) +
        ∫ x, K x * coordinateStableGenerator α φ (-x)) := by
      calc
        _ = ∫ x, (1 / 2 : ℝ) * (K x * coordinateStableGenerator α φ x +
            K x * coordinateStableGenerator α φ (-x)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [coordinateStableGenerator_sourceEvenPart hα0 hα2 hφ hs]
          ring
        _ = _ := by rw [integral_const_mul, integral_add hI hJ]
    _ = _ := by rw [href]; ring

/-- The actual compensated symmetric jump source, with its full possibly infinite measure. -/
def compensatedSymmetricSource (μ : Measure E) (φ : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ z, φ z + φ (-z) - 2 * φ 0 ∂μ

/-- The source identity holds for every genuine compact C² test,
retaining infinite small-jump mass. -/
theorem integral_kernel_generator_eq_compensatedSymmetricSource
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (hKeven : ∀ x, K (-x) = K x)
    (μ : Measure E) (hm : Integrable compensatedJumpMoment μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ x, K x * coordinateStableGenerator α ψ x) = ∫ x, ψ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, K x * coordinateStableGenerator α φ x) = compensatedSymmetricSource μ φ := by
  rw [← integral_kernel_generator_sourceEvenPart hα0 hα2 hK hKeven hφ hs,
    integral_kernel_generator_eq_compensated_of_derivative_zero hα0 hα2 hK μ hm haway
      (sourceEvenPart_contDiff hφ) (sourceEvenPart_hasCompactSupport hs)
      (sourceEvenPart_fderiv_zero φ)]
  unfold compensatedSymmetricSource
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [sourceEvenPart, neg_zero]
  ring

end PartialBalayage.Maximal.Square
