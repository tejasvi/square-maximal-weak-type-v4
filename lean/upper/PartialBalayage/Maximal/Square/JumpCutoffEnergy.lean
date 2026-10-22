/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpGeneratorPairing
public import PartialBalayage.Maximal.Square.JumpDensityMass
public import Mathlib.Analysis.Normed.MulAction

/-!
# Actual bounded Lipschitz multiplication in the full jump energy

The product rule has one increment of the state and one increment of the
cutoff. The latter is square integrable against the entire singular jump
measure: Lipschitz continuity controls small jumps and boundedness controls
the tail. No deletion of small jumps is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The true coordinate increment of a bounded Lipschitz function has a quadratic bound. -/
theorem coordinateJump_sq_le_quadratic {η : E → ℝ} {K : ℝ≥0}
    (hη : LipschitzWith K η) (i : Fin 2) (x : E) (t : ℝ) :
    coordinateJump η i (x, t) ^ 2 ≤ (K : ℝ) ^ 2 * t ^ 2 := by
  have h := hη.norm_sub_le (coordinateJumpPoint i (x, t)) x
  have ha : ‖coordinateJumpPoint i (x, t) - x‖ = |t| := by
    simp only [coordinateJumpPoint, add_sub_cancel_left, norm_smul,
      (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs]
  rw [ha, Real.norm_eq_abs] at h
  have hp := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (K : ℝ) * |t|)).mpr h
  simpa only [coordinateJump, Prod.fst, mul_pow, sq_abs] using hp

/-- An actual uniform amplitude bound controls every coordinate jump square. -/
theorem coordinateJump_sq_le_four {η : E → ℝ} {M : ℝ}
    (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) (x : E) (t : ℝ) :
    coordinateJump η i (x, t) ^ 2 ≤ 4 * M ^ 2 := by
  have hx := hM x
  have hy := hM (coordinateJumpPoint i (x, t))
  have h : ‖coordinateJump η i (x, t)‖ ≤ 2 * M := by
    exact (norm_sub_le _ _).trans (by
      change ‖η (coordinateJumpPoint i (x, t))‖ + ‖η x‖ ≤ 2 * M
      linarith)
  have hM0 : 0 ≤ M := (norm_nonneg (η x)).trans (hM x)
  rw [Real.norm_eq_abs] at h
  have hp := (sq_le_sq₀ (abs_nonneg (coordinateJump η i (x, t)))
    (by positivity : 0 ≤ 2 * M)).mpr h
  nlinarith [sq_abs (coordinateJump η i (x, t))]

/-- Every actual bounded Lipschitz cutoff has a finite full jump square at each point. -/
theorem integrable_coordinateJump_sq {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {η : E → ℝ} {K : ℝ≥0} {M : ℝ} (hη : LipschitzWith K η)
    (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) (x : E) :
    Integrable (fun t : ℝ ↦ coordinateJump η i (x, t) ^ 2) (stableJumpMeasure α) := by
  have hm : Continuous (fun t : ℝ ↦ coordinateJump η i (x, t) ^ 2) := by
    have hc := hη.continuous
    unfold coordinateJump coordinateJumpPoint
    fun_prop
  apply integrable_stableJumpMeasure_of_bounds hα0 hα2 (by norm_num : (0 : ℝ) < 1) _
    hm.aestronglyMeasurable
  · intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact coordinateJump_sq_le_quadratic hη i x t
  · intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact coordinateJump_sq_le_four hM i x t

/-- The actual cutoff square integral has the exact split-at-radius estimate. -/
theorem integral_coordinateJump_sq_le {α r : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hr : 0 < r) {η : E → ℝ} {K : ℝ≥0} {M : ℝ} (hη : LipschitzWith K η)
    (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) (x : E) :
    (∫ t, coordinateJump η i (x, t) ^ 2 ∂stableJumpMeasure α) ≤
      stableNormalization α * ((K : ℝ) ^ 2 * r ^ (2 - α) / (2 - α) +
        4 * M ^ 2 * r ^ (-α) / α) := by
  have hm : Continuous (fun t : ℝ ↦ coordinateJump η i (x, t) ^ 2) := by
    have hc := hη.continuous
    unfold coordinateJump coordinateJumpPoint
    fun_prop
  simpa only [Real.norm_eq_abs, abs_sq] using
    integral_norm_stableJumpMeasure_le hα0 hα2 hr
      (fun t : ℝ ↦ coordinateJump η i (x, t) ^ 2) hm.aestronglyMeasurable
      (fun t _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact coordinateJump_sq_le_quadratic hη i x t)
      (fun t _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact coordinateJump_sq_le_four hM i x t)

set_option maxHeartbeats 600000 in
/-- The genuine product-rule cutoff error belongs to full spatial jump L². -/
theorem memLp_value_mul_coordinateJump {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (u : Lp ℝ 2 (volume : Measure E)) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) :
    MemLp (fun p : E × ℝ ↦ u p.1 * coordinateJump η i p) 2
      (spatialJumpMeasure α) := by
  let C := stableNormalization α * ((K : ℝ) ^ 2 / (2 - α) + 4 * M ^ 2 / α)
  have hj : Continuous (coordinateJump η i) := by
    have hc := hη.continuous
    unfold coordinateJump coordinateJumpPoint
    fun_prop
  have hm : AEStronglyMeasurable (fun p : E × ℝ ↦ u p.1 * coordinateJump η i p)
      (spatialJumpMeasure α) :=
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α))).mul hj.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  change Integrable _ (volume.prod (stableJumpMeasure α))
  apply (integrable_prod_iff (hm.pow 2)).mpr
  constructor
  · filter_upwards with x
    simpa only [Pi.pow_apply, mul_pow] using
      (integrable_coordinateJump_sq hα0 hα2 hη hM i x).const_mul (u x ^ 2)
  · apply ((Lp.memLp u).integrable_sq.mul_const C).mono'
      (hm.pow 2).norm.integral_prod_right'
    filter_upwards with x
    have hC : (∫ t, coordinateJump η i (x, t) ^ 2 ∂stableJumpMeasure α) ≤ C := by
      simpa only [Real.one_rpow, mul_one, C] using
        integral_coordinateJump_sq_le hα0 hα2 (by norm_num : (0 : ℝ) < 1) hη hM i x
    simp only [Pi.pow_apply, mul_pow, Real.norm_eq_abs, abs_mul, abs_sq, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hC (sq_nonneg _)

/-- The genuine product-rule error has the exact full-energy radius estimate. -/
theorem integral_value_mul_coordinateJump_sq_le {α r : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r)
    (u : Lp ℝ 2 (volume : Measure E)) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) :
    (∫ p : E × ℝ, (u p.1 * coordinateJump η i p) ^ 2 ∂spatialJumpMeasure α) ≤
      (∫ x : E, u x ^ 2) * stableNormalization α *
        ((K : ℝ) ^ 2 * r ^ (2 - α) / (2 - α) + 4 * M ^ 2 * r ^ (-α) / α) := by
  let C := stableNormalization α *
    ((K : ℝ) ^ 2 * r ^ (2 - α) / (2 - α) + 4 * M ^ 2 * r ^ (-α) / α)
  have hi := (memLp_value_mul_coordinateJump hα0 hα2 u hη hM i).integrable_sq
  change Integrable _ (volume.prod (stableJumpMeasure α)) at hi
  have he : (fun x : E ↦ ∫ t, (u x * coordinateJump η i (x, t)) ^ 2
      ∂stableJumpMeasure α) = fun x ↦
        u x ^ 2 * ∫ t, coordinateJump η i (x, t) ^ 2 ∂stableJumpMeasure α := by
    funext x
    simp only [mul_pow, integral_const_mul]
  have hinner := hi.integral_prod_left
  rw [he] at hinner
  calc
    _ = ∫ x : E, u x ^ 2 *
        ∫ t, coordinateJump η i (x, t) ^ 2 ∂stableJumpMeasure α := by
      rw [spatialJumpMeasure, integral_prod _ hi]
      simp only [mul_pow, integral_const_mul]
    _ ≤ ∫ x : E, u x ^ 2 * C := by
      apply integral_mono_ae hinner ((Lp.memLp u).integrable_sq.mul_const C)
      filter_upwards with x
      exact mul_le_mul_of_nonneg_left
        (integral_coordinateJump_sq_le hα0 hα2 hr hη hM i x) (sq_nonneg _)
    _ = _ := by rw [integral_mul_const]; dsimp [C]; ring

/-- Multiplication by a genuine bounded Lipschitz function preserves the entire jump graph. -/
theorem memLp_coordinateJump_mul {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) (i : Fin 2) :
    MemLp (coordinateJump (fun x : E ↦ η x * stableJumpValue α U x) i) 2
      (spatialJumpMeasure α) := by
  have hm : AEStronglyMeasurable (fun p : E × ℝ ↦
      η (coordinateJumpPoint i p) * stableJumpData α U i p) (spatialJumpMeasure α) :=
    (hη.continuous.comp (by unfold coordinateJumpPoint; fun_prop)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (stableJumpData α U i))
  have hmain : MemLp (fun p : E × ℝ ↦
      η (coordinateJumpPoint i p) * stableJumpData α U i p) 2
      (spatialJumpMeasure α) := by
    apply (Lp.memLp (stableJumpData α U i)).of_le_mul hm
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have herr := memLp_value_mul_coordinateJump hα0 hα2 (stableJumpValue α U) hη hM i
  apply MemLp.ae_eq _ (hmain.add herr)
  filter_upwards [stableJumpData_ae α U i] with p hp
  dsimp only [coordinateJump, Pi.add_apply]
  rw [hp]
  unfold coordinateJump
  ring

/-- The true L² value of the product by a bounded continuous coefficient. -/
theorem memLp_mul_stableJumpValue {α : ℝ} (U : StableJumpEnergySpace α)
    {η : E → ℝ} {M : ℝ} (hη : Continuous η) (hM : ∀ x, ‖η x‖ ≤ M) :
    MemLp (fun x : E ↦ η x * stableJumpValue α U x) 2 volume := by
  apply (Lp.memLp (stableJumpValue α U)).of_le_mul
    (hη.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (stableJumpValue α U)))
  filter_upwards with x
  change ‖η x * stableJumpValue α U x‖ ≤ M * ‖stableJumpValue α U x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

/-- Actual bounded Lipschitz multiplication, realized in the closed singular energy graph. -/
def stableJumpLipschitzMul {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) : StableJumpEnergySpace α := by
  let u := fun x : E ↦ η x * stableJumpValue α U x
  let hv := memLp_mul_stableJumpValue U hη.continuous hM
  let hj := fun i ↦ memLp_coordinateJump_mul hα0 hα2 U hη hM i
  refine ⟨WithLp.toLp 2 (hv.toLp u,
    WithLp.toLp 2 fun i ↦ (hj i).toLp (coordinateJump u i)), ?_⟩
  change ∀ i : Fin 2, ∀ᵐ p ∂spatialJumpMeasure α,
    (hj i).toLp (coordinateJump u i) p = coordinateJump (hv.toLp u : E → ℝ) i p
  intro i
  filter_upwards [(hj i).coeFn_toLp,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae hv.coeFn_toLp,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae hv.coeFn_toLp] with p hp hx hy
  dsimp [u] at ⊢
  rw [hp]
  unfold coordinateJump
  rw [hx, hy]

/-- The true physical value of actual bounded Lipschitz multiplication. -/
theorem stableJumpLipschitzMul_value_ae {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) :
    (stableJumpValue α (stableJumpLipschitzMul hα0 hα2 U hη hM) : E → ℝ)
      =ᵐ[volume] fun x ↦ η x * stableJumpValue α U x := by
  change (memLp_mul_stableJumpValue U hη.continuous hM).toLp
    (fun x ↦ η x * stableJumpValue α U x) =ᵐ[volume] _
  exact (memLp_mul_stableJumpValue U hη.continuous hM).coeFn_toLp

/-- Every actual compact multiplier gives a genuinely supported jump state. -/
theorem stableJumpLipschitzMul_mem_supported {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) {η : E → ℝ} {K : ℝ≥0} {M : ℝ}
    (hη : LipschitzWith K η) (hM : ∀ x, ‖η x‖ ≤ M) {S : Set E}
    (hS : MeasurableSet S) (hsub : tsupport η ⊆ S) :
    stableJumpLipschitzMul hα0 hα2 U hη hM ∈ stableJumpSupported α S := by
  rw [mem_stableJumpSupported_iff α hS]
  filter_upwards [stableJumpLipschitzMul_value_ae hα0 hα2 U hη hM] with x hx
  intro hxo
  rw [hx, image_eq_zero_of_notMem_tsupport (fun h ↦ hxo (hsub h)), zero_mul]

end PartialBalayage.Maximal.Square
