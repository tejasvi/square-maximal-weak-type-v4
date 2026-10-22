/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpDirichletSpace
public import PartialBalayage.Linear.FractionalCutoffBound
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual compact Lipschitz tests for the singular jump form

Compact Lipschitz functions have quadratic integrated differences at small jumps
and a uniform integrated bound at large jumps. Thus they belong to the genuine
singular energy graph for every stable order between zero and two.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set
open PartialBalayage.Linear
open scoped ENNReal NNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual scalar physical translation difference. -/
def translationDifference (φ : E → ℝ) (a : E) (x : E) : ℝ := φ (x + a) - φ x

/-- The genuine translated difference is square integrable whenever the original function is. -/
theorem memLp_translationDifference {φ : E → ℝ} (hφ : MemLp φ 2 volume) (a : E) :
    MemLp (translationDifference φ a) 2 volume :=
  (hφ.comp_measurePreserving (measurePreserving_add_right volume a)).sub hφ

/-- The actual translated square integral has the uniform large-jump bound. -/
theorem integral_translationDifference_sq_le_four {φ : E → ℝ}
    (hφ : MemLp φ 2 volume) (a : E) :
    (∫ x : E, translationDifference φ a x ^ 2) ≤ 4 * ∫ x : E, φ x ^ 2 := by
  have ht : Integrable (fun x ↦ φ (x + a) ^ 2) volume :=
    (hφ.comp_measurePreserving (measurePreserving_add_right volume a)).integrable_sq
  have hi := (memLp_translationDifference hφ a).integrable_sq
  calc
    _ ≤ ∫ x : E, 2 * φ (x + a) ^ 2 + 2 * φ x ^ 2 :=
      integral_mono hi ((ht.const_mul 2).add (hφ.integrable_sq.const_mul 2))
        (fun x ↦ by dsimp [translationDifference]; nlinarith [sq_nonneg (φ (x + a) + φ x)])
    _ = _ := by
      rw [integral_add (ht.const_mul 2) (hφ.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul,
        (measurePreserving_add_right volume a).integral_comp
          (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (fun x ↦ φ x ^ 2)]
      ring

/-- Compactness and an actual Lipschitz bound give the integrated quadratic small-jump bound. -/
theorem integral_coordinate_translationDifference_sq_le_quadratic {φ : E → ℝ}
    {K : ℝ≥0} (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) (i : Fin 2) (t : ℝ) :
    (∫ x : E, translationDifference φ (t • EuclideanSpace.basisFun (Fin 2) ℝ i) x ^ 2) ≤
      (2 * (volume (tsupport φ)).toReal * (K : ℝ) ^ 2) * t ^ 2 := by
  let a := t • EuclideanSpace.basisFun (Fin 2) ℝ i
  let C := (K : ℝ) ^ 2 * t ^ 2
  let g := (tsupport φ).indicator (fun _ : E ↦ C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgc : Integrable g volume :=
    (integrable_indicator_iff hs.isCompact.measurableSet).mpr
      (integrableOn_const hs.isCompact.measure_lt_top.ne)
  have hgt : Integrable (fun x ↦ g (x + a)) volume :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable hgc
  have hm := hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume)
  have hi := (memLp_translationDifference hm a).integrable_sq
  have hb (x : E) : translationDifference φ a x ^ 2 ≤ C := by
    have h := hφ.norm_sub_le (x + a) x
    have ha : ‖(x + a) - x‖ = |t| := by
      rw [add_sub_cancel_left, norm_smul,
        (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs]
    rw [ha, Real.norm_eq_abs] at h
    have hp := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (K : ℝ) * |t|) |>.mpr h
    simpa only [translationDifference, C, mul_pow, sq_abs] using hp
  have hb2 (x : E) : translationDifference φ a x ^ 2 ≤ g x + g (x + a) := by
    by_cases hx : x ∈ tsupport φ
    · rw [show g x = C by exact indicator_of_mem hx _]
      exact (hb x).trans (le_add_of_nonneg_right (indicator_nonneg (fun _ _ ↦ hC) _))
    · by_cases hy : x + a ∈ tsupport φ
      · rw [show g x = 0 by exact indicator_of_notMem hx _,
          show g (x + a) = C by exact indicator_of_mem hy _, zero_add]
        exact hb x
      · rw [show g x = 0 by exact indicator_of_notMem hx _,
          show g (x + a) = 0 by exact indicator_of_notMem hy _, zero_add]
        rw [translationDifference, image_eq_zero_of_notMem_tsupport hy,
          image_eq_zero_of_notMem_tsupport hx, sub_self, zero_pow two_ne_zero]
  calc
    _ ≤ ∫ x : E, g x + g (x + a) := integral_mono hi (hgc.add hgt) hb2
    _ = _ := by
      rw [integral_add hgc hgt,
        (measurePreserving_add_right volume a).integral_comp
          (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding,
        show (∫ x : E, g x) = (volume (tsupport φ)).toReal * C by
          dsimp [g]
          rw [integral_indicator hs.isCompact.measurableSet, integral_const]
          simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]]
      dsimp [C]
      ring

/-- The actual integrated jump square is measurable as a function of its jump length. -/
theorem measurable_integral_coordinate_translationDifference_sq {φ : E → ℝ}
    (hφ : Continuous φ) (i : Fin 2) :
    Measurable (fun t : ℝ ↦ ∫ x : E,
      translationDifference φ (t • EuclideanSpace.basisFun (Fin 2) ℝ i) x ^ 2) := by
  have hm : StronglyMeasurable (fun p : ℝ × E ↦
      translationDifference φ (p.1 • EuclideanSpace.basisFun (Fin 2) ℝ i) p.2 ^ 2) :=
    (by unfold translationDifference; fun_prop : Continuous _).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- The actual integrated jump square is integrable against the entire singular measure. -/
theorem integrable_integral_coordinate_translationDifference_sq {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    Integrable (fun t : ℝ ↦ ∫ x : E,
      translationDifference φ (t • EuclideanSpace.basisFun (Fin 2) ℝ i) x ^ 2)
        (stableJumpMeasure α) := by
  let g := fun t : ℝ ↦ ∫ x : E,
    translationDifference φ (t • EuclideanSpace.basisFun (Fin 2) ℝ i) x ^ 2
  have hm := measurable_integral_coordinate_translationDifference_sq hφ.continuous i
  have hg0 (t : ℝ) : 0 ≤ g t := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hf := hφ.continuous.memLp_of_hasCompactSupport hs
    (p := (2 : ℝ≥0∞)) (μ := volume)
  have hi : IntegrableOn (fun t ↦ t ^ (-1 - α) • g t) (Ioi 0) :=
    integrable_stable_weighted_difference hα0 hα2 (by norm_num : (0 : ℝ) < 1) g
      hm.aestronglyMeasurable
      (fun t _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
        exact integral_coordinate_translationDifference_sq_le_quadratic hφ hs i t)
      (fun t _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
        exact integral_translationDifference_sq_le_four hf _)
  unfold stableJumpMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply (hi.const_mul (stableNormalization α)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [ENNReal.toReal_ofReal (mul_nonneg
    (stableNormalization_pos hα0 hα2).le (Real.rpow_nonneg ht.le _)), smul_eq_mul]
  dsimp [g]
  rw [show -(1 + α) = -1 - α by ring]
  ring

/-- Every actual compact Lipschitz test has both full singular jump increments in L². -/
theorem memLp_coordinateJump_of_compact_lipschitz {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    MemLp (coordinateJump φ i) 2 (spatialJumpMeasure α) := by
  have hc := hφ.continuous
  have hm : Continuous (coordinateJump φ i) := by
    unfold coordinateJump coordinateJumpPoint
    fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  change Integrable (fun p : E × ℝ ↦ coordinateJump φ i p ^ 2)
    (volume.prod (stableJumpMeasure α))
  apply (integrable_prod_iff' (hm.pow 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with t
    exact (memLp_translationDifference
      (hφ.continuous.memLp_of_hasCompactSupport hs (p := (2 : ℝ≥0∞)) (μ := volume))
      (t • EuclideanSpace.basisFun (Fin 2) ℝ i)).integrable_sq
  · have hi := integrable_integral_coordinate_translationDifference_sq hα0 hα2 hφ hs i
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs, coordinateJump,
      coordinateJumpPoint,
      translationDifference] using hi

/-- The genuine energy graph element represented by an actual compact Lipschitz function. -/
def stableJumpCompactLipschitzTest {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) :
    StableJumpEnergySpace α := by
  let hv := hφ.continuous.memLp_of_hasCompactSupport hs
    (p := (2 : ℝ≥0∞)) (μ := volume)
  let hj := fun i ↦ memLp_coordinateJump_of_compact_lipschitz hα0 hα2 hφ hs i
  refine ⟨WithLp.toLp 2 (hv.toLp φ,
    WithLp.toLp 2 fun i ↦ (hj i).toLp (coordinateJump φ i)), ?_⟩
  change ∀ i : Fin 2, ∀ᵐ p ∂spatialJumpMeasure α,
    (hj i).toLp (coordinateJump φ i) p = coordinateJump (hv.toLp φ : E → ℝ) i p
  intro i
  filter_upwards [(hj i).coeFn_toLp,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae hv.coeFn_toLp,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae hv.coeFn_toLp] with p hp hx hy
  simp only [hp, coordinateJump, hx, hy]

/-- The genuine compact test value equals the original function almost everywhere. -/
theorem stableJumpCompactLipschitzTest_value_ae {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) :
    (stableJumpValue α (stableJumpCompactLipschitzTest hα0 hα2 hφ hs) : E → ℝ)
      =ᵐ[volume] φ :=
  (hφ.continuous.memLp_of_hasCompactSupport hs
    (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp

/-- An actual support inclusion places the genuine compact test in the zero-exterior space. -/
theorem stableJumpCompactLipschitzTest_mem_supported {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hs : HasCompactSupport φ) {S : Set E}
    (hS : MeasurableSet S) (hsub : tsupport φ ⊆ S) :
    stableJumpCompactLipschitzTest hα0 hα2 hφ hs ∈ stableJumpSupported α S := by
  rw [mem_stableJumpSupported_iff α hS]
  filter_upwards [stableJumpCompactLipschitzTest_value_ae hα0 hα2 hφ hs] with x hx
  intro hxo
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport (fun hx ↦ hxo (hsub hx))

/-- Genuine compact C¹ tests belong to the full singular graph and every containing domain. -/
theorem exists_stableJumpCompactC1Test {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∃ V : StableJumpEnergySpace α, (stableJumpValue α V : E → ℝ) =ᵐ[volume] φ ∧
      ∀ S : Set E, MeasurableSet S → tsupport φ ⊆ S → V ∈ stableJumpSupported α S := by
  obtain ⟨K, hLip⟩ := hφ.lipschitzWith_of_hasCompactSupport hs one_ne_zero
  exact ⟨stableJumpCompactLipschitzTest hα0 hα2 hLip hs,
    stableJumpCompactLipschitzTest_value_ae hα0 hα2 hLip hs,
    fun _ hS hsub ↦ stableJumpCompactLipschitzTest_mem_supported hα0 hα2 hLip hs hS hsub⟩

end PartialBalayage.Maximal.Square
