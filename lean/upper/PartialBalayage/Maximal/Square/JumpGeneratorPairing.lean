/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpCompactTests
public import PartialBalayage.Maximal.Square.GeneratorCutoff

/-!
# The actual jump form and physical singular-integral generator

Spatial translation invariance turns the product of two jump increments into a
second difference of the test function. The small-jump cancellation is kept
intact throughout the full singular integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open PartialBalayage.Linear
open scoped NNReal ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Actual integrability against the jump measure equals weighted half-line integrability. -/
theorem integrable_stableJumpMeasure_iff {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (g : ℝ → ℝ) :
    Integrable g (stableJumpMeasure α) ↔
      IntegrableOn (fun t ↦ t ^ (-1 - α) * g t) (Ioi 0) := by
  unfold stableJumpMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have he : (fun t : ℝ ↦
      (ENNReal.ofReal (stableNormalization α * t ^ (-(1 + α)))).toReal • g t)
      =ᵐ[volume.restrict (Ioi 0)] fun t ↦ stableNormalization α * (t ^ (-1 - α) * g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.toReal_ofReal (mul_nonneg (stableNormalization_pos hα0 hα2).le
      (Real.rpow_nonneg ht.le _)), smul_eq_mul,
      show -(1 + α) = -1 - α by ring]
    ring
  rw [integrable_congr he,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (stableNormalization_pos hα0 hα2).ne')]
  rfl

/-- The true jump integral has the exact physical half-line normalization. -/
theorem integral_stableJumpMeasure {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (g : ℝ → ℝ) :
    (∫ t, g t ∂stableJumpMeasure α) =
      stableNormalization α * ∫ t in Ioi 0, t ^ (-1 - α) * g t := by
  unfold stableJumpMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (mul_nonneg (stableNormalization_pos hα0 hα2).le
    (Real.rpow_nonneg ht.le _)), smul_eq_mul,
    show -(1 + α) = -1 - α by ring]
  ring

/-- Quadratic and bounded actual functions are integrable against the full jump measure. -/
theorem integrable_stableJumpMeasure_of_bounds {α r M₂ M₀ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hnear : ∀ t ∈ Ioc 0 r, ‖g t‖ ≤ M₂ * t ^ 2)
    (hfar : ∀ t ∈ Ioi r, ‖g t‖ ≤ 4 * M₀) :
    Integrable g (stableJumpMeasure α) := by
  rw [integrable_stableJumpMeasure_iff hα0 hα2]
  simpa only [smul_eq_mul] using
    integrable_stable_weighted_difference hα0 hα2 hr g hg hnear hfar

/-- The full absolute jump integral has its exact quadratic-plus-tail upper bound. -/
theorem integral_norm_stableJumpMeasure_le {α r M₂ M₀ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hnear : ∀ t ∈ Ioc 0 r, ‖g t‖ ≤ M₂ * t ^ 2)
    (hfar : ∀ t ∈ Ioi r, ‖g t‖ ≤ 4 * M₀) :
    (∫ t, ‖g t‖ ∂stableJumpMeasure α) ≤ stableNormalization α *
      (M₂ * r ^ (2 - α) / (2 - α) + 4 * M₀ * r ^ (-α) / α) := by
  have hb := norm_integral_stable_weighted_difference_le hα0 hα2 hr (fun t ↦ ‖g t‖)
    hg.norm (fun t ht ↦ by simpa only [norm_norm] using hnear t ht)
    (fun t ht ↦ by simpa only [norm_norm] using hfar t ht)
  have hn : 0 ≤ ∫ t in Ioi 0, t ^ (-1 - α) * ‖g t‖ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _)
  simp only [smul_eq_mul] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hn] at hb
  rw [integral_stableJumpMeasure hα0 hα2]
  exact mul_le_mul_of_nonneg_left hb (stableNormalization_pos hα0 hα2).le

/-- Exact translation integration by parts for genuine square-integrable functions. -/
theorem integral_translationDifference_mul {u φ : E → ℝ}
    (hu : MemLp u 2 volume) (hφ : MemLp φ 2 volume) (a : E) :
    (∫ x : E, translationDifference u a x * translationDifference φ a x) =
      -(∫ x : E, u x * (φ (x + a) + φ (x - a) - 2 * φ x)) := by
  have hua := hu.comp_measurePreserving (measurePreserving_add_right volume a)
  have hφa := hφ.comp_measurePreserving (measurePreserving_add_right volume a)
  have hφn := hφ.comp_measurePreserving (measurePreserving_add_right volume (-a))
  have hii : Integrable (fun x : E ↦ u (x + a) * φ (x + a)) volume :=
    hua.integrable_mul hφa
  have hij : Integrable (fun x : E ↦ u (x + a) * φ x) volume := hua.integrable_mul hφ
  have hji : Integrable (fun x : E ↦ u x * φ (x + a)) volume := hu.integrable_mul hφa
  have hjj : Integrable (fun x : E ↦ u x * φ x) volume := hu.integrable_mul hφ
  have hjn : Integrable (fun x : E ↦ u x * φ (x - a)) volume := by
    have hn : Integrable (fun x : E ↦ u x * φ (x + -a)) volume := hu.integrable_mul hφn
    simpa only [sub_eq_add_neg] using hn
  have heii : (∫ x : E, u (x + a) * φ (x + a)) = ∫ x : E, u x * φ x :=
    (measurePreserving_add_right volume a).integral_comp
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (fun x ↦ u x * φ x)
  have heij : (∫ x : E, u (x + a) * φ x) = ∫ x : E, u x * φ (x - a) := by
    simpa only [add_sub_cancel_right] using
      (measurePreserving_add_right volume a).integral_comp
        (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
        (fun x ↦ u x * φ (x - a))
  calc
    _ = ∫ x : E, (u (x + a) * φ (x + a) - u (x + a) * φ x) -
        (u x * φ (x + a) - u x * φ x) := by
      congr 1
      funext x
      dsimp [translationDifference]
      ring
    _ = _ := by
      have e1 := integral_sub (hii.sub hij) (hji.sub hjj)
      have e2 := integral_sub hii hij
      have e3 := integral_sub hji hjj
      simp only [Pi.sub_apply] at e1 e2 e3
      rw [e1, e2, e3, heii, heij]
      have he : (fun x : E ↦ u x * (φ (x + a) + φ (x - a) - 2 * φ x)) =
          fun x ↦ (u x * φ (x + a) + u x * φ (x - a)) - 2 * (u x * φ x) := by
        funext x
        ring
      have e4 := integral_sub (hji.add hjn) (hjj.const_mul 2)
      have e5 := integral_add hji hjn
      simp only [Pi.add_apply] at e4 e5
      rw [he, e4, e5, integral_const_mul]
      ring

/-- Compact C² tests have an actual second difference integrable over space and all jumps. -/
theorem integrable_value_mul_coordinateSecondDifference {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (i : Fin 2) :
    Integrable (fun p : E × ℝ ↦
      u p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α) := by
  obtain ⟨M, K, hM, hd, hLip⟩ := compactC2_coordinateLine_bounds φ hφ hs
  have hg : Continuous (fun p : E × ℝ ↦
      stableSecondDifference (coordinateLine φ p.1 i) p.2) := by
    unfold stableSecondDifference coordinateLine
    have hc := hφ.continuous
    fun_prop
  have hm : AEStronglyMeasurable (fun p : E × ℝ ↦
      u p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2)
        (spatialJumpMeasure α) :=
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α))).mul hg.aestronglyMeasurable
  have hi (x : E) : Integrable (stableSecondDifference (coordinateLine φ x i))
      (stableJumpMeasure α) :=
    integrable_stableJumpMeasure_of_bounds hα0 hα2 (by norm_num : (0 : ℝ) < 1) _
      (continuous_stableSecondDifference (hd x i).continuous).aestronglyMeasurable
      (fun t ht ↦ norm_stableSecondDifference_le_quadratic (hd x i) (hLip x i) ht.1.le)
      (fun t _ ↦ norm_stableSecondDifference_le_four (fun _ ↦ hM _) t)
  have hb (x : E) :
      (∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖ ∂stableJumpMeasure α) ≤
        stableNormalization α * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α) := by
    simpa only [Real.one_rpow, mul_one] using
      integral_norm_stableJumpMeasure_le hα0 hα2 (by norm_num : (0 : ℝ) < 1) _
        (continuous_stableSecondDifference (hd x i).continuous).aestronglyMeasurable
        (fun t ht ↦ norm_stableSecondDifference_le_quadratic (hd x i) (hLip x i) ht.1.le)
        (fun t _ ↦ norm_stableSecondDifference_le_four (fun _ ↦ hM _) t)
  change Integrable _ (volume.prod (stableJumpMeasure α))
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards with x
    exact (hi x).const_mul (u x)
  · apply (hu.norm.mul_const
      (stableNormalization α * ((2 * (K : ℝ)) / (2 - α) + 4 * M / α))).mono'
      hm.norm.integral_prod_right'
    filter_upwards with x
    simp only [norm_mul, integral_const_mul]
    have hn : ‖∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖
        ∂stableJumpMeasure α‖ =
        ∫ t, ‖stableSecondDifference (coordinateLine φ x i) t‖ ∂stableJumpMeasure α := by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    rw [norm_norm, hn]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)

/-- Fubini identifies the genuine full second-difference pairing with the original generator. -/
theorem integral_value_mul_coordinateSecondDifference {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (i : Fin 2) :
    (∫ p, u p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2
      ∂spatialJumpMeasure α) = stableNormalization α *
        ∫ x : E, u x * stableGeneratorIntegral α (coordinateLine φ x i) := by
  have hi := integrable_value_mul_coordinateSecondDifference hα0 hα2 u hu φ hφ hs i
  rw [spatialJumpMeasure, integral_prod _ hi, ← integral_const_mul]
  congr 1
  funext x
  dsimp only
  rw [integral_const_mul, integral_stableJumpMeasure hα0 hα2]
  unfold stableGeneratorIntegral
  simp only [smul_eq_mul]
  ring

/-- A state with actual L¹ value pairs integrably with each true coordinate generator. -/
theorem integrable_value_mul_coordinateGenerator {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) (i : Fin 2) :
    Integrable (fun x : E ↦ u x * stableGeneratorIntegral α (coordinateLine φ x i))
      volume := by
  have hi := integrable_value_mul_coordinateSecondDifference hα0 hα2 u hu φ hφ hs i
  have he : (fun x : E ↦ ∫ t, u x * stableSecondDifference (coordinateLine φ x i) t
      ∂stableJumpMeasure α) = fun x ↦ stableNormalization α *
        (u x * stableGeneratorIntegral α (coordinateLine φ x i)) := by
    funext x
    rw [integral_const_mul, integral_stableJumpMeasure hα0 hα2]
    unfold stableGeneratorIntegral
    simp only [smul_eq_mul]
    ring
  have ht : Integrable (fun x : E ↦ stableNormalization α *
      (u x * stableGeneratorIntegral α (coordinateLine φ x i))) volume := by
    rw [← he]
    exact hi.integral_prod_left
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (stableNormalization_pos hα0 hα2).ne') _).mp ht

/-- Genuine L¹ state values pair integrably with the original full normalized generator. -/
theorem integrable_value_mul_coordinateStableGenerator {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hs : HasCompactSupport φ) :
    Integrable (fun x : E ↦ u x * coordinateStableGenerator α φ x) volume := by
  have he : (fun x : E ↦ u x * coordinateStableGenerator α φ x) =
      fun x ↦ stableNormalization α * ∑ i : Fin 2,
        u x * stableGeneratorIntegral α (coordinateLine φ x i) := by
    funext x
    unfold coordinateStableGenerator
    rw [← Finset.mul_sum]
    ring
  rw [he]
  exact (integrable_finsetSum _
    (fun i _ ↦ integrable_value_mul_coordinateGenerator hα0 hα2 u hu φ hφ hs i)).const_mul _

private theorem integral_coordinateJump_mul_compactC2 {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (U : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ) volume)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    (∫ p, coordinateJump (stableJumpValue α U : E → ℝ) i p * coordinateJump φ i p
      ∂spatialJumpMeasure α) = -(stableNormalization α *
        ∫ x : E, stableJumpValue α U x *
          stableGeneratorIntegral α (coordinateLine φ x i)) := by
  let u := stableJumpValue α U
  have hum := Lp.memLp u
  have hφm := hφ.continuous.memLp_of_hasCompactSupport hs
    (p := (2 : ℝ≥0∞)) (μ := volume)
  obtain ⟨K, hLip⟩ :=
    (hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).lipschitzWith_of_hasCompactSupport
      hs one_ne_zero
  have huj : MemLp (coordinateJump (u : E → ℝ) i) 2 (spatialJumpMeasure α) :=
    MemLp.ae_eq (stableJumpData_ae α U i) (Lp.memLp (stableJumpData α U i))
  have hφj := memLp_coordinateJump_of_compact_lipschitz hα0 hα2 hLip hs i
  have hij : Integrable (fun p ↦ coordinateJump (u : E → ℝ) i p * coordinateJump φ i p)
      (spatialJumpMeasure α) := huj.integrable_mul hφj
  have hsij := integrable_value_mul_coordinateSecondDifference hα0 hα2 u hu φ hφ hs i
  calc
    _ = ∫ t, (∫ x : E,
        coordinateJump (u : E → ℝ) i (x, t) * coordinateJump φ i (x, t))
        ∂stableJumpMeasure α := integral_prod_symm _ hij
    _ = ∫ t, -(∫ x : E, u x * stableSecondDifference (coordinateLine φ x i) t)
        ∂stableJumpMeasure α := by
      congr 1
      funext t
      simpa only [coordinateJump, coordinateJumpPoint, translationDifference,
        stableSecondDifference, coordinateLine, neg_smul, zero_smul, add_zero,
        smul_eq_mul, sub_eq_add_neg] using integral_translationDifference_mul hum hφm
          (t • EuclideanSpace.basisFun (Fin 2) ℝ i)
    _ = -(∫ p, u p.1 * stableSecondDifference (coordinateLine φ p.1 i) p.2
        ∂spatialJumpMeasure α) := by
      rw [integral_neg, ← integral_prod_symm _ hsij]
      rfl
    _ = _ := by rw [integral_value_mul_coordinateSecondDifference hα0 hα2 u hu φ hφ hs i]

/-- The actual singular jump form equals minus pairing with the original normalized generator. -/
theorem stableJumpForm_eq_neg_integral_coordinateStableGenerator {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (U V : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ) volume)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (hV : (stableJumpValue α V : E → ℝ) =ᵐ[volume] φ) :
    stableJumpForm α U V =
      -(∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) := by
  have hgen (i : Fin 2) := integrable_value_mul_coordinateGenerator hα0 hα2
    (stableJumpValue α U) hu φ hφ hs i
  rw [stableJumpForm_eq_sum_integral]
  have he : ∀ i : Fin 2,
      (∫ p, coordinateJump (stableJumpValue α U : E → ℝ) i p *
        coordinateJump (stableJumpValue α V : E → ℝ) i p ∂spatialJumpMeasure α) =
      -(stableNormalization α * ∫ x : E,
        stableJumpValue α U x * stableGeneratorIntegral α (coordinateLine φ x i)) := by
    intro i
    rw [← integral_coordinateJump_mul_compactC2 hα0 hα2 U hu φ hφ hs i]
    apply integral_congr_ae
    filter_upwards [(quasiMeasurePreserving_coordinateJumpPoint α i).ae hV,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α)).ae hV] with p hx hy
    simp only [coordinateJump, hx, hy]
  simp_rw [he]
  have hA : (fun x : E ↦ stableJumpValue α U x * coordinateStableGenerator α φ x) =
      fun x ↦ stableNormalization α * ∑ i : Fin 2,
        stableJumpValue α U x * stableGeneratorIntegral α (coordinateLine φ x i) := by
    funext x
    unfold coordinateStableGenerator
    rw [← Finset.mul_sum]
    ring
  rw [hA, integral_const_mul, integral_finsetSum _ (fun i _ ↦ hgen i),
    Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- Every actual compact C² function is a supported energy test with the true generator pairing. -/
theorem exists_stableJumpCompactC2Test_pairing {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (U : StableJumpEnergySpace α)
    (hu : Integrable (stableJumpValue α U : E → ℝ) volume)
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ V : StableJumpEnergySpace α, (stableJumpValue α V : E → ℝ) =ᵐ[volume] φ ∧
      stableJumpForm α U V =
        -(∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) ∧
      ∀ S : Set E, MeasurableSet S → tsupport φ ⊆ S → V ∈ stableJumpSupported α S := by
  obtain ⟨V, hV, hsV⟩ := exists_stableJumpCompactC1Test hα0 hα2
    (hφ.of_le (by norm_num)) hs
  exact ⟨V, hV,
    stableJumpForm_eq_neg_integral_coordinateStableGenerator hα0 hα2 U V hu φ hφ hs hV, hsV⟩

end PartialBalayage.Maximal.Square
