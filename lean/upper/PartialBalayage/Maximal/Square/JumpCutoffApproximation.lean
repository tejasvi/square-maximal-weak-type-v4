/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpCutoffEnergy

/-!
# Genuine large-cutoff approximation in the singular jump graph

Actual smooth large cutoffs converge to one in the value and increment
coordinates. Their product-rule error decays at the genuine stable order.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual compact smooth cutoff has a genuine global Lipschitz constant. -/
theorem exists_lipschitzWith_jumpSource : ∃ K : ℝ≥0, LipschitzWith K (sourceCutoff 2) :=
  (sourceCutoff_contDiff 2).lipschitzWith_of_hasCompactSupport
    (sourceCutoff_hasCompactSupport 2) (by norm_num)

/-- A fixed genuine Lipschitz constant of the actual smooth source cutoff. -/
def jumpSourceLipschitzConstant : ℝ≥0 := Classical.choose exists_lipschitzWith_jumpSource

theorem lipschitzWith_jumpSource :
    LipschitzWith jumpSourceLipschitzConstant (sourceCutoff 2) :=
  Classical.choose_spec exists_lipschitzWith_jumpSource

theorem lipschitzWith_jumpSourceCutoff (k : ℕ) :
    LipschitzWith (jumpSourceLipschitzConstant * ‖sourceInverseRadius k‖₊)
      (jumpSourceCutoff k) :=
  lipschitzWith_jumpSource.comp (lipschitzWith_smul (sourceInverseRadius k))

theorem norm_jumpSourceCutoff_le_one (k : ℕ) (x : E) : ‖jumpSourceCutoff k x‖ ≤ 1 := by
  rw [norm_jumpSourceCutoff]
  exact jumpSourceCutoff_le_one k x

/-- The original cutoff scaled by a positive radius has actual stable-order error decay. -/
theorem integral_value_mul_scaled_sourceJump_sq_le {α r : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r)
    (u : Lp ℝ 2 (volume : Measure E)) (i : Fin 2) :
    (∫ p : E × ℝ, (u p.1 * coordinateJump
      (fun x : E ↦ sourceCutoff 2 (r⁻¹ • x)) i p) ^ 2 ∂spatialJumpMeasure α) ≤
      ((∫ x : E, u x ^ 2) * stableNormalization α *
        ((jumpSourceLipschitzConstant : ℝ) ^ 2 / (2 - α) + 4 / α)) * r ^ (-α) := by
  have hη := lipschitzWith_jumpSource.comp (lipschitzWith_smul r⁻¹)
  have hM (x : E) : ‖sourceCutoff 2 (r⁻¹ • x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceCutoff_nonneg 2 _)]
    exact sourceCutoff_le_one 2 _
  have hp : r ^ (2 - α) = r ^ (2 : ℕ) * r ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_two]
  have he : ((jumpSourceLipschitzConstant * ‖r⁻¹‖₊ : ℝ≥0) : ℝ) ^ 2 *
      r ^ (2 - α) / (2 - α) + 4 * (1 : ℝ) ^ 2 * r ^ (-α) / α =
        ((jumpSourceLipschitzConstant : ℝ) ^ 2 / (2 - α) + 4 / α) * r ^ (-α) := by
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hp]
    field_simp
  calc
    _ ≤ (∫ x : E, u x ^ 2) * stableNormalization α *
        (((jumpSourceLipschitzConstant * ‖r⁻¹‖₊ : ℝ≥0) : ℝ) ^ 2 *
          r ^ (2 - α) / (2 - α) + 4 * (1 : ℝ) ^ 2 * r ^ (-α) / α) :=
      integral_value_mul_coordinateJump_sq_le hα0 hα2 hr u hη hM i
    _ = _ := by rw [he]; ring

/-- The true full product-rule cutoff error square tends to zero. -/
theorem tendsto_integral_value_mul_jumpSourceCutoff_jump_sq {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E)) (i : Fin 2) :
    Tendsto (fun k : ℕ ↦ ∫ p : E × ℝ,
      (u p.1 * coordinateJump (jumpSourceCutoff k) i p) ^ 2 ∂spatialJumpMeasure α)
        atTop (𝓝 0) := by
  have he (k : ℕ) : jumpSourceCutoff k =
      fun x : E ↦ sourceCutoff 2 (((k : ℝ) + 1)⁻¹ • x) := by
    funext x
    simp only [jumpSourceCutoff, sourceCutoffScale, sourceInverseRadius, one_div]
  have hb (k : ℕ) : (∫ p : E × ℝ,
      (u p.1 * coordinateJump (jumpSourceCutoff k) i p) ^ 2 ∂spatialJumpMeasure α) ≤
        ((∫ x : E, u x ^ 2) * stableNormalization α *
          ((jumpSourceLipschitzConstant : ℝ) ^ 2 / (2 - α) + 4 / α)) *
            ((k : ℝ) + 1) ^ (-α) := by
    rw [he]
    exact integral_value_mul_scaled_sourceJump_sq_le hα0 hα2
      (by positivity : 0 < (k : ℝ) + 1) u i
  apply squeeze_zero (fun k : ℕ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) hb
  have ht : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, mul_zero] using
    ((tendsto_rpow_neg_atTop hα0).comp ht).const_mul
      ((∫ x : E, u x ^ 2) * stableNormalization α *
        ((jumpSourceLipschitzConstant : ℝ) ^ 2 / (2 - α) + 4 / α))

private theorem realLp_norm_sq_eq_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Lp ℝ 2 μ) : ‖u‖ ^ (2 : ℕ) = ∫ x, u x ^ (2 : ℕ) ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.inner_apply, pow_two]

private theorem tendsto_realLp_of_norm_sq_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ}
    (h : Tendsto (fun k ↦ ‖a k - u‖ ^ (2 : ℕ)) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

/-- Bounded measurable coefficients multiply genuine scalar L² representatives. -/
theorem memLp_boundedRealMultiplier {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (hb : ∀ x, ‖a x‖ ≤ 1)
    (u : Lp ℝ 2 μ) : MemLp (fun x ↦ a x * u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (ha.mul (Lp.aestronglyMeasurable u)) (c := (1 : ℝ))
  filter_upwards with x
  change ‖a x * u x‖ ≤ 1 * ‖u x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- Actual bounded coefficient convergence gives strong L² multiplier convergence. -/
theorem tendsto_boundedRealMultiplier {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : ℕ → X → ℝ) (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (hb : ∀ k x, ‖a k x‖ ≤ 1) (hpt : ∀ x, Tendsto (fun k ↦ a k x) atTop (𝓝 1))
    (u : Lp ℝ 2 μ) :
    Tendsto (fun k ↦ (memLp_boundedRealMultiplier μ (a k) (ha k) (hb k) u).toLp
      (fun x ↦ a k x * u x)) atTop (𝓝 u) := by
  apply tendsto_realLp_of_norm_sq_sub
  have he (k : ℕ) :
      ‖(memLp_boundedRealMultiplier μ (a k) (ha k) (hb k) u).toLp
        (fun x ↦ a k x * u x) - u‖ ^ (2 : ℕ) =
          ∫ x, (a k x * u x - u x) ^ (2 : ℕ) ∂μ := by
    rw [realLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      ((memLp_boundedRealMultiplier μ (a k) (ha k) (hb k) u).toLp
        (fun x ↦ a k x * u x)) u,
      (memLp_boundedRealMultiplier μ (a k) (ha k) (hb k) u).coeFn_toLp] with x hs hm
    rw [hs]
    simp only [Pi.sub_apply, hm]
  simp_rw [he]
  have ht : Tendsto (fun k : ℕ ↦ ∫ x, (a k x * u x - u x) ^ (2 : ℕ) ∂μ)
      atTop (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ 4 * u x ^ (2 : ℕ))
    · intro k
      exact (((ha k).mul (Lp.aestronglyMeasurable u)).sub
        (Lp.aestronglyMeasurable u)).pow 2
    · exact (Lp.memLp u).integrable_sq.const_mul 4
    · intro k
      filter_upwards with x
      have hab : |a k x| ≤ 1 := by simpa only [Real.norm_eq_abs] using hb k x
      have hn : |a k x * u x - u x| ≤ 2 * |u x| := by
        calc
          _ ≤ |a k x * u x| + |u x| := abs_sub _ _
          _ = |a k x| * |u x| + |u x| := by rw [abs_mul]
          _ ≤ 2 * |u x| := by nlinarith [abs_nonneg (u x)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hs := (sq_le_sq₀ (abs_nonneg _)
        (by positivity : 0 ≤ 2 * |u x|)).mpr hn
      nlinarith [sq_abs (a k x * u x - u x), sq_abs (u x)]
    · filter_upwards with x
      simpa only [one_mul, sub_self, zero_pow two_ne_zero] using
        (((hpt x).mul_const (u x)).sub_const (u x)).pow 2
  simpa only [integral_zero] using ht

/-- The actual state multiplied by a genuine smooth large cutoff. -/
def stableJumpLargeCutoff {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) (k : ℕ) : StableJumpEnergySpace α :=
  stableJumpLipschitzMul hα0 hα2 U (lipschitzWith_jumpSourceCutoff k)
    (norm_jumpSourceCutoff_le_one k)

theorem stableJumpLargeCutoff_value_ae {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) (k : ℕ) :
    (stableJumpValue α (stableJumpLargeCutoff hα0 hα2 U k) : E → ℝ) =ᵐ[volume]
      fun x ↦ jumpSourceCutoff k x * stableJumpValue α U x :=
  stableJumpLipschitzMul_value_ae hα0 hα2 U (lipschitzWith_jumpSourceCutoff k)
    (norm_jumpSourceCutoff_le_one k)

/-- The true large-cutoff values converge strongly in ordinary volume L². -/
theorem tendsto_stableJumpLargeCutoff_value {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) :
    Tendsto (fun k : ℕ ↦ stableJumpValue α (stableJumpLargeCutoff hα0 hα2 U k))
      atTop (𝓝 (stableJumpValue α U)) := by
  have ht := tendsto_boundedRealMultiplier (volume : Measure E) jumpSourceCutoff
    (fun k ↦ (jumpSourceCutoff_contDiff k).continuous.aestronglyMeasurable)
    norm_jumpSourceCutoff_le_one tendsto_jumpSourceCutoff (stableJumpValue α U)
  apply ht.congr'
  filter_upwards with k
  apply Lp.ext
  exact (memLp_boundedRealMultiplier (volume : Measure E) (jumpSourceCutoff k)
    (jumpSourceCutoff_contDiff k).continuous.aestronglyMeasurable
    (norm_jumpSourceCutoff_le_one k) (stableJumpValue α U)).coeFn_toLp.trans
      (stableJumpLargeCutoff_value_ae hα0 hα2 U k).symm

/-- The actual L² class of the genuine product-rule cutoff error. -/
def stableJumpLargeCutoffError {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (u : Lp ℝ 2 (volume : Measure E)) (i : Fin 2) (k : ℕ) :
    Lp ℝ 2 (spatialJumpMeasure α) :=
  (memLp_value_mul_coordinateJump hα0 hα2 u (lipschitzWith_jumpSourceCutoff k)
    (norm_jumpSourceCutoff_le_one k) i).toLp
      (fun p ↦ u p.1 * coordinateJump (jumpSourceCutoff k) i p)

theorem stableJumpLargeCutoffError_ae {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (u : Lp ℝ 2 (volume : Measure E)) (i : Fin 2) (k : ℕ) :
    (stableJumpLargeCutoffError hα0 hα2 u i k : E × ℝ → ℝ) =ᵐ[spatialJumpMeasure α]
      fun p ↦ u p.1 * coordinateJump (jumpSourceCutoff k) i p :=
  (memLp_value_mul_coordinateJump hα0 hα2 u (lipschitzWith_jumpSourceCutoff k)
    (norm_jumpSourceCutoff_le_one k) i).coeFn_toLp

/-- The genuine product-rule error converges strongly in the full singular jump L². -/
theorem tendsto_stableJumpLargeCutoffError {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (u : Lp ℝ 2 (volume : Measure E)) (i : Fin 2) :
    Tendsto (stableJumpLargeCutoffError hα0 hα2 u i) atTop (𝓝 0) := by
  apply tendsto_realLp_of_norm_sq_sub
  have he (k : ℕ) : ‖stableJumpLargeCutoffError hα0 hα2 u i k - 0‖ ^ (2 : ℕ) =
      ∫ p : E × ℝ, (u p.1 * coordinateJump (jumpSourceCutoff k) i p) ^ 2
        ∂spatialJumpMeasure α := by
    rw [sub_zero, realLp_norm_sq_eq_integral]
    exact integral_congr_ae
      ((stableJumpLargeCutoffError_ae hα0 hα2 u i k).fun_comp (fun x : ℝ ↦ x ^ (2 : ℕ)))
  simpa only [he] using tendsto_integral_value_mul_jumpSourceCutoff_jump_sq hα0 hα2 u i

private def largeCutoffMainData {α : ℝ} (U : StableJumpEnergySpace α) (i : Fin 2) (k : ℕ) :
    Lp ℝ 2 (spatialJumpMeasure α) :=
  (memLp_boundedRealMultiplier (spatialJumpMeasure α)
    (fun p : E × ℝ ↦ jumpSourceCutoff k (coordinateJumpPoint i p))
    ((jumpSourceCutoff_contDiff k).continuous.comp
      (by unfold coordinateJumpPoint; fun_prop)).aestronglyMeasurable
    (fun p ↦ norm_jumpSourceCutoff_le_one k _) (stableJumpData α U i)).toLp
      (fun p : E × ℝ ↦ jumpSourceCutoff k (coordinateJumpPoint i p) * stableJumpData α U i p)

private theorem largeCutoffMainData_ae {α : ℝ} (U : StableJumpEnergySpace α)
    (i : Fin 2) (k : ℕ) :
    (largeCutoffMainData U i k : E × ℝ → ℝ) =ᵐ[spatialJumpMeasure α]
      fun p ↦ jumpSourceCutoff k (coordinateJumpPoint i p) * stableJumpData α U i p :=
  (memLp_boundedRealMultiplier (spatialJumpMeasure α)
    (fun p : E × ℝ ↦ jumpSourceCutoff k (coordinateJumpPoint i p))
    ((jumpSourceCutoff_contDiff k).continuous.comp
      (by unfold coordinateJumpPoint; fun_prop)).aestronglyMeasurable
    (fun p ↦ norm_jumpSourceCutoff_le_one k _) (stableJumpData α U i)).coeFn_toLp

private theorem tendsto_largeCutoffMainData {α : ℝ} (U : StableJumpEnergySpace α)
    (i : Fin 2) : Tendsto (largeCutoffMainData U i) atTop (𝓝 (stableJumpData α U i)) :=
  tendsto_boundedRealMultiplier (spatialJumpMeasure α)
    (fun k (p : E × ℝ) ↦ jumpSourceCutoff k (coordinateJumpPoint i p))
    (fun k ↦ ((jumpSourceCutoff_contDiff k).continuous.comp
      (by unfold coordinateJumpPoint; fun_prop)).aestronglyMeasurable)
    (fun k p ↦ norm_jumpSourceCutoff_le_one k _) (fun p ↦ tendsto_jumpSourceCutoff _)
    (stableJumpData α U i)

private theorem stableJumpLargeCutoff_data_eq {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) (i : Fin 2) (k : ℕ) :
    stableJumpData α (stableJumpLargeCutoff hα0 hα2 U k) i = largeCutoffMainData U i k +
      stableJumpLargeCutoffError hα0 hα2 (stableJumpValue α U) i k := by
  apply Lp.ext
  filter_upwards [stableJumpData_ae α (stableJumpLargeCutoff hα0 hα2 U k) i,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae
      (stableJumpLargeCutoff_value_ae hα0 hα2 U k),
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae (stableJumpLargeCutoff_value_ae hα0 hα2 U k),
    Lp.coeFn_add (largeCutoffMainData U i k)
      (stableJumpLargeCutoffError hα0 hα2 (stableJumpValue α U) i k),
    largeCutoffMainData_ae U i k,
    stableJumpLargeCutoffError_ae hα0 hα2 (stableJumpValue α U) i k,
    stableJumpData_ae α U i] with p hp hx hy hs hm he hU
  rw [hp, hs]
  simp only [Pi.add_apply]
  rw [hm, he, hU]
  unfold coordinateJump
  rw [hx, hy]
  ring

/-- Each actual jump coordinate of the large cutoff converges strongly over all jump lengths. -/
theorem tendsto_stableJumpLargeCutoff_data_coordinate {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (U : StableJumpEnergySpace α) (i : Fin 2) :
    Tendsto (fun k : ℕ ↦ stableJumpData α (stableJumpLargeCutoff hα0 hα2 U k) i)
      atTop (𝓝 (stableJumpData α U i)) := by
  have ht := (tendsto_largeCutoffMainData U i).add
    (tendsto_stableJumpLargeCutoffError hα0 hα2 (stableJumpValue α U) i)
  simpa only [add_zero, ← stableJumpLargeCutoff_data_eq hα0 hα2 U i] using ht

/-- The actual pair of singular jump coordinates converges strongly. -/
theorem tendsto_stableJumpLargeCutoff_data {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) :
    Tendsto (fun k : ℕ ↦ stableJumpData α (stableJumpLargeCutoff hα0 hα2 U k))
      atTop (𝓝 (stableJumpData α U)) := by
  have ht : Tendsto (fun k (i : Fin 2) ↦
      stableJumpData α (stableJumpLargeCutoff hα0 hα2 U k) i) atTop
        (𝓝 (fun i : Fin 2 ↦ stableJumpData α U i)) :=
    tendsto_pi_nhds.mpr (fun i ↦ tendsto_stableJumpLargeCutoff_data_coordinate hα0 hα2 U i)
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin 2 ↦ Lp ℝ 2 (spatialJumpMeasure α))).tendsto _ |>.comp ht

/-- Every genuine energy state is strongly approximated by the actual large-cutoff states. -/
theorem tendsto_stableJumpLargeCutoff {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) :
    Tendsto (stableJumpLargeCutoff hα0 hα2 U) atTop (𝓝 U) := by
  apply tendsto_subtype_rng.mpr
  have ht := (tendsto_stableJumpLargeCutoff_value hα0 hα2 U).prodMk_nhds
    (tendsto_stableJumpLargeCutoff_data hα0 hα2 U)
  have h := (WithLp.prod_continuous_toLp 2 (Lp ℝ 2 (volume : Measure E))
    (PiLp 2 (fun _ : Fin 2 ↦ Lp ℝ 2 (spatialJumpMeasure α)))).tendsto
      (stableJumpValue α U, stableJumpData α U) |>.comp ht
  exact h

/-- Each actual cutoff approximation lies in its genuine compact support domain. -/
theorem stableJumpLargeCutoff_mem_supported {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (U : StableJumpEnergySpace α) (k : ℕ) :
    stableJumpLargeCutoff hα0 hα2 U k ∈ stableJumpSupported α (tsupport (jumpSourceCutoff k)) :=
  stableJumpLipschitzMul_mem_supported hα0 hα2 U (lipschitzWith_jumpSourceCutoff k)
    (norm_jumpSourceCutoff_le_one k)
    (jumpSourceCutoff_hasCompactSupport k).isCompact.measurableSet (Subset.refl _)

end PartialBalayage.Maximal.Square
