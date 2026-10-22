/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpWeakPDE
public import PartialBalayage.Linear.WholeSpaceDensityMass
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Genuine whole-space density mass from the stable generator equation

The actual large smooth cutoffs have vanishing generator against an integrable
state. Fatou first proves global density integrability; dominated convergence
then recovers exact equality of the original input and output masses.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Strictly positive Gaussian weighting preserves actual strong measurability for volume. -/
theorem aestronglyMeasurable_weightedDensity (ν : Lp ℝ 2 jumpExhaustionMeasure) :
    AEStronglyMeasurable (ν : E → ℝ) volume := by
  have hac : (volume : Measure E) ≪ jumpExhaustionMeasure :=
    withDensity_absolutelyContinuous'
      continuous_jumpExhaustionWeight.measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall (fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr
        (jumpExhaustionWeight_pos x)))
  exact (Lp.aestronglyMeasurable ν).mono_ac hac

/-- The genuine large smooth cutoff used in the physical jump exhaustion. -/
def jumpSourceCutoff (k : ℕ) (x : E) : ℝ :=
  sourceCutoffScale 2 (sourceInverseRadius k) x

theorem jumpSourceCutoff_nonneg (k : ℕ) (x : E) : 0 ≤ jumpSourceCutoff k x :=
  sourceCutoff_nonneg 2 _

theorem jumpSourceCutoff_le_one (k : ℕ) (x : E) : jumpSourceCutoff k x ≤ 1 :=
  sourceCutoff_le_one 2 _

theorem norm_jumpSourceCutoff (k : ℕ) (x : E) :
    ‖jumpSourceCutoff k x‖ = jumpSourceCutoff k x := by
  rw [Real.norm_eq_abs, abs_of_nonneg (jumpSourceCutoff_nonneg k x)]

theorem jumpSourceCutoff_contDiff (k : ℕ) : ContDiff ℝ 2 (jumpSourceCutoff k) :=
  sourceCutoffScale_contDiff 2 _

theorem jumpSourceCutoff_hasCompactSupport (k : ℕ) : HasCompactSupport (jumpSourceCutoff k) :=
  sourceCutoffScale_hasCompactSupport 2 (sourceInverseRadius_pos k)

theorem tendsto_jumpSourceCutoff (x : E) :
    Tendsto (fun k : ℕ ↦ jumpSourceCutoff k x) atTop (𝓝 1) := by
  have harg : Tendsto (fun k : ℕ ↦ sourceInverseRadius k • x) atTop (𝓝 0) := by
    simpa only [zero_smul] using tendsto_sourceInverseRadius.smul_const x
  simpa only [jumpSourceCutoff, sourceCutoffScale, sourceCutoff_zero, Function.comp_def] using
    (sourceCutoff_contDiff 2).continuous.continuousAt.tendsto.comp harg

/-- Actual integrable functions recover their integral through the genuine large cutoffs. -/
theorem tendsto_integral_mul_jumpSourceCutoff {g : E → ℝ} (hg : Integrable g volume) :
    Tendsto (fun k : ℕ ↦ ∫ x : E, g x * jumpSourceCutoff k x) atTop
      (𝓝 (∫ x : E, g x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖g x‖)
  · intro k
    exact hg.aestronglyMeasurable.mul (jumpSourceCutoff_contDiff k).continuous.aestronglyMeasurable
  · exact hg.norm
  · intro k
    filter_upwards with x
    rw [norm_mul, norm_jumpSourceCutoff]
    exact mul_le_of_le_one_right (norm_nonneg _) (jumpSourceCutoff_le_one k x)
  · filter_upwards with x
    simpa only [mul_one] using (tendsto_jumpSourceCutoff x).const_mul (g x)

/-- The actual large-cutoff generator pairing tends to zero against every integrable state. -/
theorem tendsto_integral_value_mul_jumpSourceCutoff_generator {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) :
    Tendsto (fun k : ℕ ↦ ∫ x : E, u x * coordinateStableGenerator α (jumpSourceCutoff k) x)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := sourceCutoff_coordinateStableGenerator_bound hα0 hα2
  have he (k : ℕ) : jumpSourceCutoff k =
      fun x : E ↦ sourceCutoff 2 (((k : ℝ) + 1)⁻¹ • x) := by
    funext x
    simp only [jumpSourceCutoff, sourceCutoffScale, sourceInverseRadius, one_div]
  have hb (k : ℕ) :
      ‖∫ x : E, u x * coordinateStableGenerator α (jumpSourceCutoff k) x‖ ≤
        ((∫ x : E, ‖u x‖) * C) * ((k : ℝ) + 1) ^ (-α) := by
    have hi := integrable_value_mul_coordinateStableGenerator hα0 hα2 u hu
      (jumpSourceCutoff k) (jumpSourceCutoff_contDiff k) (jumpSourceCutoff_hasCompactSupport k)
    calc
      _ ≤ ∫ x : E, ‖u x * coordinateStableGenerator α (jumpSourceCutoff k) x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : E, ‖u x‖ * (C * ((k : ℝ) + 1) ^ (-α)) := by
        apply integral_mono_ae hi.norm (hu.norm.mul_const _)
        filter_upwards with x
        rw [norm_mul, he]
        exact mul_le_mul_of_nonneg_left (hC ((k : ℝ) + 1) (by positivity) x) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring
  apply squeeze_zero_norm hb
  have ht : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  simpa only [mul_zero, Function.comp_apply] using
    ((tendsto_rpow_neg_atTop hα0).comp ht).const_mul ((∫ x : E, ‖u x‖) * C)

/-- The actual compact generator PDE and L¹ state force genuine global density integrability
and exact equality of physical input and output masses. -/
theorem integrable_weightedDensity_mass_eq_of_jumpPDE {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (u f : Lp ℝ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℝ) volume) (hf : Integrable (f : E → ℝ) volume)
    (ν : Lp ℝ 2 jumpExhaustionMeasure) (hνpos : ∀ᵐ x ∂volume, 0 ≤ ν x)
    (hpde : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ x : E, u x * coordinateStableGenerator α φ x) = ∫ x : E, (ν x - f x) * φ x) :
    Integrable (ν : E → ℝ) volume ∧ (∫ x : E, ν x) = ∫ x : E, f x := by
  have hνmeas := aestronglyMeasurable_weightedDensity ν
  have hνi (k : ℕ) : Integrable (fun x : E ↦ ν x * jumpSourceCutoff k x) volume :=
    integrable_weightedDensity_mul_compactTest ν (jumpSourceCutoff k)
      (jumpSourceCutoff_contDiff k).continuous (jumpSourceCutoff_hasCompactSupport k)
  have hfi (k : ℕ) : Integrable (fun x : E ↦ f x * jumpSourceCutoff k x) volume := by
    apply hf.norm.mono'
      ((Lp.aestronglyMeasurable f).mul
        (jumpSourceCutoff_contDiff k).continuous.aestronglyMeasurable)
    filter_upwards with x
    change ‖f x * jumpSourceCutoff k x‖ ≤ ‖f x‖
    rw [norm_mul, norm_jumpSourceCutoff]
    exact mul_le_of_le_one_right (norm_nonneg _) (jumpSourceCutoff_le_one k x)
  have he (k : ℕ) : (∫ x : E, ν x * jumpSourceCutoff k x) =
      (∫ x : E, f x * jumpSourceCutoff k x) +
        ∫ x : E, u x * coordinateStableGenerator α (jumpSourceCutoff k) x := by
    have h := hpde (jumpSourceCutoff k) (jumpSourceCutoff_contDiff k)
      (jumpSourceCutoff_hasCompactSupport k)
    have hg : (fun x : E ↦ (ν x - f x) * jumpSourceCutoff k x) =
        fun x ↦ ν x * jumpSourceCutoff k x - f x * jumpSourceCutoff k x := by
      funext x
      ring
    have hint := integral_sub (hνi k) (hfi k)
    rw [hg, hint] at h
    linarith
  have htν : Tendsto (fun k : ℕ ↦ ∫ x : E, ν x * jumpSourceCutoff k x)
      atTop (𝓝 (∫ x : E, f x)) := by
    simpa only [he, add_zero] using (tendsto_integral_mul_jumpSourceCutoff hf).add
      (tendsto_integral_value_mul_jumpSourceCutoff_generator hα0 hα2 u hu)
  have hνχpos (k : ℕ) : ∀ᵐ x ∂volume, 0 ≤ ν x * jumpSourceCutoff k x :=
    hνpos.mono fun x hx ↦ mul_nonneg hx (jumpSourceCutoff_nonneg k x)
  have htENN : Tendsto (fun k : ℕ ↦ ∫⁻ x : E,
      ENNReal.ofReal (ν x * jumpSourceCutoff k x)) atTop
        (𝓝 (ENNReal.ofReal (∫ x : E, f x))) := by
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hνi _) (hνχpos _)]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp htν
  have hpt (x : E) : liminf (fun k : ℕ ↦
      ENNReal.ofReal (ν x * jumpSourceCutoff k x)) atTop = ENNReal.ofReal (ν x) := by
    apply Tendsto.liminf_eq
    simpa only [mul_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_jumpSourceCutoff x).const_mul (ν x))
  have hmeas (k : ℕ) : AEMeasurable
      (fun x : E ↦ ENNReal.ofReal (ν x * jumpSourceCutoff k x)) volume := by
    have h : AEStronglyMeasurable (fun x : E ↦ ν x * jumpSourceCutoff k x) volume :=
      hνmeas.mul (jumpSourceCutoff_contDiff k).continuous.aestronglyMeasurable
    exact h.aemeasurable.ennreal_ofReal
  have hmass : (∫⁻ x : E, ‖ν x‖ₑ) ≤ ENNReal.ofReal (∫ x : E, f x) := by
    calc
      _ = ∫⁻ x : E, ENNReal.ofReal (ν x) := by
        apply lintegral_congr_ae
        filter_upwards [hνpos] with x hx
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]
      _ = ∫⁻ x : E, liminf (fun k : ℕ ↦
          ENNReal.ofReal (ν x * jumpSourceCutoff k x)) atTop := by simp_rw [hpt]
      _ ≤ liminf (fun k : ℕ ↦ ∫⁻ x : E,
          ENNReal.ofReal (ν x * jumpSourceCutoff k x)) atTop :=
        lintegral_liminf_le' hmeas
      _ = _ := htENN.liminf_eq
  have hνint : Integrable (ν : E → ℝ) volume :=
    ⟨hνmeas, hasFiniteIntegral_iff_enorm.mpr (hmass.trans_lt ENNReal.ofReal_lt_top)⟩
  exact ⟨hνint, tendsto_nhds_unique (tendsto_integral_mul_jumpSourceCutoff hνint) htν⟩

set_option maxHeartbeats 800000 in
/-- Actual nonnegative L¹ and L² input admits a global positive jump state and an ordinary
volume L² capped density, with exact physical mass and the genuine compact generator PDE. -/
theorem exists_positive_stableJump_global_density {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (κ : ℝ≥0) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : Integrable (f : E → ℝ) volume)
    (hfpos : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∃ (ν : Lp ℝ 2 (volume : Measure E)) (U : StableJumpEnergySpace α),
      (∀ᵐ x ∂volume, 0 ≤ ν x ∧ ν x ≤ (κ : ℝ)) ∧
      Integrable (ν : E → ℝ) volume ∧ (∫ x : E, ν x) = ∫ x : E, f x ∧
      ‖ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x : E, ‖f x‖ ∧
      (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α U x) ∧
      Integrable (stableJumpValue α U : E → ℝ) volume ∧
      (∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        (∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) =
          ∫ x : E, (ν x - f x) * φ x) := by
  obtain ⟨v, U, hvbound, hUpos, hUint, hpde⟩ :=
    exists_positive_stableJumpCompactWeak_solution hα0 hα2 κ hκ f hfpos
  obtain ⟨hvint, hvmass⟩ := integrable_weightedDensity_mass_eq_of_jumpPDE hα0 hα2
    (stableJumpValue α U) f hUint hf v (hvbound.mono fun _ h ↦ h.1) hpde
  have hvmeas := aestronglyMeasurable_weightedDensity v
  have hvm : MemLp (v : E → ℝ) 2 volume := by
    apply (memLp_two_iff_integrable_sq hvmeas).mpr
    apply (hvint.const_mul (κ : ℝ)).mono' (hvmeas.pow 2)
    filter_upwards [hvbound] with x hx
    change ‖v x ^ 2‖ ≤ (κ : ℝ) * v x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hx.1, hx.2]
  let ν := hvm.toLp (v : E → ℝ)
  have hνae : (ν : E → ℝ) =ᵐ[volume] v := hvm.coeFn_toLp
  have hνbound : ∀ᵐ x ∂volume, 0 ≤ ν x ∧ ν x ≤ (κ : ℝ) := by
    filter_upwards [hνae, hvbound] with x he hx
    rwa [he]
  have hνint : Integrable (ν : E → ℝ) volume := hvint.congr hνae.symm
  have hνmass : (∫ x : E, ν x) = ∫ x : E, f x := (integral_congr_ae hνae).trans hvmass
  have hnormmass : (∫ x : E, ‖ν x‖) = ∫ x : E, ‖f x‖ := by
    calc
      _ = ∫ x : E, ν x := by
        apply integral_congr_ae
        filter_upwards [hνbound] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      _ = ∫ x : E, f x := hνmass
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hfpos] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx]
  let mass : ℝ≥0 := ⟨∫ x : E, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩
  have hνcap : ν ∈ normMassCap volume κ mass := by
    constructor
    · filter_upwards [hνbound] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    · rw [← ofReal_integral_norm_eq_lintegral_enorm hνint, hnormmass]
      change ENNReal.ofReal (mass : ℝ) ≤ (mass : ℝ≥0∞)
      rw [ENNReal.ofReal_coe_nnreal]
  refine ⟨ν, U, hνbound, hνint, hνmass, norm_sq_le_of_mem_normMassCap hνcap,
    hUpos, hUint, ?_⟩
  intro φ hφ hs
  rw [hpde φ hφ hs]
  apply integral_congr_ae
  filter_upwards [hνae] with x hx
  rw [hx]

end PartialBalayage.Maximal.Square
