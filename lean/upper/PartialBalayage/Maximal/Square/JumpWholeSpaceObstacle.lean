/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpWeakEnergyMass

/-!
# Genuine whole-space positive coordinate-stable balayage

The actual finite obstacles, joint weak compactness, full graph testing, and
weak energy-mass inequality construct a positive capped density and genuine
positive state. Saturation on the active set follows from the true support
pairing. Its volume is controlled by the original physical input mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open PartialBalayage.Linear
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual active set of a genuine full singular-energy state. -/
def stableJumpActiveSet (α : ℝ) (U : StableJumpEnergySpace α) : Set E :=
  {x | stableJumpValue α U x ≠ 0}

theorem measurableSet_stableJumpActiveSet (α : ℝ) (U : StableJumpEnergySpace α) :
    MeasurableSet (stableJumpActiveSet α U) :=
  (measurableSet_eq_fun (Lp.stronglyMeasurable (stableJumpValue α U)).measurable
    measurable_const).compl

/-- True saturation and physical density mass bound the actual full-space active volume. -/
theorem cap_measure_stableJumpActiveSet {α : ℝ} (κ : ℝ≥0)
    (U : StableJumpEnergySpace α) (ν f : Lp ℝ 2 (volume : Measure E))
    (hν : Integrable (ν : E → ℝ) volume) (hf : Integrable (f : E → ℝ) volume)
    (hsat : ∀ᵐ x ∂volume, stableJumpValue α U x ≠ 0 → ν x = (κ : ℝ))
    (hmass : (∫ x : E, ‖ν x‖) ≤ ∫ x : E, ‖f x‖) :
    (κ : ℝ≥0∞) * volume (stableJumpActiveSet α U) ≤ ∫⁻ x : E, ‖f x‖ₑ := by
  calc
    _ = ∫⁻ x : E, (stableJumpActiveSet α U).indicator (fun _ ↦ (κ : ℝ≥0∞)) x := by
      rw [lintegral_indicator (measurableSet_stableJumpActiveSet α U), lintegral_const]
      simp only [Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x : E, ‖ν x‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [hsat] with x hx
      by_cases hxs : x ∈ stableJumpActiveSet α U
      · rw [indicator_of_mem hxs, hx hxs, ← ofReal_norm,
          Real.norm_eq_abs, abs_of_nonneg κ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      · rw [indicator_of_notMem hxs]
        exact zero_le
    _ ≤ _ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hν,
        ← ofReal_integral_norm_eq_lintegral_enorm hf]
      exact ENNReal.ofReal_le_ofReal hmass

/-- Positive cap and true mass give finite active volume in ordinary whole-space measure. -/
theorem measure_stableJumpActiveSet_ne_top {α : ℝ} {κ : ℝ≥0} (hκ : 0 < κ)
    (U : StableJumpEnergySpace α) (f : Lp ℝ 2 (volume : Measure E))
    (hf : Integrable (f : E → ℝ) volume)
    (hbound : (κ : ℝ≥0∞) * volume (stableJumpActiveSet α U) ≤ ∫⁻ x : E, ‖f x‖ₑ) :
    volume (stableJumpActiveSet α U) ≠ ⊤ := by
  intro ht
  have hc : (κ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hκ.ne'
  rw [ht, ENNReal.mul_top hc] at hbound
  exact (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral).not_ge hbound

set_option maxHeartbeats 1000000 in
/-- Genuine positive L¹ and L² input admits whole-space coordinate-stable balayage,
including the actual all-energy PDE, cap saturation, and finite controlled active volume. -/
theorem exists_positive_stableJump_obstacle {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (κ : ℝ≥0) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : Integrable (f : E → ℝ) volume)
    (hfpos : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∃ (ν : Lp ℝ 2 (volume : Measure E)) (U : StableJumpEnergySpace α),
      (∀ᵐ x ∂volume, 0 ≤ ν x ∧ ν x ≤ (κ : ℝ)) ∧
      Integrable (ν : E → ℝ) volume ∧ (∫ x : E, ν x) = ∫ x : E, f x ∧
      ‖ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x : E, ‖f x‖ ∧
      (∀ᵐ x ∂volume, 0 ≤ stableJumpValue α U x) ∧
      Integrable (stableJumpValue α U : E → ℝ) volume ∧
      (∀ V : StableJumpEnergySpace α, stableJumpForm α U V =
        ⟪f - ν, stableJumpValue α V⟫) ∧
      (∀ᵐ x ∂volume, stableJumpValue α U x ≠ 0 → ν x = (κ : ℝ)) ∧
      ((κ : ℝ≥0∞) * volume (stableJumpActiveSet α U) ≤ ∫⁻ x : E, ‖f x‖ₑ) ∧
      volume (stableJumpActiveSet α U) ≠ ⊤ := by
  obtain ⟨vseq, Useq, v, U, l, hdata, hvbound, hUpos, hUint, hlne, hl, hvt, hUt⟩ :=
    exists_positive_stableJumpBall_joint_energy_limit hα0 hα2 κ hκ f hfpos
  let : l.NeBot := hlne
  have hcompact : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ x : E, stableJumpValue α U x * coordinateStableGenerator α φ x) =
        ∫ x : E, (v x - f x) * φ x := by
    intro φ hφ hs
    obtain ⟨V, hV, hVs⟩ :=
      exists_stableJumpCompactC1Test hα0 hα2 (hφ.of_le (by norm_num)) hs
    have he := stableJump_test_equation_of_joint_limit vseq Useq f v U
      (fun k ↦ (hdata k).2.1) hl hvt hUt φ hφ.continuous hs V hV hVs
    rw [stableJumpForm_eq_neg_integral_coordinateStableGenerator
      hα0 hα2 U V hUint φ hφ hs hV] at he
    calc
      _ = -(∫ x : E, (f x - v x) * φ x) := by linarith
      _ = _ := by
        rw [← integral_neg]
        congr 1
        funext x
        ring
  obtain ⟨hvint, hvmass⟩ := integrable_weightedDensity_mass_eq_of_jumpPDE hα0 hα2
    (stableJumpValue α U) f hUint hf v (hvbound.mono fun _ h ↦ h.1) hcompact
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
  have hνmasscap : ν ∈ normMassCap volume κ mass := by
    constructor
    · filter_upwards [hνbound] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    · rw [← ofReal_integral_norm_eq_lintegral_enorm hνint, hnormmass]
      change ENNReal.ofReal (mass : ℝ) ≤ (mass : ℝ≥0∞)
      rw [ENNReal.ofReal_coe_nnreal]
  have heq : ∀ V : StableJumpEnergySpace α, stableJumpForm α U V =
      ⟪f - ν, stableJumpValue α V⟫ :=
    stableJump_equation_of_joint_limit hα0 hα2 vseq Useq f ν v U hνae.symm
      (fun k ↦ (hdata k).2.1) hl hvt hUt
  let L : StableJumpEnergySpace α →L[ℝ] ℝ := (innerSL ℝ f).comp (stableJumpValue α)
  have henergy : stableJumpForm α U U + (κ : ℝ) *
      (∫ x : E, ‖stableJumpValue α U x‖) ≤ ⟪f, stableJumpValue α U⟫ :=
    stableJump_energy_mass_le_of_weak_tendsto κ.coe_nonneg hUt L hUint
      (Eventually.of_forall fun k ↦
        integrable_stableJumpBall_globalValue α ((k : ℝ) + 1) (Useq k))
      (Eventually.of_forall fun k ↦ (hdata k).2.2.2.2)
  have hpair : (κ : ℝ) * (∫ x : E, ‖stableJumpValue α U x‖) ≤
      ⟪ν, stableJumpValue α U⟫ := by
    rw [heq U, inner_sub_left] at henergy
    linarith
  have hsat : ∀ᵐ x ∂volume, stableJumpValue α U x ≠ 0 → ν x = (κ : ℝ) := by
    have hs := (ae_alignment_saturation_of_pairing_ge κ.coe_nonneg ν
      (stableJumpValue α U) hνmasscap.1 hUint hpair).2
    filter_upwards [hs, hνbound] with x hx hνx
    intro hu
    have he := hx hu
    rwa [Real.norm_eq_abs, abs_of_nonneg hνx.1] at he
  have hcapmeasure := cap_measure_stableJumpActiveSet κ U ν f hνint hf hsat hnormmass.le
  exact ⟨ν, U, hνbound, hνint, hνmass, norm_sq_le_of_mem_normMassCap hνmasscap,
    hUpos, hUint, heq, hsat, hcapmeasure,
    measure_stableJumpActiveSet_ne_top hκ U f hf hcapmeasure⟩

end PartialBalayage.Maximal.Square
