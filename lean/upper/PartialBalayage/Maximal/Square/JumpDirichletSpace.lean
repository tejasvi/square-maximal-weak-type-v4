/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpEnergy
public import PartialBalayage.Linear.L2DomainRestriction
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Genuine zero-exterior states for the anisotropic stable generator

The zero-exterior condition is the kernel of an actual bounded `L²` restriction map.
Consequently it defines a complete Hilbert subspace of the full singular jump graph.
Normal contractions preserve this condition. A positive interval of long jumps gives
coercivity on every bounded ball without discarding the small jumps from the form.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual zero-exterior subspace of the genuine stable energy graph. -/
def stableJumpSupported (α : ℝ) (Ω : Set E) : Submodule ℝ (StableJumpEnergySpace α) :=
  LinearMap.ker ((PartialBalayage.Linear.restrictL2CLM Ωᶜ) ∘L stableJumpValue α).toLinearMap

theorem isClosed_stableJumpSupported (α : ℝ) (Ω : Set E) :
    IsClosed (stableJumpSupported α Ω : Set (StableJumpEnergySpace α)) :=
  ContinuousLinearMap.isClosed_ker _

/-- Genuine zero-exterior energy states, rather than an assumed Sobolev certificate. -/
abbrev StableJumpDirichletSpace (α : ℝ) (Ω : Set E) := ↥(stableJumpSupported α Ω)

instance (α : ℝ) (Ω : Set E) : CompleteSpace (StableJumpDirichletSpace α Ω) :=
  (isClosed_stableJumpSupported α Ω).completeSpace_coe

/-- The exact pointwise interpretation of the zero-exterior Hilbert subspace. -/
theorem mem_stableJumpSupported_iff (α : ℝ) {Ω : Set E} (hΩ : MeasurableSet Ω)
    (U : StableJumpEnergySpace α) :
    U ∈ stableJumpSupported α Ω ↔ ∀ᵐ x, x ∉ Ω → stableJumpValue α U x = 0 := by
  change PartialBalayage.Linear.restrictL2CLM Ωᶜ (stableJumpValue α U) = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hr := PartialBalayage.Linear.restrictL2CLM_ae Ωᶜ (stableJumpValue α U)
  constructor
  · intro h
    apply (ae_restrict_iff' hΩ.compl).mp
    exact hr.symm.trans h
  · intro h
    exact hr.trans ((ae_restrict_iff' hΩ.compl).mpr h)

/-- The actual whole-space value observation of a zero-exterior state. -/
def stableJumpDirichletGlobalValue (α : ℝ) (Ω : Set E) :
    StableJumpDirichletSpace α Ω →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  stableJumpValue α ∘L (stableJumpSupported α Ω).subtypeL

/-- The genuine value observation restricted to the finite obstacle domain. -/
def stableJumpDirichletValue (α : ℝ) (Ω : Set E) :
    StableJumpDirichletSpace α Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  PartialBalayage.Linear.restrictL2CLM Ω ∘L stableJumpDirichletGlobalValue α Ω

/-- The actual increment-data observation on the zero-exterior Hilbert subspace. -/
def stableJumpDirichletData (α : ℝ) (Ω : Set E) :
    StableJumpDirichletSpace α Ω →L[ℝ]
      PiLp 2 (fun _ : Fin 2 ↦ Lp ℝ 2 (spatialJumpMeasure α)) :=
  stableJumpData α ∘L (stableJumpSupported α Ω).subtypeL

/-- Normal contractions keep the genuine zero-exterior boundary condition. -/
theorem stableJumpNormalContraction_mem_supported (α : ℝ) {Ω : Set E}
    (hΩ : MeasurableSet Ω) (η : ℝ → ℝ) (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    {U : StableJumpEnergySpace α} (hU : U ∈ stableJumpSupported α Ω) :
    stableJumpNormalContraction α η hη hη0 U ∈ stableJumpSupported α Ω := by
  rw [mem_stableJumpSupported_iff α hΩ] at hU ⊢
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [hU, he] with x hx he
  intro hxo
  rw [stableJumpNormalContraction_value, he, Function.comp_apply, hx hxo, hη0]

/-- The actual negative-part test with its genuine zero-exterior condition. -/
def stableJumpDirichletNegativePart (α : ℝ) {Ω : Set E} (hΩ : MeasurableSet Ω)
    (U : StableJumpDirichletSpace α Ω) : StableJumpDirichletSpace α Ω :=
  ⟨stableJumpNegativePart α U.val,
    stableJumpNormalContraction_mem_supported α hΩ _ _ _ U.property⟩

/-- A closed band of long coordinate jumps. -/
def longJumpBand (R : ℝ) : Set ℝ := Icc (4 * R) (5 * R)

private theorem longJumpBand_subset_pos {R : ℝ} (hR : 0 < R) :
    longJumpBand R ⊆ Ioi 0 := by
  intro t ht
  dsimp [longJumpBand] at ht
  exact lt_of_lt_of_le (by positivity : 0 < 4 * R) ht.1

/-- The exact long-jump mass has a positive elementary lower bound. -/
theorem stableJumpMeasure_longJumpBand_lower {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) :
    ENNReal.ofReal (stableNormalization α * (5 * R) ^ (-(1 + α)) * R) ≤
      stableJumpMeasure α (longJumpBand R) := by
  have hm : MeasurableSet (longJumpBand R) := measurableSet_Icc
  rw [stableJumpMeasure, withDensity_apply _ hm,
    Measure.restrict_restrict_of_subset (longJumpBand_subset_pos hR)]
  calc
    _ = ∫⁻ _ in longJumpBand R,
        ENNReal.ofReal (stableNormalization α * (5 * R) ^ (-(1 + α))) := by
      rw [setLIntegral_const, longJumpBand, Real.volume_Icc]
      have he : 5 * R - 4 * R = R := by ring
      rw [he, ← ENNReal.ofReal_mul]
      exact le_of_lt (mul_pos (stableNormalization_pos hα0 hα2) (Real.rpow_pos_of_pos
        (by positivity) _))
    _ ≤ _ := by
      apply setLIntegral_mono' hm
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by positivity) ht.1) ht.2
          (by linarith)) (stableNormalization_pos hα0 hα2).le

/-- Long-jump bands have finite mass, despite the infinite mass at the origin. -/
theorem stableJumpMeasure_longJumpBand_ne_top {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) : stableJumpMeasure α (longJumpBand R) ≠ ⊤ := by
  have hm : MeasurableSet (longJumpBand R) := measurableSet_Icc
  rw [stableJumpMeasure, withDensity_apply _ hm,
    Measure.restrict_restrict_of_subset (longJumpBand_subset_pos hR)]
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal
    (stableNormalization α * (4 * R) ^ (-(1 + α))) * volume (longJumpBand R))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      rw [longJumpBand, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  · rw [← setLIntegral_const]
    apply setLIntegral_mono' hm
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) ht.1 (by linarith))
      (stableNormalization_pos hα0 hα2).le

theorem stableJumpMeasure_longJumpBand_toReal_pos {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) : 0 < (stableJumpMeasure α (longJumpBand R)).toReal := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((ENNReal.ofReal_pos.mpr (mul_pos
      (mul_pos (stableNormalization_pos hα0 hα2) (Real.rpow_pos_of_pos (by positivity) _))
      hR)).trans_le (stableJumpMeasure_longJumpBand_lower hα0 hα2 hR))
  · exact stableJumpMeasure_longJumpBand_ne_top hα0 hα2 hR

private theorem coordinateJumpPoint_not_mem_ball {R : ℝ} (hR : 0 < R) (i : Fin 2)
    {x : E} (hx : x ∈ closedBall 0 R) {t : ℝ} (ht : t ∈ longJumpBand R) :
    coordinateJumpPoint i (x, t) ∉ closedBall 0 R := by
  have htx : 0 < t := longJumpBand_subset_pos hR ht
  have hnormx : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have htriangle := norm_sub_le (coordinateJumpPoint i (x, t)) x
  have he : coordinateJumpPoint i (x, t) - x =
      t • EuclideanSpace.basisFun (Fin 2) ℝ i := by
    unfold coordinateJumpPoint
    simp
  rw [he, norm_smul, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one i,
    mul_one, Real.norm_of_nonneg htx.le] at htriangle
  have hlong : 4 * R ≤ t := ht.1
  have hfar : R < ‖coordinateJumpPoint i (x, t)‖ := by linarith
  simpa only [mem_closedBall_zero_iff, not_le] using hfar

/-- A positive interval of long jumps controls the actual physical `L²` value. -/
theorem stableJumpData_longJumpBand_enorm_sq_le (α : ℝ) {R : ℝ} (hR : 0 < R)
    (U : StableJumpEnergySpace α) (hU : U ∈ stableJumpSupported α (closedBall 0 R))
    (i : Fin 2) :
    ‖stableJumpValue α U‖ₑ ^ (2 : ℕ) * stableJumpMeasure α (longJumpBand R) ≤
      ‖stableJumpData α U i‖ₑ ^ (2 : ℕ) := by
  let u := stableJumpValue α U
  have hz : ∀ᵐ x, x ∉ closedBall 0 R → u x = 0 :=
    (mem_stableJumpSupported_iff α measurableSet_closedBall U).mp hU
  have hm : MeasurableSet (longJumpBand R) := measurableSet_Icc
  have hnorm : ‖u‖ₑ ^ (2 : ℕ) = ∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ) := by
    rw [Lp.enorm_def]
    simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
      (Lp.aestronglyMeasurable u)
  calc
    _ = ∫⁻ p : E × ℝ, ‖u p.1‖ₑ ^ (2 : ℕ) * (longJumpBand R).indicator 1 p.2
        ∂spatialJumpMeasure α := by
      change ‖u‖ₑ ^ (2 : ℕ) * stableJumpMeasure α (longJumpBand R) =
        ∫⁻ p : E × ℝ, ‖u p.1‖ₑ ^ (2 : ℕ) * (longJumpBand R).indicator 1 p.2
          ∂((volume : Measure E).prod (stableJumpMeasure α))
      have hf : AEMeasurable (fun x : E ↦ ‖u x‖ₑ ^ (2 : ℕ)) volume :=
        (Lp.aestronglyMeasurable u).enorm.pow_const 2
      have hg : AEMeasurable ((longJumpBand R).indicator (1 : ℝ → ℝ≥0∞))
          (stableJumpMeasure α) := (measurable_const.indicator hm).aemeasurable
      rw [lintegral_prod_mul hf hg, lintegral_indicator_one hm, ← hnorm]
    _ ≤ ∫⁻ p, ‖coordinateJump (u : E → ℝ) i p‖ₑ ^ (2 : ℕ)
        ∂spatialJumpMeasure α := by
      apply lintegral_mono_ae
      filter_upwards [(quasiMeasurePreserving_coordinateJumpPoint α i).ae hz,
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure E))
          (ν := stableJumpMeasure α)).ae hz] with p hx hy
      by_cases ht : p.2 ∈ longJumpBand R
      · rw [indicator_of_mem ht, Pi.one_apply, mul_one]
        by_cases hp : p.1 ∈ closedBall 0 R
        · have hf := coordinateJumpPoint_not_mem_ball hR i hp ht
          rw [coordinateJump, hx hf, zero_sub, enorm_neg]
        · rw [hy hp, enorm_zero, zero_pow (by decide)]
          exact bot_le
      · rw [indicator_of_notMem ht, mul_zero]
        exact bot_le
    _ = _ := (stableJumpData_enorm_sq α U i).symm

/-- The actual zero-exterior singular form controls the full physical value norm. -/
theorem stableJumpForm_ball_value_coercive {α R : ℝ} (hR : 0 < R)
    (U : StableJumpDirichletSpace α (closedBall 0 R)) :
    (stableJumpMeasure α (longJumpBand R)).toReal * ‖stableJumpValue α U.val‖ ^ 2 ≤
      stableJumpForm α U.val U.val := by
  have h := ENNReal.toReal_mono (ENNReal.pow_ne_top enorm_ne_top)
    (stableJumpData_longJumpBand_enorm_sq_le α hR U.val U.property 0)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] at h
  rw [stableJumpForm_self, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  nlinarith [sq_nonneg ‖stableJumpData α U.val 1‖]

/-- Coercivity in the complete graph norm follows from genuine long jumps. -/
theorem stableJumpForm_ball_coercive {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : StableJumpDirichletSpace α (closedBall 0 R)) :
    ((stableJumpMeasure α (longJumpBand R)).toReal /
      (1 + (stableJumpMeasure α (longJumpBand R)).toReal)) * ‖U‖ ^ 2 ≤
        stableJumpForm α U.val U.val := by
  let c := (stableJumpMeasure α (longJumpBand R)).toReal
  have hc : 0 < c := stableJumpMeasure_longJumpBand_toReal_pos hα0 hα2 hR
  have hvalue := stableJumpForm_ball_value_coercive hR U
  have hnorm := stableJumpEnergy_norm_sq α U.val
  have hself := stableJumpForm_self α U.val
  change c / (1 + c) * ‖U.val‖ ^ 2 ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + c)]
  dsimp [c] at *
  nlinarith

end PartialBalayage.Maximal.Square
