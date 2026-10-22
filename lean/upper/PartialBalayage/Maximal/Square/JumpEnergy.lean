/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual anisotropic stable jump energy

The singular positive jump measure is used without truncating its mass at zero. Its
coordinate increments define a closed subspace of a Hilbert product of genuine `L²`
spaces. Normal contractions preserve this graph. These are properties of the actual
jump form, rather than assumptions about an abstract obstacle solution.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The normalization in the symmetric stable singular-integral generator. -/
def stableNormalization (α : ℝ) : ℝ :=
  Real.Gamma (1 + α) * Real.sin (Real.pi * α / 2) / Real.pi

theorem stableNormalization_pos {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    0 < stableNormalization α := by
  unfold stableNormalization
  apply div_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith)) ?_) Real.pi_pos
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- The genuine infinite-mass positive jump measure on the positive half-line. -/
def stableJumpMeasure (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t ↦ ENNReal.ofReal (stableNormalization α * t ^ (-(1 + α))))

instance (α : ℝ) : SigmaFinite (stableJumpMeasure α) := by
  unfold stableJumpMeasure
  infer_instance

/-- The product measure for a spatial point and its positive coordinate jump. -/
def spatialJumpMeasure (α : ℝ) : Measure (E × ℝ) := volume.prod (stableJumpMeasure α)

instance (α : ℝ) : SigmaFinite (spatialJumpMeasure α) := by
  unfold spatialJumpMeasure
  infer_instance

/-- Translation along the actual `i`th Euclidean coordinate. -/
def coordinateJumpPoint (i : Fin 2) (p : E × ℝ) : E :=
  p.1 + p.2 • EuclideanSpace.basisFun (Fin 2) ℝ i

theorem quasiMeasurePreserving_coordinateJumpPoint (α : ℝ) (i : Fin 2) :
    QuasiMeasurePreserving (coordinateJumpPoint i) (spatialJumpMeasure α) volume := by
  apply QuasiMeasurePreserving.prod_of_left (by unfold coordinateJumpPoint; fun_prop)
  filter_upwards with t
  exact (measurePreserving_add_right volume
    (t • EuclideanSpace.basisFun (Fin 2) ℝ i)).quasiMeasurePreserving

/-- The unweighted increment; the entire singular weight resides in the jump measure. -/
def coordinateJump (u : E → ℝ) (i : Fin 2) (p : E × ℝ) : ℝ :=
  u (coordinateJumpPoint i p) - u p.1

local notation "L²" => Lp ℝ 2 (volume : Measure E)
local notation "J²" α => Lp ℝ 2 (spatialJumpMeasure α)
local notation "D²" α => PiLp 2 (fun _ : Fin 2 ↦ J² α)
local notation "H" α => WithLp 2 (L² × D² α)

/-- The graph of the two actual coordinate-jump increments. -/
def stableJumpGraph (α : ℝ) : Submodule ℝ (H α) where
  carrier := {U | ∀ i : Fin 2, ∀ᵐ p ∂spatialJumpMeasure α,
    U.snd i p = coordinateJump (U.fst : E → ℝ) i p}
  zero_mem' := by
    intro i
    have hz := Lp.coeFn_zero ℝ 2 (volume : Measure E)
    filter_upwards [Lp.coeFn_zero ℝ 2 (spatialJumpMeasure α),
      (quasiMeasurePreserving_coordinateJumpPoint α i).ae hz,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α)).ae hz] with p hj hx hy
    simp only [WithLp.zero_fst, WithLp.zero_snd, PiLp.zero_apply, coordinateJump,
      hj, hx, hy, Pi.zero_apply, sub_self]
  add_mem' := by
    intro U V hU hV i
    have ha := Lp.coeFn_add U.fst V.fst
    filter_upwards [hU i, hV i, Lp.coeFn_add (U.snd i) (V.snd i),
      (quasiMeasurePreserving_coordinateJumpPoint α i).ae ha,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α)).ae ha] with p hU hV hj hx hy
    simp only [WithLp.add_fst, WithLp.add_snd, PiLp.add_apply, coordinateJump]
    rw [hj, hx, hy]
    simp only [Pi.add_apply]
    rw [hU, hV]
    unfold coordinateJump
    ring
  smul_mem' := by
    intro c U hU i
    have hc := Lp.coeFn_smul c U.fst
    filter_upwards [hU i, Lp.coeFn_smul c (U.snd i),
      (quasiMeasurePreserving_coordinateJumpPoint α i).ae hc,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α)).ae hc] with p hU hj hx hy
    simp only [WithLp.smul_fst, WithLp.smul_snd, PiLp.smul_apply, coordinateJump]
    rw [hj, hx, hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hU]
    unfold coordinateJump
    ring

/-- The singular jump graph is closed, including the full small-jump region. -/
theorem isClosed_stableJumpGraph (α : ℝ) : IsClosed (stableJumpGraph α : Set (H α)) := by
  apply IsSeqClosed.isClosed
  intro U V hU hUV
  have h0 : Tendsto (fun n ↦ (U n).fst) atTop (𝓝 V.fst) :=
    (WithLp.continuous_fst 2 L² (D² α)).tendsto V |>.comp hUV
  obtain ⟨s, hs, h0s⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  change ∀ i : Fin 2, ∀ᵐ p ∂spatialJumpMeasure α,
    V.snd i p = coordinateJump (V.fst : E → ℝ) i p
  have hgraphs : ∀ n i, ∀ᵐ p ∂spatialJumpMeasure α,
      (U n).snd i p = coordinateJump ((U n).fst : E → ℝ) i p := hU
  intro i
  have hi : Tendsto (fun n ↦ (U (s n)).snd i) atTop (𝓝 (V.snd i)) :=
    ((PiLp.continuous_apply 2 _ i).comp (WithLp.continuous_snd 2 L² (D² α))).tendsto V |>.comp
      (hUV.comp hs.tendsto_atTop)
  obtain ⟨r, hr, hir⟩ := (tendstoInMeasure_of_tendsto_Lp hi).exists_seq_tendsto_ae
  filter_upwards [hir, (quasiMeasurePreserving_coordinateJumpPoint α i).ae h0s,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae h0s,
    ae_all_iff.mpr (fun n ↦ hgraphs (s (r n)) i)] with p hp hx hy hgraph
  have hj := (hx.comp hr.tendsto_atTop).sub (hy.comp hr.tendsto_atTop)
  exact tendsto_nhds_unique hp
    (hj.congr' (Eventually.of_forall fun n ↦ (hgraph n).symm))

/-- The genuine complete Hilbert energy space of the anisotropic stable generator. -/
abbrev StableJumpEnergySpace (α : ℝ) := ↥(stableJumpGraph α)

instance (α : ℝ) : CompleteSpace (StableJumpEnergySpace α) :=
  (isClosed_stableJumpGraph α).completeSpace_coe

/-- The physical-space value observation of an actual stable jump state. -/
def stableJumpValue (α : ℝ) : StableJumpEnergySpace α →L[ℝ] L² :=
  WithLp.fstL 2 ℝ L² (D² α) ∘L (stableJumpGraph α).subtypeL

/-- The two actual increment coordinates of an energy state. -/
def stableJumpData (α : ℝ) : StableJumpEnergySpace α →L[ℝ] D² α :=
  WithLp.sndL 2 ℝ L² (D² α) ∘L (stableJumpGraph α).subtypeL

/-- The actual jump increments represented by the Hilbert data. -/
theorem stableJumpData_ae (α : ℝ) (U : StableJumpEnergySpace α) (i : Fin 2) :
    (stableJumpData α U i : E × ℝ → ℝ) =ᵐ[spatialJumpMeasure α]
      coordinateJump (stableJumpValue α U : E → ℝ) i := by
  have hU : ∀ i : Fin 2, ∀ᵐ p ∂spatialJumpMeasure α,
      (U : H α).snd i p = coordinateJump ((U : H α).fst : E → ℝ) i p := U.property
  exact hU i

/-- The graph norm contains exactly the value norm and the two genuine jump energies. -/
theorem stableJumpEnergy_norm_sq (α : ℝ) (U : StableJumpEnergySpace α) :
    ‖U‖ ^ 2 = ‖stableJumpValue α U‖ ^ 2 + ‖stableJumpData α U‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (U : H α)

/-- The Dirichlet form is the inner product of the actual two jump increments. -/
def stableJumpForm (α : ℝ) (U V : StableJumpEnergySpace α) : ℝ :=
  ⟪stableJumpData α U, stableJumpData α V⟫

theorem stableJumpForm_self (α : ℝ) (U : StableJumpEnergySpace α) :
    stableJumpForm α U U = ‖stableJumpData α U‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq _

/-- The squared norm of each actual jump coordinate is its full nonnegative jump integral. -/
theorem stableJumpData_enorm_sq (α : ℝ) (U : StableJumpEnergySpace α) (i : Fin 2) :
    ‖stableJumpData α U i‖ₑ ^ (2 : ℕ) = ∫⁻ p,
      ‖coordinateJump (stableJumpValue α U : E → ℝ) i p‖ₑ ^ (2 : ℕ)
        ∂spatialJumpMeasure α := by
  rw [Lp.enorm_def]
  have he : eLpNorm (stableJumpData α U i : E × ℝ → ℝ) 2 (spatialJumpMeasure α) ^
      (2 : ℕ) = ∫⁻ p, ‖stableJumpData α U i p‖ₑ ^ (2 : ℕ)
        ∂spatialJumpMeasure α := by
    simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
      (Lp.aestronglyMeasurable (stableJumpData α U i))
  rw [he]
  exact lintegral_congr_ae ((stableJumpData_ae α U i).fun_comp (fun r ↦ ‖r‖ₑ ^ (2 : ℕ)))

/-- The genuine bilinear jump integral represented by the Hilbert form. -/
theorem stableJumpForm_eq_sum_integral (α : ℝ) (U V : StableJumpEnergySpace α) :
    stableJumpForm α U V = ∑ i : Fin 2, ∫ p,
      coordinateJump (stableJumpValue α U : E → ℝ) i p *
        coordinateJump (stableJumpValue α V : E → ℝ) i p ∂spatialJumpMeasure α := by
  rw [stableJumpForm, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stableJumpData_ae α U i, stableJumpData_ae α V i] with p hU hV
  simp only [hU, hV, Real.inner_apply]

/-- The actual contracted increments remain square integrable against the singular jump measure. -/
theorem memLp_coordinateJump_of_normalContraction (α : ℝ) (η : ℝ → ℝ)
    (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) (i : Fin 2) :
    MemLp (coordinateJump (hη.compLp hη0 (stableJumpValue α U) : E → ℝ) i) 2
      (spatialJumpMeasure α) := by
  let u := hη.compLp hη0 (stableJumpValue α U)
  have hu := Lp.aestronglyMeasurable u
  have hm : AEStronglyMeasurable (coordinateJump (u : E → ℝ) i)
      (spatialJumpMeasure α) :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_coordinateJumpPoint α i)).sub
      (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fst
        (μ := (volume : Measure E)) (ν := stableJumpMeasure α)))
  apply (Lp.memLp (stableJumpData α U i)).norm.mono' hm
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [stableJumpData_ae α U i,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae he] with p hU hx hy
  change ‖u (coordinateJumpPoint i p) - u p.1‖ ≤ ‖stableJumpData α U i p‖
  rw [hx, hy, hU]
  simpa only [Function.comp_apply, coordinateJump, NNReal.coe_one, one_mul] using
    hη.norm_sub_le (stableJumpValue α U (coordinateJumpPoint i p)) (stableJumpValue α U p.1)

/-- Every genuine normal contraction of a state remains in the full singular jump graph. -/
def stableJumpNormalContraction (α : ℝ) (η : ℝ → ℝ) (hη : LipschitzWith 1 η)
    (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) : StableJumpEnergySpace α := by
  refine ⟨WithLp.toLp 2 (hη.compLp hη0 (stableJumpValue α U),
    WithLp.toLp 2 fun i ↦
      (memLp_coordinateJump_of_normalContraction α η hη hη0 U i).toLp
        (coordinateJump (hη.compLp hη0 (stableJumpValue α U) : E → ℝ) i)), ?_⟩
  change ∀ i : Fin 2, _
  exact fun i ↦ (memLp_coordinateJump_of_normalContraction α η hη hη0 U i).coeFn_toLp

theorem stableJumpNormalContraction_value (α : ℝ) (η : ℝ → ℝ)
    (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) :
    stableJumpValue α (stableJumpNormalContraction α η hη hη0 U) =
      hη.compLp hη0 (stableJumpValue α U) := rfl

/-- The actual normal contraction reduces the genuine anisotropic Dirichlet energy. -/
theorem stableJumpNormalContraction_energy_le (α : ℝ) (η : ℝ → ℝ)
    (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) (U : StableJumpEnergySpace α) :
    stableJumpForm α (stableJumpNormalContraction α η hη hη0 U)
      (stableJumpNormalContraction α η hη hη0 U) ≤ stableJumpForm α U U := by
  rw [stableJumpForm_self, stableJumpForm_self, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  apply Lp.norm_le_norm_of_ae_le
  have he := hη.coeFn_compLp hη0 (stableJumpValue α U)
  filter_upwards [stableJumpData_ae α U i,
    stableJumpData_ae α (stableJumpNormalContraction α η hη hη0 U) i,
    (quasiMeasurePreserving_coordinateJumpPoint α i).ae he,
    (quasiMeasurePreserving_fst (μ := (volume : Measure E))
      (ν := stableJumpMeasure α)).ae he] with p hU hV hx hy
  rw [hU, hV, stableJumpNormalContraction_value]
  unfold coordinateJump
  rw [hx, hy]
  simpa only [Function.comp_apply, NNReal.coe_one, one_mul] using
    hη.norm_sub_le (stableJumpValue α U (coordinateJumpPoint i p)) (stableJumpValue α U p.1)

/-- The actual positive part of a stable energy state. -/
def stableJumpPositivePart (α : ℝ) (U : StableJumpEnergySpace α) :
    StableJumpEnergySpace α :=
  stableJumpNormalContraction α (fun r ↦ max r 0) Lp.lipschitzWith_pos_part
    (max_eq_right le_rfl) U

/-- The actual negative part of a stable energy state. -/
theorem lipschitzWith_negative_part : LipschitzWith 1 (fun r : ℝ ↦ max (-r) 0) := by
  have hn : LipschitzWith 1 (fun r : ℝ ↦ -r) :=
    LipschitzWith.of_dist_le_mul fun a b ↦ by simp
  simpa only [Function.comp_def, one_mul] using Lp.lipschitzWith_pos_part.comp hn

/-- The actual negative part of a stable energy state. -/
def stableJumpNegativePart (α : ℝ) (U : StableJumpEnergySpace α) :
    StableJumpEnergySpace α :=
  stableJumpNormalContraction α (fun r ↦ max (-r) 0)
    lipschitzWith_negative_part
    (by simp) U

private theorem negative_part_increment_inequality (a b : ℝ) :
    (a - b) * (max (-a) 0 - max (-b) 0) ≤ -(max (-a) 0 - max (-b) 0) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb)]
    nlinarith
  · rw [max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
    nlinarith
  · rw [max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb)]
    nlinarith
  · rw [max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
    simp

/-- The genuine mixed-sign inequality needed to test the stable obstacle with its negative part. -/
theorem stableJumpForm_negativePart_le (α : ℝ) (U : StableJumpEnergySpace α) :
    stableJumpForm α U (stableJumpNegativePart α U) ≤
      -stableJumpForm α (stableJumpNegativePart α U) (stableJumpNegativePart α U) := by
  rw [stableJumpForm, stableJumpForm, PiLp.inner_apply, PiLp.inner_apply,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_mono_ae
  · exact L2.integrable_inner _ _
  · exact (L2.integrable_inner _ _).neg
  · have he : (stableJumpValue α (stableJumpNegativePart α U) : E → ℝ) =ᵐ[volume]
        fun x ↦ max (-stableJumpValue α U x) 0 :=
      lipschitzWith_negative_part.coeFn_compLp (by simp) (stableJumpValue α U)
    filter_upwards [stableJumpData_ae α U i,
      stableJumpData_ae α (stableJumpNegativePart α U) i,
      (quasiMeasurePreserving_coordinateJumpPoint α i).ae he,
      (quasiMeasurePreserving_fst (μ := (volume : Measure E))
        (ν := stableJumpMeasure α)).ae he] with p hU hV hx hy
    simp only [Real.inner_apply, hU, hV, coordinateJump, hx, hy]
    convert negative_part_increment_inequality
      (stableJumpValue α U (coordinateJumpPoint i p)) (stableJumpValue α U p.1) using 1
    ring

end PartialBalayage.Maximal.Square
