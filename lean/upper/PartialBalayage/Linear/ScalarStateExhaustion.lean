/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.ScalarPositiveObstacle
public import PartialBalayage.Linear.UniformFiniteStateBounds
public import PartialBalayage.Linear.JointWeakCompactness
public import PartialBalayage.Linear.WeakDirichletEnergy
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Positivity in genuine joint scalar obstacle limits

The actual scalar `L²` positive cone is norm closed and convex, hence weakly closed.
Bounded coordinate and value maps carry genuine weak state and density convergence
to that scalar cone. Finite positive obstacles are selected from the proved positive
constructor, and genuine zero extension preserves their positivity. Joint compactness
therefore gives nonnegative state and density limits, without either limit positivity
or uniform finite-state bounds being assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

section PositiveCone

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The actual scalar `L²` positive cone is weakly closed. -/
theorem isClosed_scalarLp_positiveCone_weak :
    IsClosed {v : WeakSpace ℝ (Lp ℝ 2 μ) |
      ∀ᵐ x ∂μ, 0 ≤ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm v) x} := by
  have hc : Convex ℝ (Ici (0 : Lp ℝ 2 μ)) := by
    intro f hf g hg a b ha hb _
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg,
      Lp.coeFn_smul a f, Lp.coeFn_smul b g, Lp.coeFn_add (a • f) (b • g)]
      with x hfx hgx haf hbg hab
    rw [hab, Pi.add_apply, haf, hbg, Pi.smul_apply, Pi.smul_apply]
    exact add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hgx)
  have heq : {v : WeakSpace ℝ (Lp ℝ 2 μ) |
      ∀ᵐ x ∂μ, 0 ≤ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm v) x} =
      toWeakSpace ℝ (Lp ℝ 2 μ) '' Ici 0 := by
    rw [(toWeakSpace ℝ (Lp ℝ 2 μ)).image_eq_preimage_symm]
    ext v
    exact Lp.coeFn_nonneg _
  rw [heq]
  exact hc.isClosed_toWeakSpace_image isClosed_Ici

/-- Nonnegativity passes to actual scalar `L²` weak limits along any nontrivial filter. -/
theorem ae_nonneg_of_weak_scalarLp_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → Lp ℝ 2 μ} {vlimit : Lp ℝ 2 μ}
    (ht : Tendsto (fun k ↦ toWeakSpace ℝ _ (v k)) l (𝓝 (toWeakSpace ℝ _ vlimit)))
    (hp : ∀ᶠ k in l, ∀ᵐ x ∂μ, 0 ≤ v k x) : ∀ᵐ x ∂μ, 0 ≤ vlimit x := by
  have hm : ∀ᶠ k in l, toWeakSpace ℝ (Lp ℝ 2 μ) (v k) ∈
      {v : WeakSpace ℝ (Lp ℝ 2 μ) |
        ∀ᵐ x ∂μ, 0 ≤ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm v) x} := by
    simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hp
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    isClosed_scalarLp_positiveCone_weak.mem_of_tendsto ht hm

/-- Actual bounded value maps preserve positivity under genuine weak state convergence. -/
theorem ae_nonneg_CLM_of_weak_tendsto {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : H →L[ℝ] Lp ℝ 2 μ) {U : ι → H} {Ulimit : H}
    (ht : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (hp : ∀ᶠ k in l, ∀ᵐ x ∂μ, 0 ≤ L (U k) x) : ∀ᵐ x ∂μ, 0 ≤ L Ulimit x := by
  apply ae_nonneg_of_weak_scalarLp_tendsto _ hp
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
    ((continuous_weakMap L).tendsto (toWeakSpace ℝ H Ulimit)).comp ht

/-- The actual scalar coordinate of a one-coordinate vector density as a bounded map. -/
def scalarExhaustionCoordinateCLM :
    Lp (EuclideanSpace ℝ (Fin 1)) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0).compLpL 2 μ

theorem scalarExhaustionCoordinateCLM_ae (v : Lp (EuclideanSpace ℝ (Fin 1)) 2 μ) :
    scalarExhaustionCoordinateCLM v =ᵐ[μ] fun x ↦ v x 0 := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 ↦ ℝ) 0).coeFn_compLpL (p := 2) v

/-- Genuine vector density weak limits retain positivity of their scalar coordinate. -/
theorem ae_scalarCoordinate_nonneg_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → Lp (EuclideanSpace ℝ (Fin 1)) 2 μ}
    {vlimit : Lp (EuclideanSpace ℝ (Fin 1)) 2 μ}
    (ht : Tendsto (fun k ↦ toWeakSpace ℝ _ (v k)) l (𝓝 (toWeakSpace ℝ _ vlimit)))
    (hp : ∀ᶠ k in l, ∀ᵐ x ∂μ, 0 ≤ v k x 0) : ∀ᵐ x ∂μ, 0 ≤ vlimit x 0 := by
  have hc : ∀ᵐ x ∂μ, 0 ≤ scalarExhaustionCoordinateCLM vlimit x := by
    apply ae_nonneg_CLM_of_weak_tendsto scalarExhaustionCoordinateCLM ht
    filter_upwards [hp] with k hk
    filter_upwards [hk, scalarExhaustionCoordinateCLM_ae (v k)] with x hx hcoord
    rwa [hcoord]
  filter_upwards [hc, scalarExhaustionCoordinateCLM_ae vlimit] with x hx hcoord
  rwa [hcoord] at hx

/-- Actual measurable-domain zero extension preserves positivity of the scalar density. -/
theorem ae_scalarCoordinate_nonneg_zeroExtendL2 {Ω : Set X} (hΩ : MeasurableSet Ω)
    (v : Lp (EuclideanSpace ℝ (Fin 1)) 2 (μ.restrict Ω))
    (hp : ∀ᵐ x ∂(μ.restrict Ω), 0 ≤ v x 0) :
    ∀ᵐ x ∂μ, 0 ≤ zeroExtendL2 hΩ v x 0 := by
  have hlocal : ∀ᵐ x ∂μ, x ∈ Ω → 0 ≤ v x 0 := (ae_restrict_iff' hΩ).mp hp
  filter_upwards [zeroExtendL2_ae hΩ v, hlocal] with x hx hp
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · simpa only [indicator_of_mem hxΩ] using hp hxΩ
  · simp only [indicator_of_notMem hxΩ, PiLp.zero_apply, le_refl]

end PositiveCone

section StateValues

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "ScalarState" => VectorDirichletState (univ : Set X) 1

/-- The genuine global scalar state value, as a bounded map into actual whole-space `L²`. -/
def scalarExhaustionStateValueCLM : ScalarState →L[ℝ] Lp ℝ 2 (volume : Measure X) :=
  scalarExhaustionCoordinateCLM ∘L globalVectorDirichletObservation

theorem scalarExhaustionStateValueCLM_ae (U : ScalarState) :
    scalarExhaustionStateValueCLM U =ᵐ[volume]
      fun x ↦ vectorDirichletObservation univ U x 0 := by
  filter_upwards [scalarExhaustionCoordinateCLM_ae (globalVectorDirichletObservation U),
    globalVectorDirichletObservation_ae U] with x hx hu
  exact hx.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hu)

/-- Genuine zero extension preserves positivity of the actual scalar Sobolev state value. -/
theorem ae_scalarStateValue_nonneg_zeroExtend {Ω : Set X} (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω 1)
    (hp : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ vectorDirichletObservation Ω U x 0) :
    ∀ᵐ x, 0 ≤ scalarExhaustionStateValueCLM (zeroExtendVectorDirichletState hΩ U) x := by
  have hpval : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ (U 0).val 0 x := by
    filter_upwards [hp, vectorDirichletObservation_ae Ω U] with x hx hu
    simpa only [hu, PiLp.toLp_apply] using hx
  have hlocal : ∀ᵐ x, x ∈ Ω → 0 ≤ (U 0).val 0 x := (ae_restrict_iff' hΩ).mp hpval
  have hglobal := vectorDirichletObservation_ae univ (zeroExtendVectorDirichletState hΩ U)
  have hext := zeroExtendUnivL2CLM_ae hΩ ((U 0).val 0)
  simp only [Measure.restrict_univ] at hglobal hext
  filter_upwards [scalarExhaustionStateValueCLM_ae (zeroExtendVectorDirichletState hΩ U),
    hglobal, hext, hlocal] with x hx hu he hp
  have hu0 : vectorDirichletObservation univ (zeroExtendVectorDirichletState hΩ U) x 0 =
      zeroExtendUnivL2CLM hΩ ((U 0).val 0) x := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hu
    change vectorDirichletObservation univ (zeroExtendVectorDirichletState hΩ U) x 0 =
      (zeroExtendVectorDirichletState hΩ U 0).val 0 x at h
    rw [zeroExtendVectorDirichletState_apply] at h
    change vectorDirichletObservation univ (zeroExtendVectorDirichletState hΩ U) x 0 =
      zeroExtendH1amb hΩ (U 0).val 0 x at h
    rw [zeroExtendH1amb_apply] at h
    exact h
  rw [hx, hu0, he]
  by_cases hxΩ : x ∈ Ω
  · simpa only [indicator_of_mem hxΩ] using hp hxΩ
  · simp only [indicator_of_notMem hxΩ, le_refl]

/-- Positivity of actual scalar state values survives genuine global weak convergence. -/
theorem ae_scalarStateValue_nonneg_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → ScalarState} {Ulimit : ScalarState}
    (ht : Tendsto (fun k ↦ toWeakSpace ℝ ScalarState (U k)) l
      (𝓝 (toWeakSpace ℝ ScalarState Ulimit)))
    (hp : ∀ᶠ k in l, ∀ᵐ x, 0 ≤ scalarExhaustionStateValueCLM (U k) x) :
    ∀ᵐ x, 0 ≤ vectorDirichletObservation univ Ulimit x 0 := by
  let : NormedSpace ℝ ScalarState :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin 1 ↦ H01 (univ : Set X))
  let L : ScalarState →L[ℝ] Lp ℝ 2 (volume : Measure X) :=
    scalarExhaustionStateValueCLM (d := d)
  have h : ∀ᵐ x ∂(volume : Measure X), 0 ≤ L Ulimit x :=
    ae_nonneg_CLM_of_weak_tendsto (H := ScalarState) (μ := (volume : Measure X))
      L ht hp
  filter_upwards [h, scalarExhaustionStateValueCLM_ae Ulimit] with x hx hval
  rwa [hval] at hx

end StateValues

section PositiveSelection

variable {n : ℕ}

/-- The true finite positive scalar obstacle has capped finite-mass zero extension. -/
theorem exists_scalarPositiveBalayage_zeroExtended
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (f : Lp (EuclideanSpace ℝ (Fin 1)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin 1)) volume)
    (hfpos : ∀ᵐ x, 0 ≤ f x 0) (κ mass : ℝ≥0)
    (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν : VectorDirichletL2 Ω 1) (U : VectorDirichletState Ω 1),
      ν ∈ normCap (volume.restrict Ω) (κ : ℝ) ∧
      (∀ j : Fin 1, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) -
          vectorDirichletCoordinate Ω j ν, W.val 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = ((κ : ℝ) / ‖vectorDirichletObservation Ω U x‖) •
          vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ‖ν x‖ = (κ : ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x = 0 →
        ν x = restrictL2CLM Ω f x) ∧
      zeroExtendL2 hΩ.measurableSet ν ∈ normMassCap volume κ mass ∧
      ‖zeroExtendL2 hΩ.measurableSet ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x, ‖f x‖ ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ vectorDirichletObservation Ω U x 0) ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ν x 0) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr (hΩb.measure_lt_top (μ := volume)).ne
  have hfrestrict : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ restrictL2CLM Ω f x 0 := by
    filter_upwards [ae_restrict_of_ae hfpos, restrictL2CLM_ae Ω f] with x hx hr
    rwa [hr]
  obtain ⟨ν, U, hν, hpde, halign, hsat, hlocal, hνmass, hνenergy, hUpos, hνpos⟩ :=
    exists_scalarPositiveBalayage_finite_mass hΩ hΩb (restrictL2CLM Ω f)
      κ.coe_nonneg hfrestrict
  have hinmass := integral_norm_restrictL2CLM_le Ω f hf
  have hνint : Integrable (ν : _ → EuclideanSpace ℝ (Fin 1)) (volume.restrict Ω) :=
    (Lp.memLp ν).integrable one_le_two
  have hextint := integrable_zeroExtendL2 hΩ.measurableSet ν hνint
  have hextmass : ∫⁻ x, ‖zeroExtendL2 hΩ.measurableSet ν x‖ₑ ≤ (mass : ℝ≥0∞) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hextint, integral_norm_zeroExtendL2]
    calc
      ENNReal.ofReal (∫ x, ‖ν x‖ ∂(volume.restrict Ω)) ≤
          ENNReal.ofReal (mass : ℝ) :=
        ENNReal.ofReal_le_ofReal (hνmass.trans (hinmass.trans hmass))
      _ = _ := ENNReal.ofReal_coe_nnreal
  refine ⟨ν, U, hν, hpde, halign, hsat, hlocal,
    ⟨mem_normCap_zeroExtendL2 hΩ.measurableSet κ.coe_nonneg hν, hextmass⟩,
      ?_, hUpos, hνpos⟩
  rw [norm_zeroExtendL2]
  exact hνenergy.trans (mul_le_mul_of_nonneg_left hinmass κ.coe_nonneg)

set_option maxHeartbeats 800000 in
/-- Genuine finite positive obstacles admit joint cofinal weak state and density limits.
Both limit positivities follow from the actual finite constructor and weakly closed cones. -/
theorem exists_scalarPositiveFiniteObstacle_joint_weak_limit
    (Ω : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hΩ : ∀ k, IsOpen (Ω k)) (hΩb : ∀ k, Bornology.IsBounded (Ω k))
    (f : Lp (EuclideanSpace ℝ (Fin 1)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin 1)) volume)
    (hfpos : ∀ᵐ x, 0 ≤ f x 0) (κ mass : ℝ≥0)
    (hκ : 0 < κ) (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν : ∀ k, VectorDirichletL2 (Ω k) 1) (U : ∀ k, VectorDirichletState (Ω k) 1)
      (νlimit : Lp (EuclideanSpace ℝ (Fin 1)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
      (Ulimit : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) 1)
      (l : Filter ℕ),
      (∀ k, ν k ∈ normCap (volume.restrict (Ω k)) (κ : ℝ) ∧
        (∀ j : Fin 1, ∀ W : H01 (Ω k), laplaceBilin (Ω k) (U k j) W =
          ⟪vectorDirichletCoordinate (Ω k) j (restrictL2CLM (Ω k) f) -
            vectorDirichletCoordinate (Ω k) j (ν k), W.val 0⟫) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ν k x = ((κ : ℝ) / ‖vectorDirichletObservation (Ω k) (U k) x‖) •
            vectorDirichletObservation (Ω k) (U k) x) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ‖ν k x‖ = (κ : ℝ)) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x = 0 →
          ν k x = restrictL2CLM (Ω k) f x)) ∧
      (∀ k, ∀ᵐ x ∂(volume.restrict (Ω k)),
        0 ≤ vectorDirichletObservation (Ω k) (U k) x 0) ∧
      (∀ k, ∀ᵐ x ∂(volume.restrict (Ω k)), 0 ≤ ν k x 0) ∧
      (∀ k, zeroExtendL2 (hΩ k).measurableSet (ν k) ∈ normMassCap volume κ mass) ∧
      (∀ k, ‖zeroExtendL2 (hΩ k).measurableSet (ν k)‖ ^ (2 : ℕ) ≤
        (κ : ℝ) * ∫ x, ‖f x‖) ∧
      νlimit ∈ normMassCap volume κ mass ∧
      (∀ᵐ x, 0 ≤ νlimit x 0) ∧
      (∀ᵐ x, 0 ≤ vectorDirichletObservation univ Ulimit x 0) ∧
      l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendL2 (hΩ k).measurableSet (ν k))) l
        (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _
        (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k))) l
          (𝓝 (toWeakSpace ℝ _ Ulimit)) := by
  have hdata (k : ℕ) :=
    exists_scalarPositiveBalayage_zeroExtended (hΩ k) (hΩb k) f hf hfpos κ mass hmass
  choose ν U hcap hpde halign hsat hlocal hmasscap henergy hUpos hνpos using hdata
  have hn : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by simp
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  obtain ⟨B, _, hB⟩ := exists_uniform_vectorDirichlet_state_bound (m := 1)
    hn hκreal (norm_nonneg f)
  have hU : ∀ k, ‖U k‖ ≤ B := by
    intro k
    exact hB (Ω k) (hΩ k).measurableSet ((hΩb k).measure_lt_top (μ := volume)).ne
      (U k) (restrictL2CLM (Ω k) f) (ν k) (norm_restrictL2CLM_le (Ω k) f)
        (hpde k) (halign k)
  obtain ⟨νlimit, Ulimit, l, hνlimit, _, hlne, hl, hνt, hUt⟩ :=
    exists_joint_weak_filter_zeroExtended_finite Ω (fun k ↦ (hΩ k).measurableSet)
      ν U κ mass B hmasscap hU
  have : l.NeBot := hlne
  have hνlimitpos : ∀ᵐ x, 0 ≤ νlimit x 0 := by
    apply ae_scalarCoordinate_nonneg_of_weak_tendsto hνt
    exact Eventually.of_forall fun k ↦
      ae_scalarCoordinate_nonneg_zeroExtendL2 (hΩ k).measurableSet (ν k) (hνpos k)
  have hUlimitpos : ∀ᵐ x, 0 ≤ vectorDirichletObservation univ Ulimit x 0 := by
    apply ae_scalarStateValue_nonneg_of_weak_tendsto hUt
    exact Eventually.of_forall fun k ↦
      ae_scalarStateValue_nonneg_zeroExtend (hΩ k).measurableSet (U k) (hUpos k)
  exact ⟨ν, U, νlimit, Ulimit, l,
    (fun k ↦ ⟨hcap k, hpde k, halign k, hsat k, hlocal k⟩), hUpos, hνpos,
    hmasscap, henergy, hνlimit, hνlimitpos, hUlimitpos, hlne, hl, hνt, hUt⟩

end PositiveSelection

end PartialBalayage.Linear
