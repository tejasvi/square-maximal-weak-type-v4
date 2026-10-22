/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorInactiveLocality
public import PartialBalayage.Linear.L2DomainRestriction
public import PartialBalayage.Linear.ZeroExtensionMass
public import PartialBalayage.Linear.WholeSpaceMassCompactness

/-!
# Actual whole-space density bounds from finite-domain obstacles

The genuine domain restriction of an integrable `L²` input admits a vector obstacle on each
bounded open domain. Its actual zero extension retains the cap, mass contraction, and cap-energy
bound, hence lies in the previously proved weakly compact whole-space density set. The density
compactness statement does not claim convergence of the obstacle states or a limit PDE.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

section ExtensionCap

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable {μ : Measure X} {Ω : Set X}

/-- Actual measurable-set zero extension preserves a nonnegative pointwise norm cap. -/
theorem mem_normCap_zeroExtendL2 (hΩ : MeasurableSet Ω) {κ : ℝ} (hκ : 0 ≤ κ)
    {ν : Lp E 2 (μ.restrict Ω)} (hν : ν ∈ normCap (μ.restrict Ω) κ) :
    zeroExtendL2 hΩ ν ∈ normCap μ κ := by
  have hc : ∀ᵐ x ∂μ, x ∈ Ω → ‖ν x‖ ≤ κ := (ae_restrict_iff' hΩ).mp hν
  filter_upwards [zeroExtendL2_ae hΩ ν, hc] with x hx hcap
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · simpa only [Set.indicator_of_mem hxΩ] using hcap hxΩ
  · simpa only [Set.indicator_of_notMem hxΩ, norm_zero] using hκ

end ExtensionCap

variable {n m : ℕ}

/-- A genuine finite-domain vector density, extended to the whole space, lies in the actual
weakly compact cap-and-mass set and retains the sharp cap-energy bound. -/
theorem exists_vectorBalayage_zeroExtended
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin m)) volume)
    (κ mass : ℝ≥0) (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν : VectorDirichletL2 Ω m) (U : VectorDirichletState Ω m),
      ν ∈ normCap (volume.restrict Ω) (κ : ℝ) ∧
      (∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
        ⟪vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) -
          vectorDirichletCoordinate Ω j ν, W.val 0⟫) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 →
        ν x = ((κ : ℝ) / ‖vectorDirichletObservation Ω U x‖) • vectorDirichletObservation Ω U x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x ≠ 0 → ‖ν x‖ = (κ : ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict Ω), vectorDirichletObservation Ω U x = 0 →
        ν x = restrictL2CLM Ω f x) ∧
      zeroExtendL2 hΩ.measurableSet ν ∈ normMassCap volume κ mass ∧
      ‖zeroExtendL2 hΩ.measurableSet ν‖ ^ (2 : ℕ) ≤ (κ : ℝ) * ∫ x, ‖f x‖ := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr (hΩb.measure_lt_top (μ := volume)).ne
  obtain ⟨ν, U, hν, hpde, halign, hsat, hlocal, hνmass, hνenergy⟩ :=
    exists_vectorBalayage_finite_mass hΩ hΩb (restrictL2CLM Ω f) κ.coe_nonneg
  have hinmass := integral_norm_restrictL2CLM_le Ω f hf
  have hνint : Integrable (ν : _ → EuclideanSpace ℝ (Fin m)) (volume.restrict Ω) :=
    (Lp.memLp ν).integrable one_le_two
  have hextint := integrable_zeroExtendL2 hΩ.measurableSet ν hνint
  have hextmass : ∫⁻ x, ‖zeroExtendL2 hΩ.measurableSet ν x‖ₑ ≤ (mass : ℝ≥0∞) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hextint, integral_norm_zeroExtendL2]
    calc
      ENNReal.ofReal (∫ x, ‖ν x‖ ∂(volume.restrict Ω)) ≤
          ENNReal.ofReal (mass : ℝ) := ENNReal.ofReal_le_ofReal (hνmass.trans (hinmass.trans hmass))
      _ = _ := ENNReal.ofReal_coe_nnreal
  refine ⟨ν, U, hν, hpde, halign, hsat, hlocal,
    ⟨mem_normCap_zeroExtendL2 hΩ.measurableSet κ.coe_nonneg hν, hextmass⟩, ?_⟩
  rw [norm_zeroExtendL2]
  exact hνenergy.trans (mul_le_mul_of_nonneg_left hinmass κ.coe_nonneg)

/-- Any sequence of actual cap-and-mass densities has a weak cluster point retaining both
constraints. This uses compactness directly and does not assert a countable weak basis. -/
theorem exists_weak_cluster_density_of_normMassCap
    (κ mass : ℝ≥0)
    (ν : ℕ → Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hν : ∀ k, ν k ∈ normMassCap volume κ mass) :
    ∃ limit ∈ normMassCap volume κ mass,
      MapClusterPt (toWeakSpace ℝ _ limit) atTop (fun k ↦ toWeakSpace ℝ _ (ν k)) := by
  have hc := isCompact_toWeakSpace_image_normMassCap
    (E := EuclideanSpace ℝ (Fin m)) (μ := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    κ mass
  have hmem : ∀ᶠ k in atTop, toWeakSpace ℝ _ (ν k) ∈
      toWeakSpace ℝ _ '' normMassCap volume κ mass :=
    Eventually.of_forall fun k ↦ ⟨ν k, hν k, rfl⟩
  obtain ⟨_, ⟨limit, hlimit, rfl⟩, hcluster⟩ := hc.exists_mapClusterPt_of_frequently hmem.frequently
  exact ⟨limit, hlimit, hcluster⟩

/-- Actual finite-domain obstacle densities for a sequence of bounded open domains admit a
whole-space weak cluster point with the same cap and full mass bound. The domains may later
be chosen as an exhaustion; this theorem needs no asserted limiting PDE or state convergence. -/
theorem exists_finiteObstacle_density_weak_cluster
    (Ω : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hΩ : ∀ k, IsOpen (Ω k)) (hΩb : ∀ k, Bornology.IsBounded (Ω k))
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin m)) volume)
    (κ mass : ℝ≥0) (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν : ∀ k, VectorDirichletL2 (Ω k) m) (U : ∀ k, VectorDirichletState (Ω k) m),
      (∀ k, ν k ∈ normCap (volume.restrict (Ω k)) (κ : ℝ) ∧
        (∀ j : Fin m, ∀ W : H01 (Ω k), laplaceBilin (Ω k) (U k j) W =
          ⟪vectorDirichletCoordinate (Ω k) j (restrictL2CLM (Ω k) f) -
            vectorDirichletCoordinate (Ω k) j (ν k), W.val 0⟫) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ν k x = ((κ : ℝ) / ‖vectorDirichletObservation (Ω k) (U k) x‖) •
            vectorDirichletObservation (Ω k) (U k) x) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ‖ν k x‖ = (κ : ℝ)) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x = 0 →
          ν k x = restrictL2CLM (Ω k) f x)) ∧
      (∀ k, zeroExtendL2 (hΩ k).measurableSet (ν k) ∈ normMassCap volume κ mass) ∧
      (∀ k, ‖zeroExtendL2 (hΩ k).measurableSet (ν k)‖ ^ (2 : ℕ) ≤
        (κ : ℝ) * ∫ x, ‖f x‖) ∧
      ∃ limit ∈ normMassCap volume κ mass,
        MapClusterPt (toWeakSpace ℝ _ limit) atTop
          (fun k ↦ toWeakSpace ℝ _ (zeroExtendL2 (hΩ k).measurableSet (ν k))) := by
  have hdata (k : ℕ) := exists_vectorBalayage_zeroExtended (hΩ k) (hΩb k) f hf κ mass hmass
  choose ν U hcap hpde halign hsat hlocal hmasscap henergy using hdata
  refine ⟨ν, U, (fun k ↦ ⟨hcap k, hpde k, halign k, hsat k, hlocal k⟩),
    hmasscap, henergy, ?_⟩
  exact exists_weak_cluster_density_of_normMassCap κ mass
    (fun k ↦ zeroExtendL2 (hΩ k).measurableSet (ν k)) hmasscap

end PartialBalayage.Linear
