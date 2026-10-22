/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FiniteDensityExhaustion
public import PartialBalayage.Linear.VectorSobolevExtension
public import Mathlib.Topology.Ultrafilter

/-!
# Joint weak compactness and genuine cofinal limits

A capped finite-mass density sequence and a norm-bounded sequence in an actual Hilbert state
space admit a simultaneous weak limit along one ultrafilter below `atTop`. Compactness of the
product supplies the joint cluster point, so no first-countability or sequential compactness
of the weak topology is used. Weakly continuous test pairings pass actual eventual equations
to the joint limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace PartialBalayage.Linear

variable {X E H : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {μ : Measure X} [SigmaFinite μ]

/-- Actual jointly bounded state and capped-density sequences have a genuine joint weak
cluster point retaining the density cap, full mass, and state norm bound. -/
theorem exists_joint_weak_cluster_normMassCap
    (κ mass : ℝ≥0) (R : ℝ) (ν : ℕ → Lp E 2 μ) (U : ℕ → H)
    (hν : ∀ k, ν k ∈ normMassCap μ κ mass) (hU : ∀ k, ‖U k‖ ≤ R) :
    ∃ (νlimit : Lp E 2 μ) (Ulimit : H),
      νlimit ∈ normMassCap μ κ mass ∧ ‖Ulimit‖ ≤ R ∧
      MapClusterPt (toWeakSpace ℝ _ νlimit, toWeakSpace ℝ H Ulimit) atTop
        (fun k ↦ (toWeakSpace ℝ _ (ν k), toWeakSpace ℝ H (U k))) := by
  have hc := (isCompact_toWeakSpace_image_normMassCap (E := E) (μ := μ) κ mass).prod
    (isCompact_toWeakSpace_image_closedBall (0 : H) R)
  have hm : ∀ᶠ k in atTop, (toWeakSpace ℝ _ (ν k), toWeakSpace ℝ H (U k)) ∈
      (toWeakSpace ℝ _ '' normMassCap μ κ mass) ×ˢ
        (toWeakSpace ℝ H '' closedBall (0 : H) R) := by
    apply Eventually.of_forall
    intro k
    refine ⟨⟨ν k, hν k, rfl⟩, ⟨U k, ?_, rfl⟩⟩
    simpa only [mem_closedBall, dist_zero_right] using hU k
  obtain ⟨⟨_, _⟩, ⟨⟨νlimit, hνlimit, rfl⟩, ⟨Ulimit, hUlimit, rfl⟩⟩, hcluster⟩ :=
    hc.exists_mapClusterPt_of_frequently hm.frequently
  exact ⟨νlimit, Ulimit, hνlimit,
    by simpa only [mem_closedBall, dist_zero_right] using hUlimit, hcluster⟩

/-- One genuine cofinal ultrafilter realizes both weak limits simultaneously. -/
theorem exists_joint_weak_ultrafilter_normMassCap
    (κ mass : ℝ≥0) (R : ℝ) (ν : ℕ → Lp E 2 μ) (U : ℕ → H)
    (hν : ∀ k, ν k ∈ normMassCap μ κ mass) (hU : ∀ k, ‖U k‖ ≤ R) :
    ∃ (νlimit : Lp E 2 μ) (Ulimit : H) (l : Ultrafilter ℕ),
      νlimit ∈ normMassCap μ κ mass ∧ ‖Ulimit‖ ≤ R ∧ (l : Filter ℕ) ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)) := by
  obtain ⟨νlimit, Ulimit, hνlimit, hUlimit, hcluster⟩ :=
    exists_joint_weak_cluster_normMassCap κ mass R ν U hν hU
  obtain ⟨l, hl, ht⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)) := by
    exact (continuous_fst.tendsto _).comp ht
  have hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)) := by
    exact (continuous_snd.tendsto _).comp ht
  exact ⟨νlimit, Ulimit, l, hνlimit, hUlimit, hl, hνt, hUt⟩

/-- The same convergence can be exposed as an ordinary nontrivial filter refining `atTop`. -/
theorem exists_joint_weak_filter_normMassCap
    (κ mass : ℝ≥0) (R : ℝ) (ν : ℕ → Lp E 2 μ) (U : ℕ → H)
    (hν : ∀ k, ν k ∈ normMassCap μ κ mass) (hU : ∀ k, ‖U k‖ ≤ R) :
    ∃ (νlimit : Lp E 2 μ) (Ulimit : H) (l : Filter ℕ),
      νlimit ∈ normMassCap μ κ mass ∧ ‖Ulimit‖ ≤ R ∧ l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)) := by
  obtain ⟨νlimit, Ulimit, l, hνlimit, hUlimit, hl, hνt, hUt⟩ :=
    exists_joint_weak_ultrafilter_normMassCap κ mass R ν U hν hU
  exact ⟨νlimit, Ulimit, l, hνlimit, hUlimit, inferInstance, hl, hνt, hUt⟩

omit [CompleteSpace E] [CompleteSpace H] [SigmaFinite μ] in
/-- A fixed genuine weak test pairing passes an eventual approximate equation to the joint
limit along any nontrivial filter below `atTop`. -/
theorem weak_linear_equation_of_joint_tendsto
    {ν : ℕ → Lp E 2 μ} {U : ℕ → H} {νlimit : Lp E 2 μ} {Ulimit : H}
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (ℓν : Lp E 2 μ →L[ℝ] ℝ) (ℓU : H →L[ℝ] ℝ) (b : ℝ)
    (heq : ∀ᶠ k in atTop, ℓU (U k) = b - ℓν (ν k)) :
    ℓU Ulimit = b - ℓν νlimit := by
  have hνeval : Tendsto (fun k ↦ ℓν (ν k)) l (𝓝 (ℓν νlimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (ℓν.continuous_comp_toWeakSpace_symm.tendsto (toWeakSpace ℝ _ νlimit)).comp hνt
  have hUeval : Tendsto (fun k ↦ ℓU (U k)) l (𝓝 (ℓU Ulimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (ℓU.continuous_comp_toWeakSpace_symm.tendsto (toWeakSpace ℝ H Ulimit)).comp hUt
  exact tendsto_nhds_unique_of_eventuallyEq hUeval (tendsto_const_nhds.sub hνeval)
    (heq.filter_mono hl)

omit [CompleteSpace E] [CompleteSpace H] [SigmaFinite μ] in
/-- Fixed compact tests with eventually contained supports inherit the actual joint-limit
equation. The containment assumption concerns the approximating domains, not the limit PDE. -/
theorem weak_test_equation_of_eventual_domain_containment {Γ : Type*}
    (Ω : ℕ → Set X) (support : Γ → Set X)
    {ν : ℕ → Lp E 2 μ} {U : ℕ → H} {νlimit : Lp E 2 μ} {Ulimit : H}
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (ν k)) l (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ H (U k)) l (𝓝 (toWeakSpace ℝ H Ulimit)))
    (ℓν : Γ → Lp E 2 μ →L[ℝ] ℝ) (ℓU : Γ → H →L[ℝ] ℝ) (b : Γ → ℝ)
    (hcontained : ∀ ψ, ∀ᶠ k in atTop, support ψ ⊆ Ω k)
    (hpde : ∀ ψ k, support ψ ⊆ Ω k → ℓU ψ (U k) = b ψ - ℓν ψ (ν k)) :
    ∀ ψ, ℓU ψ Ulimit = b ψ - ℓν ψ νlimit := by
  intro ψ
  apply weak_linear_equation_of_joint_tendsto hl hνt hUt (ℓν ψ) (ℓU ψ) (b ψ)
  exact (hcontained ψ).mono (fun k hk ↦ hpde ψ k hk)

/-- Genuine finite-domain states and densities, zero extended by the actual isometries,
admit a joint cofinal weak limit once the finite state norms are uniformly bounded. -/
theorem exists_joint_weak_filter_zeroExtended_finite
    {d m : ℕ} (Ω : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (hΩ : ∀ k, MeasurableSet (Ω k))
    (ν : ∀ k, VectorDirichletL2 (Ω k) m) (U : ∀ k, VectorDirichletState (Ω k) m)
    (κ mass : ℝ≥0) (R : ℝ)
    (hν : ∀ k, zeroExtendL2 (hΩ k) (ν k) ∈ normMassCap volume κ mass)
    (hU : ∀ k, ‖U k‖ ≤ R) :
    ∃ (νlimit : Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (Ulimit : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
      (l : Filter ℕ),
      νlimit ∈ normMassCap volume κ mass ∧ ‖Ulimit‖ ≤ R ∧ l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendL2 (hΩ k) (ν k))) l
        (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendVectorDirichletState (hΩ k) (U k))) l
        (𝓝 (toWeakSpace ℝ _ Ulimit)) := by
  apply exists_joint_weak_filter_normMassCap κ mass R
    (fun k ↦ zeroExtendL2 (hΩ k) (ν k))
    (fun k ↦ zeroExtendVectorDirichletState (hΩ k) (U k)) hν
  intro k
  simpa only [norm_zeroExtendVectorDirichletState] using hU k

end PartialBalayage.Linear
