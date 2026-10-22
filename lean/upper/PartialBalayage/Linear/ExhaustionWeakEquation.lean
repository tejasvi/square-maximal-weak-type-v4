/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.JointWeakCompactness
public import PartialBalayage.Linear.ZeroExtensionWeakEquation

/-!
# Genuine fixed-test equations under domain exhaustion

Actual coordinate restriction and zero extension commute. Consequently finite-domain weak
equations, tested where their smooth compact supports lie inside the domain, become actual
whole-space bounded linear pairings. Simultaneous cofinal weak convergence passes these fixed
pairings to the limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter ContinuousLinearMap
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace Topology

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The actual scalar coordinate of a whole-space Euclidean-valued `L²` input, transported
to the existing `L2D univ` convention. -/
def univVectorCoordinateCLM (j : Fin m) :
    Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      L2D (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  vectorDirichletCoordinate univ j ∘L restrictL2CLM univ

theorem univVectorCoordinateCLM_ae (j : Fin m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    univVectorCoordinateCLM j f =ᵐ[volume] fun x ↦ f x j := by
  have hcoord := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL
    (p := 2) (restrictL2CLM univ f)
  have hrestrict := restrictL2CLM_ae univ f
  simp only [Measure.restrict_univ] at hcoord hrestrict
  filter_upwards [hcoord, hrestrict] with x hc hr
  exact hc.trans (congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) hr)

/-- Actual Euclidean coordinates commute with zero extension to the whole-space convention. -/
theorem coordinate_zeroExtendL2 (hΩ : MeasurableSet Ω) (j : Fin m)
    (ν : VectorDirichletL2 Ω m) :
    univVectorCoordinateCLM j (zeroExtendL2 hΩ ν) =
      zeroExtendUnivL2CLM hΩ (vectorDirichletCoordinate Ω j ν) := by
  have hcoord := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL (p := 2) ν
  have hcoord' : ∀ᵐ x ∂volume, x ∈ Ω → vectorDirichletCoordinate Ω j ν x = ν x j :=
    (ae_restrict_iff' hΩ).mp hcoord
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have hscalar : zeroExtendUnivL2CLM hΩ (vectorDirichletCoordinate Ω j ν) =ᵐ[volume]
      Ω.indicator (vectorDirichletCoordinate Ω j ν : _ → ℝ) := by
    simpa only [Measure.restrict_univ] using
      zeroExtendUnivL2CLM_ae hΩ (vectorDirichletCoordinate Ω j ν)
  filter_upwards [univVectorCoordinateCLM_ae j (zeroExtendL2 hΩ ν),
    zeroExtendL2_ae hΩ ν, hscalar, hcoord'] with x hc hext hsc hlocal
  rw [hc, hext, hsc]
  by_cases hx : x ∈ Ω
  · simp only [Set.indicator_of_mem hx]
    exact (hlocal hx).symm
  · simp only [Set.indicator_of_notMem hx, PiLp.zero_apply]

/-- Actual scalar coordinate restriction agrees with the coordinate of the original input. -/
theorem coordinate_restrictL2CLM_ae (j : Fin m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) =ᵐ[volume.restrict Ω] fun x ↦ f x j := by
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) j).coeFn_compLpL
    (p := 2) (restrictL2CLM Ω f), restrictL2CLM_ae Ω f] with x hc hr
  exact hc.trans (congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v j) hr)

/-- On an interior compact test, the actually restricted source has its original global pairing. -/
theorem inner_zeroExtended_restricted_coordinate_test (hΩ : MeasurableSet Ω) (j : Fin m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Ω φ) :
    ⟪zeroExtendUnivL2CLM hΩ (vectorDirichletCoordinate Ω j (restrictL2CLM Ω f)),
      (hφ.mono (subset_univ Ω)).testCls⟫ =
      ⟪univVectorCoordinateCLM j f, (hφ.mono (subset_univ Ω)).testCls⟫ := by
  rw [L2.inner_def, L2.inner_def]
  simp only [Measure.restrict_univ]
  have hsource : ∀ᵐ x ∂volume, x ∈ Ω →
      vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) x = f x j :=
    (ae_restrict_iff' hΩ).mp (coordinate_restrictL2CLM_ae j f)
  have hext : zeroExtendUnivL2CLM hΩ (vectorDirichletCoordinate Ω j (restrictL2CLM Ω f))
      =ᵐ[volume] Ω.indicator (vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) : _ → ℝ) := by
    simpa only [Measure.restrict_univ] using
      zeroExtendUnivL2CLM_ae hΩ (vectorDirichletCoordinate Ω j (restrictL2CLM Ω f))
  have htest : (hφ.mono (subset_univ Ω)).testCls =ᵐ[volume] φ := by
    simpa only [Measure.restrict_univ, IsTestFn.testCls] using
      (hφ.mono (subset_univ Ω)).mem_lp.coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hsource, hext, htest, univVectorCoordinateCLM_ae j f] with x hs he ht hg
  rw [Real.inner_apply, Real.inner_apply, he, ht, hg]
  by_cases hx : x ∈ Ω
  · rw [Set.indicator_of_mem hx, hs hx]
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφ.2.2 h))
    simp only [Set.indicator_of_notMem hx, hφx, mul_zero]

/-- Actual global density pairing for one fixed scalar compact test and output coordinate. -/
def vectorDirichletTestDensityCLM
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (j : Fin m) :
    Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℝ] ℝ :=
  innerSL ℝ hφ.testCls ∘L univVectorCoordinateCLM j

/-- Actual global state pairing for the same fixed compact test. -/
def vectorDirichletTestStateCLM
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (j : Fin m) :
    VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m →L[ℝ] ℝ :=
  (laplaceBilin univ).flip hφ.toH01 ∘L
    PiLp.proj 2 (fun _ : Fin m ↦ H01 (univ : Set (EuclideanSpace ℝ (Fin d)))) j

theorem vectorDirichletTestDensityCLM_apply
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (j : Fin m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    vectorDirichletTestDensityCLM hφ j f = ⟪hφ.testCls, univVectorCoordinateCLM j f⟫ := rfl

theorem vectorDirichletTestStateCLM_apply
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (j : Fin m)
    (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m) :
    vectorDirichletTestStateCLM hφ j U = laplaceBilin univ (U j) hφ.toH01 := rfl

/-- The finite actual PDE, on a compact interior test, becomes the global fixed linear pairing. -/
theorem zeroExtended_vector_test_equation (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) (ν : VectorDirichletL2 Ω m)
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hpde : ∀ j : Fin m, ∀ W : H01 Ω, laplaceBilin Ω (U j) W =
      ⟪vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) -
        vectorDirichletCoordinate Ω j ν, W.val 0⟫)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (hcontained : tsupport φ ⊆ Ω)
    (j : Fin m) :
    vectorDirichletTestStateCLM hφ j (zeroExtendVectorDirichletState hΩ U) =
      vectorDirichletTestDensityCLM hφ j f -
        vectorDirichletTestDensityCLM hφ j (zeroExtendL2 hΩ ν) := by
  let hlocal : IsTestFn Ω φ := ⟨hφ.1, hφ.2.1, hcontained⟩
  have h := zeroExtendH01_interior_weak_equation hΩ (U j)
    (vectorDirichletCoordinate Ω j (restrictL2CLM Ω f) - vectorDirichletCoordinate Ω j ν)
    (hpde j) hlocal
  rw [map_sub, inner_sub_left, inner_zeroExtended_restricted_coordinate_test hΩ j f hlocal,
    ← coordinate_zeroExtendL2 hΩ j ν] at h
  change laplaceBilin univ (zeroExtendH01 hΩ (U j)) hφ.toH01 =
    ⟪univVectorCoordinateCLM j f, hφ.testCls⟫ -
      ⟪univVectorCoordinateCLM j (zeroExtendL2 hΩ ν), hφ.testCls⟫ at h
  change laplaceBilin univ (zeroExtendH01 hΩ (U j)) hφ.toH01 =
    ⟪hφ.testCls, univVectorCoordinateCLM j f⟫ -
      ⟪hφ.testCls, univVectorCoordinateCLM j (zeroExtendL2 hΩ ν)⟫
  simpa only [real_inner_comm] using h

/-- Actual finite PDEs pass to all fixed compact tests in the joint cofinal weak limit. -/
theorem vector_weak_test_equation_of_joint_limit
    (Ω : ℕ → Set (EuclideanSpace ℝ (Fin d))) (hΩ : ∀ k, MeasurableSet (Ω k))
    (ν : ∀ k, VectorDirichletL2 (Ω k) m) (U : ∀ k, VectorDirichletState (Ω k) m)
    (f νlimit : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (Ulimit : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m)
    (hpde : ∀ k, ∀ j : Fin m, ∀ W : H01 (Ω k), laplaceBilin (Ω k) (U k j) W =
      ⟪vectorDirichletCoordinate (Ω k) j (restrictL2CLM (Ω k) f) -
        vectorDirichletCoordinate (Ω k) j (ν k), W.val 0⟫)
    (hcontained : ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      ∀ᶠ k in atTop, K ⊆ Ω k)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hνt : Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendL2 (hΩ k) (ν k))) l
      (𝓝 (toWeakSpace ℝ _ νlimit)))
    (hUt : Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendVectorDirichletState (hΩ k) (U k))) l
      (𝓝 (toWeakSpace ℝ _ Ulimit))) :
    ∀ j : Fin m, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ∀ hφ : IsTestFn univ φ,
      laplaceBilin univ (Ulimit j) hφ.toH01 =
        ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j νlimit, hφ.testCls⟫ := by
  intro j φ hφ
  have heq : ∀ᶠ k in atTop,
      vectorDirichletTestStateCLM hφ j (zeroExtendVectorDirichletState (hΩ k) (U k)) =
        vectorDirichletTestDensityCLM hφ j f -
          vectorDirichletTestDensityCLM hφ j (zeroExtendL2 (hΩ k) (ν k)) :=
    (hcontained (tsupport φ) hφ.2.1.isCompact).mono (fun k hk ↦
      zeroExtended_vector_test_equation (hΩ k) (U k) (ν k) f (hpde k) hφ hk j)
  have hνeval : Tendsto
      (fun k ↦ vectorDirichletTestDensityCLM hφ j (zeroExtendL2 (hΩ k) (ν k))) l
      (𝓝 (vectorDirichletTestDensityCLM hφ j νlimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((vectorDirichletTestDensityCLM hφ j).continuous_comp_toWeakSpace_symm.tendsto
        (toWeakSpace ℝ _ νlimit)).comp hνt
  have hUeval : Tendsto
      (fun k ↦ vectorDirichletTestStateCLM hφ j (zeroExtendVectorDirichletState (hΩ k) (U k))) l
      (𝓝 (vectorDirichletTestStateCLM hφ j Ulimit)) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((vectorDirichletTestStateCLM hφ j).continuous_comp_toWeakSpace_symm.tendsto
        (toWeakSpace ℝ _ Ulimit)).comp hUt
  have h := tendsto_nhds_unique_of_eventuallyEq hUeval
    (tendsto_const_nhds.sub hνeval) (heq.filter_mono hl)
  rw [vectorDirichletTestStateCLM_apply, vectorDirichletTestDensityCLM_apply,
    vectorDirichletTestDensityCLM_apply] at h
  rw [inner_sub_left]
  simpa only [real_inner_comm] using h

/-- The concrete expanding open balls contain every compact set eventually. -/
theorem eventually_compact_subset_expanding_balls
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, K ⊆ Metric.ball 0 (k + 1 : ℝ) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with k hk
  intro x hx
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [Metric.mem_ball, dist_zero_right]
  linarith [hR x hx]

end PartialBalayage.Linear
