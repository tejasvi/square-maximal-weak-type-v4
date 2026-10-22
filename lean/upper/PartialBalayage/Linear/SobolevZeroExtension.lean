/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.L2ZeroExtension
public import CenteredMaximal.Ball.DirichletH01

/-!
# Actual zero extension of Dirichlet Sobolev graphs

The genuine isometric L² zero extension is applied to every value and gradient coordinate.
It sends compact interior test graphs to their whole-space test graphs, hence sends the actual
H01 closure into H01 on the whole space. This first-derivative assertion includes the true
zero-boundary condition; it does not assert a whole-space Laplace equation for local solutions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Transport the actual zero extension to the existing `L2D univ` coordinate convention. -/
def zeroExtendUnivL2CLM (hΩ : MeasurableSet Ω) :
    L2D Ω →L[ℝ] L2D (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simp) ∘L zeroExtendL2CLM hΩ

theorem zeroExtendUnivL2CLM_ae (hΩ : MeasurableSet Ω) (f : L2D Ω) :
    zeroExtendUnivL2CLM hΩ f =ᵐ[volume.restrict univ]
      Ω.indicator (f : EuclideanSpace ℝ (Fin d) → ℝ) := by
  have hm := Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1 : ENNReal))
    (by simp : (1 : ENNReal) ≠ ∞)
    (by simp : volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d))) ≤
      (1 : ENNReal) • volume)
    (zeroExtendL2 hΩ f)
  exact hm.trans (by simpa only [Measure.restrict_univ] using zeroExtendL2_ae hΩ f)

theorem norm_zeroExtendUnivL2CLM (hΩ : MeasurableSet Ω) (f : L2D Ω) :
    ‖zeroExtendUnivL2CLM hΩ f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (zeroExtendUnivL2CLM_ae hΩ f),
    Measure.restrict_univ, eLpNorm_indicator_eq_eLpNorm_restrict hΩ, Lp.norm_def]

/-- Actual simultaneous extension of the value and first weak derivative coordinates. -/
def zeroExtendH1amb (hΩ : MeasurableSet Ω) :
    H1amb Ω →L[ℝ] H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ L2D univ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i ↦ zeroExtendUnivL2CLM hΩ ∘L
      PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) i)

theorem zeroExtendH1amb_apply (hΩ : MeasurableSet Ω) (U : H1amb Ω) (i : Fin (d + 1)) :
    zeroExtendH1amb hΩ U i = zeroExtendUnivL2CLM hΩ (U i) := rfl

theorem norm_zeroExtendH1amb (hΩ : MeasurableSet Ω) (U : H1amb Ω) :
    ‖zeroExtendH1amb hΩ U‖ = ‖U‖ := by
  apply pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0) |>.mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [zeroExtendH1amb_apply, norm_zeroExtendUnivL2CLM]

/-- Zero extension of a genuine compact interior test graph is its global test graph. -/
theorem zeroExtendH1amb_testGraph (hΩ : MeasurableSet Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Ω φ) :
    zeroExtendH1amb hΩ hφ.testGraph = (hφ.mono (subset_univ Ω)).testGraph := by
  let hg := hφ.mono (subset_univ Ω)
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [zeroExtendH1amb_apply, IsTestFn.testGraph_zero, IsTestFn.testGraph_zero]
    apply Lp.ext
    have hlocal : ∀ᵐ x ∂(volume.restrict univ), x ∈ Ω → hφ.testCls x = φ x := by
      simpa only [Measure.restrict_univ, IsTestFn.testCls] using
        (ae_restrict_iff' hΩ).mp hφ.mem_lp.coeFn_toLp
    filter_upwards [zeroExtendUnivL2CLM_ae hΩ hφ.testCls,
      hg.mem_lp.coeFn_toLp, hlocal] with x hx hgx hφx
    change hg.testCls x = φ x at hgx
    change zeroExtendUnivL2CLM hΩ hφ.testCls x = hg.testCls x
    rw [hx, hgx]
    by_cases hmem : x ∈ Ω
    · rw [indicator_of_mem hmem, hφx hmem]
    · rw [indicator_of_notMem hmem]
      symm
      exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hmem (hφ.2.2 hs))
  · rw [zeroExtendH1amb_apply, IsTestFn.testGraph_succ, IsTestFn.testGraph_succ]
    apply Lp.ext
    have hlocal : ∀ᵐ x ∂(volume.restrict univ),
        x ∈ Ω → hφ.partialCls j x = partialD j φ x := by
      simpa only [Measure.restrict_univ, IsTestFn.partialCls] using
        (ae_restrict_iff' hΩ).mp (hφ.memLp_partialD j).coeFn_toLp
    filter_upwards [zeroExtendUnivL2CLM_ae hΩ (hφ.partialCls j),
      (hg.memLp_partialD j).coeFn_toLp, hlocal] with x hx hgx hφx
    change hg.partialCls j x = partialD j φ x at hgx
    change zeroExtendUnivL2CLM hΩ (hφ.partialCls j) x = hg.partialCls j x
    rw [hx, hgx]
    by_cases hmem : x ∈ Ω
    · rw [indicator_of_mem hmem, hφx hmem]
    · rw [indicator_of_notMem hmem]
      symm
      exact image_eq_zero_of_notMem_tsupport (fun hs ↦
        hmem (hφ.2.2 (tsupport_partialD_subset j φ hs)))

/-- Continuity and true test-graph preservation give actual global H01 membership. -/
theorem zeroExtendH1amb_mem_H01 (hΩ : MeasurableSet Ω) {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    zeroExtendH1amb hΩ U ∈ H01 univ := by
  have hcl : U ∈ closure (testGraphSet Ω) := by
    have hcl' : U ∈ closure ((Submodule.span ℝ (testGraphSet Ω)) : Set (H1amb Ω)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hU
    rw [span_testGraphSet] at hcl'
    exact hcl'
  have himage : zeroExtendH1amb hΩ '' testGraphSet Ω ⊆
      (H01 (univ : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb univ)) := by
    rintro V ⟨W, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [zeroExtendH1amb_testGraph hΩ hφ]
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨φ, hφ.mono (subset_univ Ω), rfl⟩)
  exact (closure_minimal himage (Submodule.isClosed_topologicalClosure _))
    ((image_closure_subset_closure_image (zeroExtendH1amb hΩ).continuous) ⟨U, hcl, rfl⟩)

/-- The actual isometric zero-extension operator on Dirichlet Sobolev states. -/
def zeroExtendH01 (hΩ : MeasurableSet Ω) :
    H01 Ω →L[ℝ] H01 (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  (zeroExtendH1amb hΩ).restrict fun _ hU ↦ zeroExtendH1amb_mem_H01 hΩ hU

theorem norm_zeroExtendH01 (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    ‖zeroExtendH01 hΩ U‖ = ‖U‖ := norm_zeroExtendH1amb hΩ U

end PartialBalayage.Linear
