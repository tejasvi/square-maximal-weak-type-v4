/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierSobolevGraph
public import PartialBalayage.Linear.L2ZeroExtension
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Distributional and Fourier gradients of actual Dirichlet graphs

Each actual all-space graph coordinate is represented in complex `L²` by genuine linear zero
extension and complexification. The distributional derivative constraint is a closed linear
condition on the ambient graph. Schwartz integration by parts proves it on smooth test graphs,
so it holds on their defining Dirichlet closure. Fourier transformation then gives the exact
frequency multiplier identity for the actual represented gradient coordinates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform LineDeriv
open CenteredMaximal.Ball.DirichletSobolev
open scoped SchwartzMap LineDeriv

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The actual complex global `L²` class of an all-space real graph coordinate. -/
def complexGlobalGraphCoordinateCLM (j : Fin (d + 1)) :
    H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Complex.ofRealCLM.compLpL 2 volume ∘L zeroExtendL2CLM (μ := volume) MeasurableSet.univ ∘L
    PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D (univ : Set (EuclideanSpace ℝ (Fin d)))) j

/-- The actual complex coordinate agrees almost everywhere with the real graph coordinate. -/
theorem complexGlobalGraphCoordinateCLM_ae (j : Fin (d + 1))
    (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) :
    complexGlobalGraphCoordinateCLM j U =ᵐ[volume] fun x ↦ ((U j x : ℝ) : ℂ) := by
  change Complex.ofRealCLM.compLp (zeroExtendL2 MeasurableSet.univ (U j)) =ᵐ[volume] _
  filter_upwards [Complex.ofRealCLM.coeFn_compLp
    (zeroExtendL2 (μ := volume) MeasurableSet.univ (U j)),
    zeroExtendL2_ae (μ := volume) MeasurableSet.univ (U j)] with x hcomplex hreal
  simp only [indicator_univ] at hreal
  rw [hcomplex, hreal]
  rfl

/-- The actual tempered-distribution inclusion of an all-space real graph coordinate. -/
def complexGlobalGraphDistributionCLM (j : Fin (d + 1)) :
    H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      𝓢'(EuclideanSpace ℝ (Fin d), ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ ∘L
    complexGlobalGraphCoordinateCLM j

/-- The actual distributional gradient constraint on the ambient all-space graph. -/
def globalGradientConstraintCLM (i : Fin d) :
    H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      𝓢'(EuclideanSpace ℝ (Fin d), ℂ) :=
  (lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)
    (EuclideanSpace.single i (1 : ℝ))).restrictScalars ℝ ∘L
      complexGlobalGraphDistributionCLM 0 - complexGlobalGraphDistributionCLM i.succ

/-- Evaluation of the actual distributional gradient constraint. -/
theorem globalGradientConstraintCLM_apply (i : Fin d)
    (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) :
    globalGradientConstraintCLM i U =
      ∂_{EuclideanSpace.single i (1 : ℝ)}
        (complexGlobalGraphCoordinateCLM 0 U : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) -
          (complexGlobalGraphCoordinateCLM i.succ U : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := rfl

private def globalComplexTestSchwartz {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn univ φ) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  (hφ.2.1.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ.1)

private theorem globalComplexTestSchwartz_partial {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    (∂_{EuclideanSpace.single i (1 : ℝ)} (globalComplexTestSchwartz hφ)) x =
      (partialD i φ x : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
    (hφ.1.differentiable (by simp) x), ContinuousLinearMap.fderiv]
  rfl

private theorem complexGlobalGraphCoordinate_test_value_ae
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) :
    complexGlobalGraphCoordinateCLM 0 hφ.testGraph =ᵐ[volume] globalComplexTestSchwartz hφ := by
  have hφae : hφ.testCls =ᵐ[volume] φ := by
    simpa only [Measure.restrict_univ, IsTestFn.testCls] using hφ.mem_lp.coeFn_toLp
  filter_upwards [complexGlobalGraphCoordinateCLM_ae 0 hφ.testGraph, hφae] with x hc hφx
  simp only [IsTestFn.testGraph_zero, hφx] at hc
  exact hc

private theorem complexGlobalGraphCoordinate_test_partial_ae
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) (i : Fin d) :
    complexGlobalGraphCoordinateCLM i.succ hφ.testGraph =ᵐ[volume]
      ((∂_{EuclideanSpace.single i (1 : ℝ)} (globalComplexTestSchwartz hφ) :
        𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : EuclideanSpace ℝ (Fin d) → ℂ) := by
  have hφae : hφ.partialCls i =ᵐ[volume] partialD i φ := by
    simpa only [Measure.restrict_univ, IsTestFn.partialCls] using
      (hφ.memLp_partialD i).coeFn_toLp
  filter_upwards [complexGlobalGraphCoordinateCLM_ae i.succ hφ.testGraph, hφae] with x hc hφx
  rw [globalComplexTestSchwartz_partial]
  simp only [IsTestFn.testGraph_succ, hφx] at hc
  exact hc

/-- Smooth test graphs satisfy the actual represented tempered-distribution gradient equation. -/
theorem globalGradientConstraintCLM_testGraph {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) :
    globalGradientConstraintCLM i hφ.testGraph = 0 := by
  rw [globalGradientConstraintCLM_apply]
  apply sub_eq_zero.mpr
  ext ψ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hleft : (∫ x, (-(∂_{EuclideanSpace.single i (1 : ℝ)} ψ)) x *
      complexGlobalGraphCoordinateCLM 0 hφ.testGraph x) =
      ∫ x, (-(∂_{EuclideanSpace.single i (1 : ℝ)} ψ)) x *
        globalComplexTestSchwartz hφ x := by
    apply integral_congr_ae
    filter_upwards [complexGlobalGraphCoordinate_test_value_ae hφ] with x hx
    rw [hx]
  have hright : (∫ x, ψ x * complexGlobalGraphCoordinateCLM i.succ hφ.testGraph x) =
      ∫ x, ψ x *
        (∂_{EuclideanSpace.single i (1 : ℝ)} (globalComplexTestSchwartz hφ)) x := by
    apply integral_congr_ae
    filter_upwards [complexGlobalGraphCoordinate_test_partial_ae hφ i] with x hx
    rw [hx]
  rw [hleft, hright]
  have hibp := (SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
    ψ (globalComplexTestSchwartz hφ) (EuclideanSpace.single i (1 : ℝ))).symm
  simpa only [← integral_neg, neg_apply, neg_mul] using hibp

/-- Actual Dirichlet graph closure preserves the represented distributional derivative equation. -/
theorem lineDeriv_complexGlobalGraphCoordinate_H01
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d)))) (i : Fin d) :
    ∂_{EuclideanSpace.single i (1 : ℝ)}
      (Lp.toTemperedDistribution (complexGlobalGraphCoordinateCLM (d := d) 0
        (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))))) =
      Lp.toTemperedDistribution (complexGlobalGraphCoordinateCLM i.succ
        (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d))))) := by
  have hs : (Submodule.span ℝ (testGraphSet univ)) ≤ (globalGradientConstraintCLM i).ker := by
    apply Submodule.span_le.mpr
    rintro X ⟨φ, hφ, rfl⟩
    exact globalGradientConstraintCLM_testGraph hφ i
  have hcl : (U : H1amb (univ : Set (EuclideanSpace ℝ (Fin d)))) ∈ closure
      ((Submodule.span ℝ (testGraphSet (univ : Set (EuclideanSpace ℝ (Fin d))))) :
        Set (H1amb (univ : Set (EuclideanSpace ℝ (Fin d))))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact U.property
  have hz := (closure_minimal hs (globalGradientConstraintCLM i).isClosed_ker) hcl
  change globalGradientConstraintCLM i (U : H1amb univ) = 0 at hz
  rw [globalGradientConstraintCLM_apply] at hz
  exact sub_eq_zero.mp hz

/-- The actual Fourier transform of a Dirichlet gradient has the exact frequency symbol. -/
theorem fourier_complexGlobalGraphCoordinate_partial
    (U : H01 (univ : Set (EuclideanSpace ℝ (Fin d)))) (i : Fin d) :
    ((𝓕 (complexGlobalGraphCoordinateCLM i.succ (U : H1amb univ)) :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (2 * Real.pi * Complex.I) • TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : EuclideanSpace ℝ (Fin d) ↦ inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)))
        ((𝓕 (complexGlobalGraphCoordinateCLM 0 (U : H1amb univ)) :
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
            𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  rw [← Lp.fourier_toTemperedDistribution_eq, ← lineDeriv_complexGlobalGraphCoordinate_H01,
    TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq]

end PartialBalayage.Linear
