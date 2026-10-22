/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SobolevDistributionGradient
public import PartialBalayage.Linear.IsotropicEnergySpace
public import PartialBalayage.Linear.SobolevZeroExtension
public import CenteredMaximal.Ball.DirichletForm

/-!
# Actual Fourier energy of Dirichlet Sobolev states

Closedness of the genuine frequency multiplication graph extends the classical derivative
formula from compact smooth tests to the actual Dirichlet closure. Plancherel then identifies
the isotropic Fourier energy with the sum of squared physical gradient norms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform LineDeriv
open CenteredMaximal.Ball.DirichletSobolev
open scoped SchwartzMap LineDeriv ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure X)

/-- The actual value and Fourier gradient pair in a two-coordinate Hilbert product. -/
def globalPartialFourierGraphCLM (i : Fin d) :
    H1amb (univ : Set X) →L[ℝ] PiLp 2 (fun _ : Fin 2 ↦ L²) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ L²)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (Fin.cons (complexGlobalGraphCoordinateCLM 0)
      (fun _ : Fin 1 ↦ (ContinuousLinearMap.restrictScalars ℝ
        (Lp.fourierTransformₗᵢ X ℂ).toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          complexGlobalGraphCoordinateCLM i.succ))

private def energyComplexTestSchwartz {φ : X → ℝ} (hφ : IsTestFn univ φ) : 𝓢(X, ℂ) :=
  (hφ.2.1.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ.1)

private theorem energyComplexTestSchwartz_partial {φ : X → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) (x : X) :
    (∂_{EuclideanSpace.single i (1 : ℝ)} (energyComplexTestSchwartz hφ)) x =
      (partialD i φ x : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
    (hφ.1.differentiable (by simp) x), ContinuousLinearMap.fderiv]
  rfl

private theorem complexGlobalGraphCoordinate_test_value {φ : X → ℝ}
    (hφ : IsTestFn univ φ) :
    complexGlobalGraphCoordinateCLM 0 hφ.testGraph = (energyComplexTestSchwartz hφ).toLp 2 := by
  apply Lp.ext
  have hφae : hφ.testCls =ᵐ[volume] φ := by
    simpa only [Measure.restrict_univ, IsTestFn.testCls] using hφ.mem_lp.coeFn_toLp
  filter_upwards [complexGlobalGraphCoordinateCLM_ae 0 hφ.testGraph, hφae,
    (energyComplexTestSchwartz hφ).coeFn_toLp 2] with x hc hφx hs
  rw [hs]
  simp only [IsTestFn.testGraph_zero, hφx] at hc
  exact hc

private theorem complexGlobalGraphCoordinate_test_partial {φ : X → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) :
    complexGlobalGraphCoordinateCLM i.succ hφ.testGraph =
      (∂_{EuclideanSpace.single i (1 : ℝ)}
        (energyComplexTestSchwartz hφ) : 𝓢(X, ℂ)).toLp 2 := by
  apply Lp.ext
  have hφae : hφ.partialCls i =ᵐ[volume] partialD i φ := by
    simpa only [Measure.restrict_univ, IsTestFn.partialCls] using
      (hφ.memLp_partialD i).coeFn_toLp
  filter_upwards [complexGlobalGraphCoordinateCLM_ae i.succ hφ.testGraph, hφae,
    (∂_{EuclideanSpace.single i (1 : ℝ)} (energyComplexTestSchwartz hφ) :
      𝓢(X, ℂ)).coeFn_toLp 2] with x hc hφx hs
  rw [hs, energyComplexTestSchwartz_partial]
  simp only [IsTestFn.testGraph_succ, hφx] at hc
  exact hc

private theorem globalPartialFourierGraphCLM_testGraph {φ : X → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) :
    globalPartialFourierGraphCLM i hφ.testGraph ∈
      weightedFourierGraph (E := ℂ) (fun ξ : X ↦
        (2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) := by
  change ∀ᵐ ξ, (𝓕 (complexGlobalGraphCoordinateCLM i.succ hφ.testGraph) : L²) ξ =
    ((2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) •
      (𝓕 (complexGlobalGraphCoordinateCLM 0 hφ.testGraph) : L²) ξ
  rw [complexGlobalGraphCoordinate_test_value, complexGlobalGraphCoordinate_test_partial,
    SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  filter_upwards [(𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)}
    (energyComplexTestSchwartz hφ)) : 𝓢(X, ℂ)).coeFn_toLp 2,
    (𝓕 (energyComplexTestSchwartz hφ) : 𝓢(X, ℂ)).coeFn_toLp 2] with ξ hg hf
  rw [hg, hf, SchwartzMap.fourier_lineDerivOp_eq]
  have hinner : (fun ξ : X ↦
      inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single i (1 : ℝ))).hasTemperateGrowth
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hinner,
    smul_eq_mul, Complex.real_smul, mul_assoc]

/-- The actual Fourier representatives of the global Dirichlet gradient have the exact symbol. -/
theorem fourier_complexGlobalGraphCoordinate_partial_ae
    (U : H01 (univ : Set X)) (i : Fin d) :
    (𝓕 (complexGlobalGraphCoordinateCLM i.succ (U : H1amb univ)) : L²) =ᵐ[volume]
      fun ξ ↦ ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) •
          (𝓕 (complexGlobalGraphCoordinateCLM 0 (U : H1amb univ)) : L²) ξ := by
  have hcl : (U : H1amb (univ : Set X)) ∈ closure (testGraphSet (univ : Set X)) := by
    have hcl' : (U : H1amb (univ : Set X)) ∈ closure
        ((Submodule.span ℝ (testGraphSet (univ : Set X))) : Set (H1amb univ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact U.property
    rw [span_testGraphSet] at hcl'
    exact hcl'
  have himage : globalPartialFourierGraphCLM i '' testGraphSet (univ : Set X) ⊆
      (weightedFourierGraph (E := ℂ) (fun ξ : X ↦
        (2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) :
          Set (PiLp 2 (fun _ : Fin 2 ↦ L²))) := by
    rintro V ⟨W, ⟨φ, hφ, rfl⟩, rfl⟩
    exact globalPartialFourierGraphCLM_testGraph hφ i
  exact (closure_minimal himage (isClosed_weightedFourierGraph _))
    ((image_closure_subset_closure_image (globalPartialFourierGraphCLM i).continuous)
      ⟨U, hcl, rfl⟩)

/-- Complexification of a genuine global graph coordinate preserves its actual `L²` norm. -/
theorem norm_complexGlobalGraphCoordinateCLM (j : Fin (d + 1))
    (U : H1amb (univ : Set X)) :
    ‖complexGlobalGraphCoordinateCLM j U‖ = ‖U j‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hmeas : AEStronglyMeasurable (U j : X → ℝ) volume := by
    simpa only [Measure.restrict_univ] using Lp.aestronglyMeasurable (U j)
  have he := eLpNorm_congr_norm_ae (p := 2)
    (Lp.aestronglyMeasurable (complexGlobalGraphCoordinateCLM j U)) hmeas
    ((complexGlobalGraphCoordinateCLM_ae j U).mono fun x hx ↦ by
      rw [hx, Complex.norm_real, Real.norm_eq_abs])
  simpa only [Measure.restrict_univ] using congrArg ENNReal.toReal he

private theorem enorm_globalPartialSymbol_sq (i : Fin d) (ξ : X) :
    ‖(2 * Real.pi * Complex.I) *
      (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)‖ₑ ^ (2 : ℕ) =
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal ((ξ i) ^ 2) := by
  have hn : ‖(2 * Real.pi * Complex.I) *
      (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)‖ =
        (2 * Real.pi) * |ξ i| := by
    simp [EuclideanSpace.inner_single_right, abs_of_pos Real.pi_pos]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hn, mul_pow, sq_abs,
    ENNReal.ofReal_mul (sq_nonneg _)]

/-- Summing the actual squared Fourier gradients gives the full isotropic frequency weight. -/
theorem sum_fourier_globalGradient_enorm_sq_ae (U : H01 (univ : Set X)) :
    (fun ξ ↦ ∑ i : Fin d,
      ‖(𝓕 (complexGlobalGraphCoordinateCLM i.succ (U : H1amb univ)) : L²) ξ‖ₑ ^
        (2 : ℕ))
      =ᵐ[volume] fun ξ ↦ ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ)) *
          ‖(𝓕 (complexGlobalGraphCoordinateCLM 0 (U : H1amb univ)) : L²) ξ‖ₑ ^
            (2 : ℕ)) := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin d ↦
    fourier_complexGlobalGraphCoordinate_partial_ae U i)] with ξ hξ
  simp_rw [hξ, enorm_smul, mul_pow, enorm_globalPartialSymbol_sq]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg (ξ i)),
    ← EuclideanSpace.real_norm_sq_eq, mul_assoc]
  simp only [mul_pow]

/-- Exact actual Fourier energy equals the physical Dirichlet energy, with unitary normalization. -/
theorem fourierEnergy_two_complexGlobalGraphCoordinate_H01 (U : H01 (univ : Set X)) :
    ENNReal.ofReal ((2 * Real.pi) ^ 2) *
      fourierEnergy 2 (complexGlobalGraphCoordinateCLM (d := d) 0
        (U : H1amb (univ : Set X))) =
        ENNReal.ofReal (laplaceBilin univ U U) := by
  have hmeas (i : Fin d) : AEMeasurable
      (fun ξ ↦ ‖(𝓕 (complexGlobalGraphCoordinateCLM i.succ
        (U : H1amb (univ : Set X))) : L²) ξ‖ₑ ^ (2 : ℕ)) volume := by
    exact (Lp.aestronglyMeasurable (𝓕 (complexGlobalGraphCoordinateCLM i.succ
      (U : H1amb (univ : Set X))) : L²)).enorm.pow_const 2
  calc
    _ = ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ (2 : ℕ)) *
          ‖(𝓕 (complexGlobalGraphCoordinateCLM 0 (U : H1amb univ)) : L²) ξ‖ₑ ^
            (2 : ℕ)) := by
      rw [fourierEnergy, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [Real.rpow_two]
    _ = ∫⁻ ξ, ∑ i : Fin d,
        ‖(𝓕 (complexGlobalGraphCoordinateCLM i.succ (U : H1amb univ)) : L²) ξ‖ₑ ^
          (2 : ℕ) := lintegral_congr_ae (sum_fourier_globalGradient_enorm_sq_ae U).symm
    _ = ∑ i : Fin d, ‖complexGlobalGraphCoordinateCLM i.succ (U : H1amb univ)‖ₑ ^
        (2 : ℕ) := by
      rw [lintegral_finsetSum' Finset.univ (fun i _ ↦ hmeas i)]
      simp only [← enorm_sq_eq_lintegral_fourier]
    _ = ENNReal.ofReal (laplaceBilin univ U U) := by
      rw [laplaceBilin_self, ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg _)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        norm_complexGlobalGraphCoordinateCLM]

/-- True zero extension preserves the physical Dirichlet energy. -/
theorem laplaceBilin_zeroExtendH01 {Ω : Set X} (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    laplaceBilin univ (zeroExtendH01 hΩ U) (zeroExtendH01 hΩ U) = laplaceBilin Ω U U := by
  rw [laplaceBilin_self, laplaceBilin_self]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖zeroExtendUnivL2CLM hΩ ((U : H1amb Ω) i.succ)‖ ^ 2 =
    ‖(U : H1amb Ω) i.succ‖ ^ 2
  rw [norm_zeroExtendUnivL2CLM]

/-- Fourier energy of the genuine zero extension equals the original physical Dirichlet energy. -/
theorem fourierEnergy_two_zeroExtendH01 {Ω : Set X} (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    ENNReal.ofReal ((2 * Real.pi) ^ 2) *
      fourierEnergy 2 (complexGlobalGraphCoordinateCLM (d := d) 0
        (zeroExtendH01 hΩ U : H1amb (univ : Set X))) =
          ENNReal.ofReal (laplaceBilin Ω U U) := by
  rw [fourierEnergy_two_complexGlobalGraphCoordinate_H01, laplaceBilin_zeroExtendH01]

end PartialBalayage.Linear
