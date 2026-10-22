/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalSecondSobolev
public import PartialBalayage.Linear.LocalCutoffEquation

/-!
# Actual real weak-gradient graphs from Fourier Sobolev regularity

Represented distributional first derivatives of a complex `L²` state give the genuine real
weak-gradient graph of its real part. The weak integral identities follow by testing the
actual tempered-distribution equation, then taking real parts. Order-one Fourier Sobolev
regularity supplies the represented first derivatives; order-two regularity gives order-one
regularity of those derivative states.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace SchwartzMap LineDeriv

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The real part of a genuine complex `L²` class belongs to the all-space scalar `L²` space. -/
theorem memLp_realPart_univ (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemLp (fun x ↦ (u x : ℂ).re) 2 (volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d)))) := by
  simpa only [Measure.restrict_univ, Function.comp_def, Complex.reCLM_apply] using
    Complex.reCLM.comp_memLp u

/-- The actual all-space scalar `L²` class of the real part of a complex `L²` state. -/
def realPartL2Univ (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    L2D (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  (memLp_realPart_univ u).toLp (fun x ↦ (u x : ℂ).re)

/-- The all-space real-part class has its actual real-part representative almost everywhere. -/
theorem realPartL2Univ_ae (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    realPartL2Univ u =ᵐ[volume] fun x ↦ (u x : ℂ).re := by
  simpa only [Measure.restrict_univ, realPartL2Univ] using
    (memLp_realPart_univ u).coeFn_toLp

/-- The actual value-gradient tuple built from represented complex `L²` states. -/
def complexL2GradientGraph (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (g : Fin d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  WithLp.toLp 2 (Fin.cons (realPartL2Univ u) (fun i ↦ realPartL2Univ (g i)))

/-- The graph's value coordinate is the actual real part of the original state. -/
theorem complexL2GradientGraph_value_ae
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (g : Fin d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    complexL2GradientGraph u g 0 =ᵐ[volume] fun x ↦ (u x : ℂ).re :=
  realPartL2Univ_ae u

/-- The graph's gradient coordinate is the actual real part of its represented derivative. -/
theorem complexL2GradientGraph_partial_ae
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (g : Fin d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) (i : Fin d) :
    complexL2GradientGraph u g i.succ =ᵐ[volume] fun x ↦ (g i x : ℂ).re :=
  realPartL2Univ_ae (g i)

private def complexTestSchwartz {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn univ φ) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  (hφ.2.1.comp_left Complex.ofRealCLM.map_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ.1)

private theorem complexTestSchwartz_partial {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn univ φ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    (∂_{EuclideanSpace.single i (1 : ℝ)} (complexTestSchwartz hφ)) x = (partialD i φ x : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
    (hφ.1.differentiable (by simp) x), ContinuousLinearMap.fderiv]
  rfl

/-- The real weak-gradient integral identity comes from the actual `L²` derivative equation. -/
theorem integral_partial_mul_realPart_add_eq_zero
    (u g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) (i : Fin d)
    (hder : ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (g : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn univ φ) :
    (∫ x, partialD i φ x * (u x : ℂ).re) + ∫ x, φ x * (g x : ℂ).re = 0 := by
  let ψ := complexTestSchwartz hφ
  have heq := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) ↦ T ψ) hder
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at heq
  have hL : Integrable (fun x ↦ (-(∂_{EuclideanSpace.single i (1 : ℝ)} ψ)) x * (u x : ℂ)) :=
    (-(∂_{EuclideanSpace.single i (1 : ℝ)} ψ)).memLp 2 |>.integrable_mul (Lp.memLp u)
  have hR : Integrable (fun x ↦ ψ x * (g x : ℂ)) :=
    ψ.memLp 2 |>.integrable_mul (Lp.memLp g)
  have hre := congrArg (fun z : ℂ ↦ Complex.reCLM z) heq
  rw [← Complex.reCLM.integral_comp_comm hL, ← Complex.reCLM.integral_comp_comm hR] at hre
  have hleft : (∫ x, Complex.reCLM ((-(∂_{EuclideanSpace.single i (1 : ℝ)} ψ)) x * (u x : ℂ))) =
      -(∫ x, partialD i φ x * (u x : ℂ).re) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [neg_apply, ψ, complexTestSchwartz_partial,
      Complex.reCLM_apply, neg_mul, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hright : (∫ x, Complex.reCLM (ψ x * (g x : ℂ))) =
      ∫ x, φ x * (g x : ℂ).re := by
    apply integral_congr_ae
    filter_upwards with x
    change ((φ x : ℂ) * (g x : ℂ)).re = _
    simp
  rw [hleft, hright] at hre
  linarith

/-- Actual represented directional derivatives give genuine all-space real `W12` membership. -/
theorem complexL2GradientGraph_mem_W12
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (g : Fin d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hder : ∀ i : Fin d,
      ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
        (g i : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    complexL2GradientGraph u g ∈ W12 (univ : Set (EuclideanSpace ℝ (Fin d))) := by
  rw [mem_W12_iff]
  intro φ hφ i
  have hφvalue : hφ.testCls =ᵐ[volume] φ := by
    simpa only [Measure.restrict_univ, IsTestFn.testCls] using hφ.mem_lp.coeFn_toLp
  have hφpartial : hφ.partialCls i =ᵐ[volume] partialD i φ := by
    simpa only [Measure.restrict_univ, IsTestFn.partialCls] using
      (hφ.memLp_partialD i).coeFn_toLp
  have hA : ⟪hφ.partialCls i, complexL2GradientGraph u g 0⟫ =
      ∫ x, partialD i φ x * (u x : ℂ).re := by
    rw [L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [hφpartial, complexL2GradientGraph_value_ae u g] with x htest hu
    simp only [Real.inner_apply, htest, hu]
  have hB : ⟪hφ.testCls, complexL2GradientGraph u g i.succ⟫ =
      ∫ x, φ x * (g i x : ℂ).re := by
    rw [L2.inner_def, setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [hφvalue, complexL2GradientGraph_partial_ae u g i] with x htest hg
    simp only [Real.inner_apply, htest, hg]
  rw [hA, hB]
  exact integral_partial_mul_realPart_add_eq_zero u (g i) i (hder i) hφ

/-- Order-one Fourier Sobolev regularity supplies actual represented `L²` partial derivatives. -/
theorem exists_L2_partial_of_memSobolev_one
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 1 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) (i : Fin d) :
    ∃ g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
        (g : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  apply TemperedDistribution.memSobolev_zero_iff.mp
  simpa only [sub_self] using hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))

/-- A chosen genuine `L²` representative of a Fourier Sobolev partial derivative. -/
def sobolevL2Partial (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 1 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) (i : Fin d) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Classical.choose (exists_L2_partial_of_memSobolev_one u hu i)

/-- The chosen derivative class satisfies the actual tempered-distribution equation. -/
theorem sobolevL2Partial_represents
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 1 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) (i : Fin d) :
    ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (sobolevL2Partial u hu i : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :=
  Classical.choose_spec (exists_L2_partial_of_memSobolev_one u hu i)

/-- The genuine real weak-gradient graph of an order-one Fourier Sobolev `L²` state. -/
def fourierSobolevRealGraph (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 1 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    W12 (univ : Set (EuclideanSpace ℝ (Fin d))) :=
  ⟨complexL2GradientGraph u (sobolevL2Partial u hu),
    complexL2GradientGraph_mem_W12 u _ (sobolevL2Partial_represents u hu)⟩

/-- An actual real `W12` graph exists, with represented value and first derivatives. -/
theorem exists_real_W12_graph_of_memSobolev_one
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 1 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ∃ V : W12 (univ : Set (EuclideanSpace ℝ (Fin d))),
      ((V : H1amb univ) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] (fun x ↦ (u x : ℂ).re) ∧
      ∀ i : Fin d, ((V : H1amb univ) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] fun x ↦ (sobolevL2Partial u hu i x : ℂ).re :=
  ⟨fourierSobolevRealGraph u hu, complexL2GradientGraph_value_ae u _,
    complexL2GradientGraph_partial_ae u _⟩

/-- For an actual order-two state, its represented first partials have order-one regularity. -/
theorem memSobolev_one_sobolevL2Partial_of_memSobolev_two
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 2 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) (i : Fin d) :
    TemperedDistribution.MemSobolev 1 2
      (sobolevL2Partial u (TemperedDistribution.MemSobolev.mono (by norm_num) hu) i :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  rw [← sobolevL2Partial_represents]
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
    hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))

end PartialBalayage.Linear
