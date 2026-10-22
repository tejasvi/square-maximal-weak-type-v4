/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallWeakDistribution

/-!
# Genuine interior cutoff identities for scalar Sobolev graphs

Multiplication by an actual smooth compactly supported cutoff permits testing an `H01` graph
against arbitrary smooth functions on the ambient Euclidean space. The weak product identity
is proved from the graph's existing first-derivative constraints, without assuming extra
regularity of its gradients or imposing zero boundary values on them.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Multiplying a genuine cutoff by an arbitrary smooth function retains the cutoff support. -/
theorem isTestFn_mul_smooth {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : IsTestFn Ω (χ * φ) :=
  ⟨hχ.1.mul hφ, hχ.2.1.mul_right, tsupport_mul_subset_left.trans hχ.2.2⟩

/-- The classical coordinate product rule for the actual cutoff test functions. -/
theorem partialD_mul_smooth {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (χ * φ) x = partialD i χ x * φ x + χ x * partialD i φ x := by
  rw [partialD, fderiv_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, partialD]
  ring

/-- The actual second coordinate product rule, needed in the localized Laplace equation. -/
theorem partialD_twice_mul_smooth {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (partialD i (χ * φ)) x =
      partialD i (partialD i χ) x * φ x +
        partialD i χ x * partialD i φ x + partialD i χ x * partialD i φ x +
        χ x * partialD i (partialD i φ) x := by
  have hχi : ContDiff ℝ (⊤ : ℕ∞) (partialD i χ) :=
    (hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (partialD i φ) :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hprod : partialD i (χ * φ) = (partialD i χ) * φ + χ * (partialD i φ) :=
    funext (partialD_mul_smooth hχ hφ i)
  have hA : ContDiff ℝ (⊤ : ℕ∞) ((partialD i χ) * φ) := by
    simpa only [Pi.mul_def] using hχi.mul hφ
  have hB : ContDiff ℝ (⊤ : ℕ∞) (χ * (partialD i φ)) := by
    simpa only [Pi.mul_def] using hχ.mul hφi
  rw [hprod, partialD_add (hA.differentiable (by simp)) (hB.differentiable (by simp)) i]
  simp only [Pi.add_apply]
  rw [partialD_mul_smooth hχi hφ i x, partialD_mul_smooth hχ hφi i x]
  ring

/-- The genuine Laplace product identity for smooth scalar cutoffs. -/
theorem laplacian_mul_smooth {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian (χ * φ) x = χ x * Laplacian.laplacian φ x +
      2 * (∑ i : Fin d, partialD i χ x * partialD i φ x) +
      Laplacian.laplacian χ x * φ x := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [laplacian_eq_sum_partialD (χ * φ) (hχ2.mul hφ2),
    laplacian_eq_sum_partialD χ hχ2, laplacian_eq_sum_partialD φ hφ2]
  simp_rw [partialD_twice_mul_smooth hχ hφ]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Localization of the genuine weak gradient by a compactly supported interior cutoff.
This is a weak integral identity derived from the actual `H01` graph constraints. -/
theorem weak_gradient_cutoff_product (U : H01 Ω)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * χ x * partialD i φ x) =
      -(∫ x in Ω, (((U : H1amb Ω) i.succ x : ℝ) * χ x +
        ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x) * φ x) := by
  let htest := isTestFn_mul_smooth hχ hφ
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (partialD i φ) :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  let htesti := isTestFn_mul_smooth hχ hφi
  let hχitest := isTestFn_mul_smooth (hχ.partialD i) hφ
  have hgrad := (mem_W12_iff (U : H1amb Ω)).mp
    ((H01_le_W12 Ω) U.property) (χ * φ) htest i
  have hgrad' : ⟪htest.partialCls i, (U : H1amb Ω) 0⟫ =
      -⟪htest.testCls, (U : H1amb Ω) i.succ⟫ := by linarith [hgrad]
  have hg :
      (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) *
        (partialD i χ x * φ x + χ x * partialD i φ x)) =
      -(∫ x in Ω, ((U : H1amb Ω) i.succ x : ℝ) * χ x * φ x) := by
    rw [L2.inner_def, L2.inner_def] at hgrad'
    convert! hgrad' using 1
    · apply integral_congr_ae
      filter_upwards [htest.memLp_partialD i |>.coeFn_toLp] with x hx
      simp only [Real.inner_apply, IsTestFn.partialCls, hx,
        partialD_mul_smooth hχ.1 hφ]
      ring
    · congr 1
      apply integral_congr_ae
      filter_upwards [htest.mem_lp.coeFn_toLp] with x hx
      simp only [Real.inner_apply, IsTestFn.testCls, hx, Pi.mul_apply]
      ring
  have hA : Integrable (fun x ↦ ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x * φ x)
      (volume.restrict Ω) := by
    convert! (Lp.memLp ((U : H1amb Ω) 0)).integrable_mul hχitest.mem_lp using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hB : Integrable (fun x ↦ ((U : H1amb Ω) 0 x : ℝ) * χ x * partialD i φ x)
      (volume.restrict Ω) := by
    convert! (Lp.memLp ((U : H1amb Ω) 0)).integrable_mul htesti.mem_lp using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hC : Integrable (fun x ↦ ((U : H1amb Ω) i.succ x : ℝ) * χ x * φ x)
      (volume.restrict Ω) := by
    convert! (Lp.memLp ((U : H1amb Ω) i.succ)).integrable_mul htest.mem_lp using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hsplit :
      (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) *
        (partialD i χ x * φ x + χ x * partialD i φ x)) =
      (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x * φ x) +
        ∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * χ x * partialD i φ x := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hout :
      (∫ x in Ω, (((U : H1amb Ω) i.succ x : ℝ) * χ x +
        ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x) * φ x) =
      (∫ x in Ω, ((U : H1amb Ω) i.succ x : ℝ) * χ x * φ x) +
        ∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x * φ x := by
    rw [← integral_add hC hA]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hsplit] at hg
  rw [hout]
  linarith

end PartialBalayage.Linear
