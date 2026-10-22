/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalCutoffEquation

/-!
# The classical Laplacian product formula under C² regularity

The formula needs only two continuous derivatives. It applies to the nonnegative compact
cutoffs used to transfer radial distributional inequalities to bounded smooth functions.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d : ℕ}

theorem partialD_mul_C1 {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hφ : ContDiff ℝ 1 φ)
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (χ * φ) x = partialD i χ x * φ x + χ x * partialD i φ x := by
  rw [partialD, fderiv_mul (hχ.differentiable (by norm_num) x)
    (hφ.differentiable (by norm_num) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, partialD]
  ring

theorem partialD_twice_mul_C2 {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hφ : ContDiff ℝ 2 φ)
    (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (partialD i (χ * φ)) x =
      partialD i (partialD i χ) x * φ x +
        partialD i χ x * partialD i φ x + partialD i χ x * partialD i φ x +
        χ x * partialD i (partialD i φ) x := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hχi : ContDiff ℝ 1 (partialD i χ) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφi : ContDiff ℝ 1 (partialD i φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hprod : partialD i (χ * φ) = (partialD i χ) * φ + χ * (partialD i φ) :=
    funext (partialD_mul_C1 hχ1 hφ1 i)
  have hA : ContDiff ℝ 1 ((partialD i χ) * φ) := by
    simpa only [Pi.mul_def] using hχi.mul hφ1
  have hB : ContDiff ℝ 1 (χ * (partialD i φ)) := by
    simpa only [Pi.mul_def] using hχ1.mul hφi
  rw [hprod, partialD_add (hA.differentiable (by norm_num))
    (hB.differentiable (by norm_num)) i]
  simp only [Pi.add_apply]
  rw [partialD_mul_C1 hχi hφ1 i x, partialD_mul_C1 hχ1 hφi i x]
  ring

/-- The actual Laplacian product formula for two C² scalar functions. -/
theorem laplacian_mul_C2 {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hφ : ContDiff ℝ 2 φ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian (χ * φ) x = χ x * Laplacian.laplacian φ x +
      2 * (∑ i : Fin d, partialD i χ x * partialD i φ x) +
      Laplacian.laplacian χ x * φ x := by
  rw [laplacian_eq_sum_partialD (χ * φ) (hχ.mul hφ),
    laplacian_eq_sum_partialD χ hχ, laplacian_eq_sum_partialD φ hφ]
  simp_rw [partialD_twice_mul_C2 hχ hφ]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end PartialBalayage.Linear
