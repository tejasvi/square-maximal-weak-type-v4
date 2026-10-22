/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalCutoffEquation

/-!
# The actual interior cutoff Laplace equation

The weak Dirichlet equation implies the genuine weak Laplace equation for multiplication of
the state by a compactly supported interior cutoff. Every first-order term is taken from the
actual `H01` graph. The result does not assume second-order regularity or zero boundary values
for its gradients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Coordinate differentiation preserves genuine smoothness. -/
theorem contDiff_partialD_smooth {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD i φ) :=
  (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- All pairings used in localization are genuine integrals of an `L²` function and a test. -/
theorem integrable_L2_mul_cutoff_smooth (a : L2D Ω)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Integrable (fun x ↦ (a x : ℝ) * χ x * φ x) (volume.restrict Ω) := by
  convert! (Lp.memLp a).integrable_mul (isTestFn_mul_smooth hχ hφ).mem_lp using 1
  funext x
  simp only [Pi.mul_apply]
  ring

/-- Localization of the actual weak Laplace equation. The right side is the represented
cutoff forcing `-χ g + 2 ∑ i, (∂ᵢ χ) Uᵢ + U₀ Δχ`, paired with an arbitrary smooth test. -/
theorem weak_laplacian_cutoff_product (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * χ x * Laplacian.laplacian φ x) =
      -(∫ x in Ω, (g x : ℝ) * χ x * φ x) +
        2 * (∑ i : Fin d, ∫ x in Ω,
          ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x) +
        ∑ i : Fin d, ∫ x in Ω,
          ((U : H1amb Ω) 0 x : ℝ) * partialD i (partialD i χ) x * φ x := by
  let A (i : Fin d) : ℝ := ∫ x in Ω,
    ((U : H1amb Ω) 0 x : ℝ) * χ x * partialD i (partialD i φ) x
  let B (i : Fin d) : ℝ := ∫ x in Ω,
    ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x
  let C (i : Fin d) : ℝ := ∫ x in Ω,
    ((U : H1amb Ω) 0 x : ℝ) * partialD i χ x * partialD i φ x
  let D (i : Fin d) : ℝ := ∫ x in Ω,
    ((U : H1amb Ω) 0 x : ℝ) * partialD i (partialD i χ) x * φ x
  let Q (i : Fin d) : ℝ := ∫ x in Ω,
    ((U : H1amb Ω) i.succ x : ℝ) * χ x * partialD i φ x
  have hA (i : Fin d) : A i = -(Q i + C i) := by
    have h := weak_gradient_cutoff_product U hχ (contDiff_partialD_smooth hφ i) i
    have hQ := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) i.succ)
      hχ (contDiff_partialD_smooth hφ i)
    have hC := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) 0)
      (hχ.partialD i) (contDiff_partialD_smooth hφ i)
    change A i = -(Q i + C i)
    rw [← integral_add hQ hC]
    convert! h using 1
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hC (i : Fin d) : C i = -(B i + D i) := by
    have h := weak_gradient_cutoff_product U (hχ.partialD i) hφ i
    have hB := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) i.succ)
      (hχ.partialD i) hφ
    have hD := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) 0)
      ((hχ.partialD i).partialD i) hφ
    change C i = -(B i + D i)
    rw [← integral_add hB hD]
    convert! h using 1
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  let htest := isTestFn_mul_smooth hχ hφ
  have hpair (i : Fin d) :
      ⟪(U : H1amb Ω) i.succ, htest.partialCls i⟫ = B i + Q i := by
    rw [L2.inner_def]
    have hB := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) i.succ)
      (hχ.partialD i) hφ
    have hQ := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) i.succ)
      hχ (contDiff_partialD_smooth hφ i)
    change _ = (∫ x in Ω,
      ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x) +
      ∫ x in Ω, ((U : H1amb Ω) i.succ x : ℝ) * χ x * partialD i φ x
    rw [← integral_add hB hQ]
    apply integral_congr_ae
    filter_upwards [htest.memLp_partialD i |>.coeFn_toLp] with x hx
    simp only [Real.inner_apply, IsTestFn.partialCls, hx,
      partialD_mul_smooth hχ.1 hφ]
    ring
  have hpde := weak_equation_testFn U g heq htest
  simp_rw [hpair] at hpde
  simp only [Finset.sum_add_distrib] at hpde
  have hpde' : (∑ i : Fin d, B i) + (∑ i : Fin d, Q i) =
      ∫ x in Ω, (g x : ℝ) * χ x * φ x := by
    convert! hpde using 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hsumA : (∑ i : Fin d, A i) =
      -((∑ i : Fin d, Q i) + ∑ i : Fin d, C i) := by
    simp_rw [hA]
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hsumC : (∑ i : Fin d, C i) =
      -((∑ i : Fin d, B i) + ∑ i : Fin d, D i) := by
    simp_rw [hC]
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hsum : (∫ x in Ω,
      ((U : H1amb Ω) 0 x : ℝ) * χ x * Laplacian.laplacian φ x) =
      ∑ i : Fin d, A i := by
    calc
      _ = ∫ x in Ω, ∑ i : Fin d,
          ((U : H1amb Ω) 0 x : ℝ) * χ x * partialD i (partialD i φ) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [laplacian_eq_sum_partialD φ hφ2]
        simp only [Finset.mul_sum]
      _ = _ := by
        rw [integral_finsetSum]
        exact fun i _ ↦ integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) 0) hχ
          (contDiff_partialD_smooth (contDiff_partialD_smooth hφ i) i)
  change _ = -(∫ x in Ω, (g x : ℝ) * χ x * φ x) +
    2 * (∑ i : Fin d, B i) + ∑ i : Fin d, D i
  rw [hsum]
  linarith

end PartialBalayage.Linear
