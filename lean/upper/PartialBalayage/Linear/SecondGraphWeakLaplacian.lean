/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CompactSobolevDensity
public import PartialBalayage.Linear.SecondSobolevZeroSet
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The weak Laplacian represented by actual second Sobolev graphs

Two genuine weak gradient identities identify the sum of the represented diagonal second
derivatives with the forcing in an actual weak Laplace equation. This supplies the equation
bridge after local elliptic regularity has constructed the second graphs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace ENNReal Laplacian

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- Twice applying the actual graph constraints gives the represented second derivative. -/
theorem integral_secondGraphLaplacian_mul_test
    (U : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))))
    (G : Fin d → H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))))
    (hG : IsSecondGradientGraph U G)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Set.univ φ) :
    (∫ x, (U.val 0 x : ℝ) * Δ φ x) =
      ∫ x, secondGraphLaplacian G x * φ x := by
  have hg (i : Fin d) :
      (∫ x, (U.val 0 x : ℝ) * partialD i (partialD i φ) x) =
      ∫ x, ((G i).val i.succ x : ℝ) * φ x := by
    rw [weak_gradient_integral_of_mem_W12_univ
      ((H01_le_W12 Set.univ) U.property) (hφ.partialD i) i]
    have hae : ((G i).val 0) =ᵐ[volume]
        (U.val i.succ) := by
      simpa only [Filter.EventuallyEq, Measure.restrict_univ] using hG i
    rw [← integral_congr_ae (hae.fun_mul
      (Filter.EventuallyEq.refl (ae volume) (partialD i φ)))]
    rw [weak_gradient_integral_of_mem_W12_univ
      ((H01_le_W12 Set.univ) (G i).property) hφ i, neg_neg]
  have hA (i : Fin d) : Integrable
      (fun x ↦ (U.val 0 x : ℝ) * partialD i (partialD i φ) x) volume := by
    have hu : MemLp (U.val 0) 2 volume := by
      simpa only [Measure.restrict_univ] using Lp.memLp (U.val 0)
    have hp : MemLp (partialD i (partialD i φ)) 2 volume := by
      simpa only [Measure.restrict_univ] using ((hφ.partialD i).partialD i).mem_lp
    exact hu.integrable_mul hp
  have hB (i : Fin d) : Integrable
      (fun x ↦ ((G i).val i.succ x : ℝ) * φ x) volume := by
    have hu : MemLp ((G i).val i.succ) 2 volume := by
      simpa only [Measure.restrict_univ] using Lp.memLp ((G i).val i.succ)
    have hp : MemLp φ 2 volume := by
      simpa only [Measure.restrict_univ] using hφ.mem_lp
    exact hu.integrable_mul hp
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp_rw [laplacian_eq_sum_partialD φ hφ2, Finset.mul_sum,
    secondGraphLaplacian, Finset.sum_mul]
  rw [integral_finsetSum (s := Finset.univ) (fun i _ ↦ hA i),
    integral_finsetSum (s := Finset.univ) (fun i _ ↦ hB i)]
  exact Finset.sum_congr rfl (fun i _ ↦ hg i)

/-- Uniqueness of actual locally integrable distributions identifies the forcing pointwise. -/
theorem ae_secondGraphLaplacian_eq_of_weak_laplacian
    (U : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))))
    (G : Fin d → H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))))
    (hG : IsSecondGradientGraph U G)
    {q : EuclideanSpace ℝ (Fin d) → ℝ} (hq : MemLp q 2 volume)
    (heq : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ →
      (∫ x, (U.val 0 x : ℝ) * Δ φ x) = ∫ x, q x * φ x) :
    secondGraphLaplacian G =ᵐ[volume] q := by
  have hsum : MemLp (secondGraphLaplacian G) 2 volume := by
    unfold secondGraphLaplacian
    apply memLp_finsetSum
    intro i _
    simpa only [Measure.restrict_univ] using Lp.memLp ((G i).val i.succ)
  apply ae_eq_of_integral_contDiff_smul_eq (hsum.locallyIntegrable (by norm_num))
    (hq.locallyIntegrable (by norm_num))
  intro φ hφ hφs
  have ht : IsTestFn Set.univ φ := ⟨hφ, hφs, subset_univ _⟩
  have h := (integral_secondGraphLaplacian_mul_test U G hG ht).symm.trans (heq φ ht)
  simpa only [smul_eq_mul, mul_comm] using h

end PartialBalayage.Linear
