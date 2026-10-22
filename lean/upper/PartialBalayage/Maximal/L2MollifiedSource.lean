/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.BoundedSourceTransfer
public import PartialBalayage.Linear.MollifierL2Convergence
public import CenteredMaximal.Ball.LocalMollifierDistribution

/-!
# Actual positive mollification of L² distributional Laplace equations

A smooth compact kernel gives genuine globally bounded classical derivatives when convolved
with an L² function. Positive convolution preserves nonnegativity, and the weak equation
identifies its classical Laplacian with the convolution of the actual forcing.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Set Filter Topology
open CenteredMaximal.Ball CenteredMaximal.Ball.DirichletSobolev
open scoped Convolution ENNReal

namespace PartialBalayage

variable {n : ℕ}

/-- Hölder's inequality gives a global genuine bound for convolution of two L² inputs. -/
theorem exists_bound_convolution_of_memLp_two
    {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : A →L[ℝ] B →L[ℝ] F) {φ : EuclideanSpace ℝ (Fin n) → A}
    {u : EuclideanSpace ℝ (Fin n) → B} (hφ : MemLp φ 2 volume) (hu : MemLp u 2 volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(φ ⋆[L, volume] u) x‖ ≤ C := by
  let C := ‖L‖ₑ * eLpNorm φ 2 volume * eLpNorm u 2 volume
  have hC : C ≠ ∞ := by dsimp [C]; finiteness
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun x ↦ ?_⟩
  simpa only [toReal_enorm] using ENNReal.toReal_mono hC
    (enorm_convolution_le L (p := 2) (q := 2) hφ.aestronglyMeasurable
      hu.aestronglyMeasurable x)

/-- Coordinate differentiation of an actual convolution only needs local integrability. -/
theorem partialD_convolution_left_of_locallyIntegrable
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LocallyIntegrable u)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    partialD i (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ((partialD i φ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have hd := hφsupp.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [partialD, hd.fderiv]
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hci := (hφsupp.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin n))) hfc hu x
  simp only [convolution_def] at hci ⊢
  rw [ContinuousLinearMap.integral_apply hci]
  rfl

/-- The classical Laplacian passes through a compact smooth kernel without global L¹ input. -/
theorem laplacian_convolution_left_of_locallyIntegrable
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LocallyIntegrable u)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ((Laplacian.laplacian φ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have htest : IsTestFn (univ : Set (EuclideanSpace ℝ (Fin n))) φ :=
    ⟨hφ, hφsupp, subset_univ _⟩
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hconv : ContDiff ℝ 2 (φ ⋆[lsmul ℝ ℝ, volume] u) :=
    (hφsupp.contDiff_convolution_left (lsmul ℝ ℝ) hφ hu).of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hp (i : Fin n) : partialD i (φ ⋆[lsmul ℝ ℝ, volume] u) =
      (partialD i φ) ⋆[lsmul ℝ ℝ, volume] u :=
    funext (partialD_convolution_left_of_locallyIntegrable u φ hu hφsupp hφ i)
  have hsum : Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ∑ i : Fin n, ((partialD i (partialD i φ)) ⋆[lsmul ℝ ℝ, volume] u) x := by
    rw [laplacian_eq_sum_partialD _ hconv x]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp i]
    exact partialD_convolution_left_of_locallyIntegrable u (partialD i φ) hu
      (htest.partialD i).2.1 (htest.partialD i).1 i x
  rw [hsum]
  have hint (i : Fin n) : Integrable
      (fun t ↦ partialD i (partialD i φ) t * u (x - t)) volume := by
    have htest2 := (htest.partialD i).partialD i
    have h := htest2.2.1.convolutionExists_left (lsmul ℝ ℝ) htest2.1.continuous hu x
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using h
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum (s := Finset.univ) (fun i _ ↦ hint i)]
  congr 1
  funext t
  rw [laplacian_eq_sum_partialD φ hφtwo t]
  simp only [Finset.sum_mul]

/-- Actual smooth mollification of an L² input has bounded value, derivative, and Laplacian. -/
theorem mollification_has_bounded_classical_derivatives
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u 2 volume)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ W G D : ℝ, 0 ≤ W ∧ 0 ≤ G ∧ 0 ≤ D ∧
      (∀ x, ‖(φ ⋆[lsmul ℝ ℝ, volume] u) x‖ ≤ W) ∧
      (∀ x, ‖fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x‖ ≤ G) ∧
      (∀ x, ‖Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x‖ ≤ D) := by
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨W, hW, hwbound⟩ := exists_bound_convolution_of_memLp_two (lsmul ℝ ℝ)
    (hφ.continuous.memLp_of_hasCompactSupport hφsupp) hu
  obtain ⟨G, hG, hdwbound⟩ := exists_bound_convolution_of_memLp_two
    ((lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin n)))
    ((hφtwo.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hφsupp.fderiv ℝ)) hu
  obtain ⟨D, hD, hΔwbound⟩ := exists_bound_convolution_of_memLp_two (lsmul ℝ ℝ)
    ((continuous_laplacian n φ hφtwo).memLp_of_hasCompactSupport
      (hasCompactSupport_laplacian n φ hφsupp)) hu
  refine ⟨W, G, D, hW, hG, hD, hwbound, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hd := hφsupp.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
      (hφ.of_le (by simp)) (hu.locallyIntegrable (by norm_num)) x
    rw [hd.fderiv]
    exact hdwbound x
  · rw [laplacian_convolution_left_of_locallyIntegrable u φ
      (hu.locallyIntegrable (by norm_num)) hφsupp hφ]
    exact hΔwbound x

/-- Positive compact kernels preserve the actual almost everywhere positivity of an input. -/
theorem mollification_nonneg_of_ae_nonneg
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hφ0 : ∀ y, 0 ≤ φ y)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ (φ ⋆[lsmul ℝ ℝ, volume] u) x := by
  apply integral_nonneg_of_ae
  have hmap := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.tendsto_ae
  have hpos := hmap.eventually hu0
  filter_upwards [hpos] with y hy
  exact mul_nonneg (hφ0 y) hy

/-- The genuine distributional equation becomes the exact pointwise mollified equation. -/
theorem laplacian_mollification_eq_of_L2_distribution
    (u g φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u 2 volume)
    (hΔ : HasLocalDistributionalLaplacian n univ u g)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
  have htestsupp : HasCompactSupport (fun y ↦ φ (x - y)) := by
    simpa [Function.comp_def, Homeomorph.subLeft, Equiv.subLeft] using
      (hφsupp.comp_homeomorph (Homeomorph.subLeft x))
  have htestsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ (x - y)) := by fun_prop
  have hdist := hΔ (fun y ↦ φ (x - y)) htestsupp htestsmooth (subset_univ _)
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  calc
    _ = ((Laplacian.laplacian φ) ⋆[lsmul ℝ ℝ, volume] u) x :=
      laplacian_convolution_left_of_locallyIntegrable u φ
        (hu.locallyIntegrable (by norm_num)) hφsupp hφ x
    _ = ∫ y, u y * Laplacian.laplacian (fun z ↦ φ (x - z)) y := by
      rw [convolution_lsmul_swap]
      apply integral_congr_ae
      filter_upwards with y
      rw [laplacian_comp_const_sub φ hφtwo x y]
      simp [smul_eq_mul, mul_comm]
    _ = ∫ y, φ (x - y) * g y := hdist.symm
    _ = _ := by
      rw [convolution_lsmul_swap]
      simp only [smul_eq_mul]

/-- The actual L² forcing mollification has an integrable pairing with every L¹ kernel. -/
theorem integrable_kernel_mul_L2_mollification
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (g φ : EuclideanSpace ℝ (Fin n) → ℝ) (hg : MemLp g 2 volume)
    (hφsupp : HasCompactSupport φ) (hφ : Continuous φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ K (y - x) * (φ ⋆[lsmul ℝ ℝ, volume] g) y) := by
  obtain ⟨D, _, hD⟩ := exists_bound_convolution_of_memLp_two (lsmul ℝ ℝ)
    (hφ.memLp_of_hasCompactSupport hφsupp) hg
  have hKx : Integrable (fun y ↦ K (y - x)) := by
    convert hK.comp_add_left (-x) using 1
    funext y
    congr 1
    abel
  exact hKx.mul_bdd
    (hφsupp.continuous_convolution_left (lsmul ℝ ℝ) hφ
      (hg.locallyIntegrable (by norm_num))).aestronglyMeasurable
    (Eventually.of_forall hD)

/-- Compact source comparisons apply to the actual positive L² mollifications at every center. -/
theorem integrable_kernel_source_bound_of_L2_mollification
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (u g φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u 2 volume)
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (x : EuclideanSpace ℝ (Fin n)) :
    -(C * (φ ⋆[lsmul ℝ ℝ, volume] u) x) ≤
      ∫ y, K (y - x) * (φ ⋆[lsmul ℝ ℝ, volume] g) y := by
  obtain ⟨W, G, D, hW, hG, _, hwbound, hdwbound, hΔwbound⟩ :=
    mollification_has_bounded_classical_derivatives u φ hu hφsupp hφ
  have hw : ContDiff ℝ 2 (φ ⋆[lsmul ℝ ℝ, volume] u) :=
    (hφsupp.contDiff_convolution_left (lsmul ℝ ℝ) hφ
      (hu.locallyIntegrable (by norm_num))).of_le (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have h := integrable_kernel_source_bound_of_bounded_C2_at n K hK C hsource _ hw
    (mollification_nonneg_of_ae_nonneg u φ hu0 hφ0) hW hG hwbound hdwbound hΔwbound x
  have hΔeq : (∫ y, K (y - x) * Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) y) =
      ∫ y, K (y - x) * (φ ⋆[lsmul ℝ ℝ, volume] g) y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [laplacian_mollification_eq_of_L2_distribution u g φ hu hΔ hφsupp hφ y]
  rwa [hΔeq] at h

/-- Every explicit positive graph mollifier satisfies the genuine kernel source comparison. -/
theorem graphMollifier_kernel_source_bound (k : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(C * ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x) ≤
      ∫ y, K (y - x) *
        ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] g) y :=
  integrable_kernel_source_bound_of_L2_mollification K hK C hsource u g _ (Lp.memLp u)
    hu0 hΔ (Linear.graphMollifierBump n k).hasCompactSupport_normed
    (Linear.graphMollifierBump n k).contDiff_normed
    (Linear.graphMollifierBump n k).nonneg_normed x

/-- The explicit mollified forcing pairings are genuine integrals at every center. -/
theorem integrable_kernel_mul_graphMollifier (k : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ K (y - x) *
      ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] g) y) :=
  integrable_kernel_mul_L2_mollification K hK g _ (Lp.memLp g)
    (Linear.graphMollifierBump n k).hasCompactSupport_normed
    ((Linear.graphMollifierBump n k).contDiff_normed (n := (⊤ : ℕ∞))).continuous x

end PartialBalayage
