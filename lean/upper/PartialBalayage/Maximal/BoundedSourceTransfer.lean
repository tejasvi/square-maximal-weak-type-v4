/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LaplacianProduct
public import PartialBalayage.Maximal.AffineRadialScaling
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing compact support from an integrable kernel source comparison

Actual smooth ball cutoffs exhaust Euclidean space. Their derivative contributions are
controlled by the inverse radius, so integrability of the kernel permits comparison against
globally bounded smooth functions whose first derivative and Laplacian are also bounded.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open CenteredMaximal.Ball CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage

/-- The fixed cutoff equals one on the unit ball and vanishes outside the ball of radius two. -/
def sourceCutoff (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  smoothBallCutoff n 0 1 1

/-- A positive inverse radius dilates the fixed cutoff. -/
def sourceCutoffScale (n : ℕ) (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sourceCutoff n (s • y)

theorem sourceCutoff_contDiff (n : ℕ) : ContDiff ℝ 2 (sourceCutoff n) :=
  smoothBallCutoff_contDiff n 0 1 1

theorem sourceCutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (sourceCutoff n) :=
  smoothBallCutoff_hasCompactSupport n 0 (by norm_num) (by norm_num)

theorem sourceCutoff_nonneg (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sourceCutoff n y := Real.smoothTransition.nonneg _

theorem sourceCutoff_le_one (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    sourceCutoff n y ≤ 1 := Real.smoothTransition.le_one _

theorem sourceCutoff_zero (n : ℕ) : sourceCutoff n 0 = 1 := by
  exact smoothBallCutoff_one n 0 0 (by norm_num) (by norm_num) (by simp)

theorem sourceCutoffScale_contDiff (n : ℕ) (s : ℝ) :
    ContDiff ℝ 2 (sourceCutoffScale n s) := by
  exact (sourceCutoff_contDiff n).comp (contDiff_const_smul s)

theorem sourceCutoffScale_hasCompactSupport (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (sourceCutoffScale n s) := by
  unfold sourceCutoffScale
  simpa only [zero_add] using
    hasCompactSupport_comp_add_smul n (sourceCutoff n)
      (sourceCutoff_hasCompactSupport n) 0 hs

theorem sourceCutoffScale_zero (n : ℕ) (s : ℝ) : sourceCutoffScale n s 0 = 1 := by
  simp only [sourceCutoffScale, smul_zero, sourceCutoff_zero]

/-- A coordinate first derivative is bounded by the operator norm of the full derivative. -/
theorem norm_partialD_le_fderiv (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
    ‖partialD i w y‖ ≤ ‖fderiv ℝ w y‖ := by
  simpa only [partialD, PiLp.norm_single, norm_one, mul_one] using
    (fderiv ℝ w y).le_opNorm (EuclideanSpace.single i 1)

/-- The cutoff gradient has exactly one inverse-radius factor. -/
theorem sourceCutoffScale_fderiv (n : ℕ) (s : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (sourceCutoffScale n s) y = s • fderiv ℝ (sourceCutoff n) (s • y) :=
  fderiv_comp_smul s

/-- The cutoff Laplacian has exactly two inverse-radius factors. -/
theorem sourceCutoffScale_laplacian (n : ℕ) (s : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (sourceCutoffScale n s) y =
      s ^ 2 * Laplacian.laplacian (sourceCutoff n) (s • y) := by
  unfold sourceCutoffScale
  simpa only [zero_add] using
    laplacian_comp_add_smul n (sourceCutoff n) (sourceCutoff_contDiff n) 0 y s

/-- Genuine derivative bounds for the fixed, compactly supported cutoff. -/
theorem sourceCutoff_derivative_bounds (n : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A) ∧
      (∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B) := by
  obtain ⟨A, hA⟩ := ((sourceCutoff_hasCompactSupport n).fderiv ℝ).exists_bound_of_continuous
    ((sourceCutoff_contDiff n).continuous_fderiv (by norm_num))
  obtain ⟨B, hB⟩ := exists_bound_laplacian n (sourceCutoff n)
    (sourceCutoff_contDiff n) (sourceCutoff_hasCompactSupport n)
  exact ⟨A, B, (norm_nonneg _).trans (hA 0), (norm_nonneg _).trans (hB 0), hA, hB⟩

/-- The product derivative errors decay with one or two powers of the inverse radius. -/
theorem sourceCutoffScale_laplacian_error_le (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    {A B W G s : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hA : ∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A)
    (hB : ∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖Laplacian.laplacian (sourceCutoffScale n s * w) y -
        sourceCutoffScale n s y * Laplacian.laplacian w y‖ ≤
      2 * (n : ℝ) * s * A * G + s ^ 2 * B * W := by
  have hχgrad : ‖fderiv ℝ (sourceCutoffScale n s) y‖ ≤ s * A := by
    rw [sourceCutoffScale_fderiv, norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (hA _) hs
  have hχlap : ‖Laplacian.laplacian (sourceCutoffScale n s) y‖ ≤ s ^ 2 * B := by
    rw [sourceCutoffScale_laplacian, norm_mul, Real.norm_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left (hB _) (sq_nonneg s)
  have hsum : ‖∑ i : Fin n,
      partialD i (sourceCutoffScale n s) y * partialD i w y‖ ≤ (n : ℝ) * (s * A * G) := by
    calc
      _ ≤ ∑ i : Fin n, ‖partialD i (sourceCutoffScale n s) y * partialD i w y‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, s * A * G := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left
          ((norm_partialD_le_fderiv n w i y).trans (hdwbound y)) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right
            ((norm_partialD_le_fderiv n _ i y).trans hχgrad) hG)
      _ = _ := by simp
  rw [Linear.laplacian_mul_C2 (sourceCutoffScale_contDiff n s) hw]
  have hcancel : sourceCutoffScale n s y * Laplacian.laplacian w y +
      2 * (∑ i : Fin n, partialD i (sourceCutoffScale n s) y * partialD i w y) +
      Laplacian.laplacian (sourceCutoffScale n s) y * w y -
      sourceCutoffScale n s y * Laplacian.laplacian w y =
      2 * (∑ i : Fin n, partialD i (sourceCutoffScale n s) y * partialD i w y) +
      Laplacian.laplacian (sourceCutoffScale n s) y * w y := by ring
  rw [hcancel]
  calc
    _ ≤ ‖2 * (∑ i : Fin n, partialD i (sourceCutoffScale n s) y * partialD i w y)‖ +
        ‖Laplacian.laplacian (sourceCutoffScale n s) y * w y‖ := norm_add_le _ _
    _ ≤ 2 * ((n : ℝ) * (s * A * G)) + (s ^ 2 * B) * W := by
      simp only [norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num))
        ((mul_le_mul_of_nonneg_left (hwbound y) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hχlap hW))
    _ = _ := by ring

/-- The cutoff error has a genuine integrable pairing with the kernel. -/
theorem integrable_sourceCutoffScale_laplacian_error (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    {A B W G s : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hA : ∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A)
    (hB : ∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G) :
    Integrable (fun y ↦ K y * (Laplacian.laplacian (sourceCutoffScale n s * w) y -
      sourceCutoffScale n s y * Laplacian.laplacian w y)) := by
  have hc : Continuous (fun y ↦ Laplacian.laplacian (sourceCutoffScale n s * w) y -
      sourceCutoffScale n s y * Laplacian.laplacian w y) :=
    (continuous_laplacian n _ ((sourceCutoffScale_contDiff n s).mul hw)).sub
      ((sourceCutoffScale_contDiff n s).continuous.mul (continuous_laplacian n w hw))
  exact hK.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun y ↦
    sourceCutoffScale_laplacian_error_le n w hw hs hW hG hA hB hwbound hdwbound y)

/-- The integrated cutoff error is controlled by the actual L¹ norm of the kernel. -/
theorem integral_sourceCutoffScale_laplacian_error_le (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    {A B W G s : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hA : ∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A)
    (hB : ∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G) :
    ‖∫ y, K y * (Laplacian.laplacian (sourceCutoffScale n s * w) y -
      sourceCutoffScale n s y * Laplacian.laplacian w y)‖ ≤
      (∫ y, ‖K y‖) * (2 * (n : ℝ) * s * A * G + s ^ 2 * B * W) := by
  calc
    _ ≤ ∫ y, ‖K y‖ * (2 * (n : ℝ) * s * A * G + s ^ 2 * B * W) := by
      apply norm_integral_le_of_norm_le (hK.norm.mul_const _)
      exact Eventually.of_forall fun y ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (sourceCutoffScale_laplacian_error_le n w hw hs hW hG hA hB hwbound hdwbound y)
          (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Uniform domination for the cutoff Laplacians, independent of the exhausting radius. -/
theorem sourceCutoffScale_laplacian_norm_le (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    {A B W G D s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hA : ∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A)
    (hB : ∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G)
    (hΔwbound : ∀ y, ‖Laplacian.laplacian w y‖ ≤ D)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖Laplacian.laplacian (sourceCutoffScale n s * w) y‖ ≤
      D + 2 * (n : ℝ) * A * G + B * W := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hχ : ‖sourceCutoffScale n s y‖ ≤ 1 := by
    unfold sourceCutoffScale
    rw [Real.norm_of_nonneg (sourceCutoff_nonneg n _)]
    exact sourceCutoff_le_one n _
  have hmain : ‖sourceCutoffScale n s y * Laplacian.laplacian w y‖ ≤ D := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
      (by simpa using hΔwbound y)
  have he := sourceCutoffScale_laplacian_error_le n w hw hs hW hG hA hB
    hwbound hdwbound y
  have htriangle : ‖Laplacian.laplacian (sourceCutoffScale n s * w) y‖ ≤
      ‖sourceCutoffScale n s y * Laplacian.laplacian w y‖ +
      ‖Laplacian.laplacian (sourceCutoffScale n s * w) y -
        sourceCutoffScale n s y * Laplacian.laplacian w y‖ := by
    calc
      _ = ‖sourceCutoffScale n s y * Laplacian.laplacian w y +
          (Laplacian.laplacian (sourceCutoffScale n s * w) y -
            sourceCutoffScale n s y * Laplacian.laplacian w y)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  calc
    _ ≤ D + (2 * (n : ℝ) * s * A * G + s ^ 2 * B * W) :=
      htriangle.trans (add_le_add hmain he)
    _ ≤ _ := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      have hfirst : 2 * (n : ℝ) * s * A * G ≤ 2 * (n : ℝ) * A * G := by
        convert mul_le_mul_of_nonneg_right hs1
          (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) hA0) hG) using 1 <;>
          ring
      have hsecond : s ^ 2 * B * W ≤ B * W := by
        convert mul_le_mul_of_nonneg_right hs2 (mul_nonneg hB0 hW) using 1 <;> ring
      linarith

/-- The inverse radii used in the actual cutoff exhaustion. -/
def sourceInverseRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem sourceInverseRadius_pos (k : ℕ) : 0 < sourceInverseRadius k := by
  unfold sourceInverseRadius
  positivity

theorem sourceInverseRadius_le_one (k : ℕ) : sourceInverseRadius k ≤ 1 := by
  unfold sourceInverseRadius
  apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem tendsto_sourceInverseRadius : Tendsto sourceInverseRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The actual cutoff products recover the untruncated Laplacian pointwise. -/
theorem tendsto_sourceCutoff_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    {A B W G : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hA : ∀ y, ‖fderiv ℝ (sourceCutoff n) y‖ ≤ A)
    (hB : ∀ y, ‖Laplacian.laplacian (sourceCutoff n) y‖ ≤ B)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G)
    (y : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k ↦ Laplacian.laplacian (sourceCutoffScale n (sourceInverseRadius k) * w) y)
      atTop (𝓝 (Laplacian.laplacian w y)) := by
  have harg : Tendsto (fun k ↦ sourceInverseRadius k • y) atTop (𝓝 0) := by
    simpa only [zero_smul] using tendsto_sourceInverseRadius.smul_const y
  have hχ : Tendsto (fun k ↦ sourceCutoffScale n (sourceInverseRadius k) y)
      atTop (𝓝 1) := by
    simpa only [sourceCutoffScale, sourceCutoff_zero, Function.comp_def] using
      (sourceCutoff_contDiff n).continuous.continuousAt.tendsto.comp harg
  have herr : Tendsto (fun k ↦
      Laplacian.laplacian (sourceCutoffScale n (sourceInverseRadius k) * w) y -
        sourceCutoffScale n (sourceInverseRadius k) y * Laplacian.laplacian w y)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k ↦ sourceCutoffScale_laplacian_error_le n w hw
      (sourceInverseRadius_pos k).le hW hG hA hB hwbound hdwbound y)
    have hlinear := tendsto_sourceInverseRadius.const_mul (2 * (n : ℝ))
    have hfirst := (hlinear.mul_const A).mul_const G
    have hsecond := ((tendsto_sourceInverseRadius.pow 2).mul_const B).mul_const W
    convert hfirst.add hsecond using 1
    norm_num
  have htotal := (hχ.mul_const (Laplacian.laplacian w y)).add herr
  convert htotal using 1
  · funext k
    ring
  · simp

/-- A bounded Laplacian has a genuine integrable pairing with an integrable kernel. -/
theorem integrable_kernel_mul_laplacian_of_bounded (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w) {D : ℝ}
    (hΔwbound : ∀ y, ‖Laplacian.laplacian w y‖ ≤ D) :
    Integrable (fun y ↦ K y * Laplacian.laplacian w y) :=
  hK.mul_bdd (continuous_laplacian n w hw).aestronglyMeasurable
    (Eventually.of_forall hΔwbound)

/-- Compact-test source bounds extend to bounded C² tests for an actual integrable kernel. -/
theorem integrable_kernel_source_bound_of_bounded_C2 (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hwpos : ∀ y, 0 ≤ w y) {W G D : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G)
    (hΔwbound : ∀ y, ‖Laplacian.laplacian w y‖ ≤ D) :
    -(C * w 0) ≤ ∫ y, K y * Laplacian.laplacian w y := by
  obtain ⟨A, B, _, _, hA, hB⟩ := sourceCutoff_derivative_bounds n
  let v := fun k ↦ sourceCutoffScale n (sourceInverseRadius k) * w
  have hv : ∀ k, ContDiff ℝ 2 (v k) := fun k ↦
    (sourceCutoffScale_contDiff n (sourceInverseRadius k)).mul hw
  have hbound : ∀ k y, ‖Laplacian.laplacian (v k) y‖ ≤
      D + 2 * (n : ℝ) * A * G + B * W := fun k y ↦
    sourceCutoffScale_laplacian_norm_le n w hw (sourceInverseRadius_pos k).le
      (sourceInverseRadius_le_one k) hW hG hA hB hwbound hdwbound hΔwbound y
  have hlim : Tendsto (fun k ↦ ∫ y, K y * Laplacian.laplacian (v k) y)
      atTop (𝓝 (∫ y, K y * Laplacian.laplacian w y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y ↦ ‖K y‖ * (D + 2 * (n : ℝ) * A * G + B * W))
    · intro k
      exact hK.aestronglyMeasurable.mul
        (continuous_laplacian n (v k) (hv k)).aestronglyMeasurable
    · exact hK.norm.mul_const _
    · intro k
      exact Eventually.of_forall fun y ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound k y) (norm_nonneg _)
    · exact Eventually.of_forall fun y ↦ tendsto_const_nhds.mul
        (tendsto_sourceCutoff_laplacian n w hw hW hG hA hB hwbound hdwbound y)
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun k ↦ by
    have hsupp : HasCompactSupport (v k) :=
      (sourceCutoffScale_hasCompactSupport n (sourceInverseRadius_pos k)).mul_right
    have hpos : ∀ y, 0 ≤ v k y := fun y ↦
      mul_nonneg (sourceCutoff_nonneg n _) (hwpos y)
    simpa only [v, Pi.mul_apply, sourceCutoffScale_zero, one_mul] using
      hsource (v k) (hv k) hsupp hpos

/-- The bounded-test comparison holds at every translated center. -/
theorem integrable_kernel_source_bound_of_bounded_C2_at (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hwpos : ∀ y, 0 ≤ w y) {W G D : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hwbound : ∀ y, ‖w y‖ ≤ W) (hdwbound : ∀ y, ‖fderiv ℝ w y‖ ≤ G)
    (hΔwbound : ∀ y, ‖Laplacian.laplacian w y‖ ≤ D)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(C * w x) ≤ ∫ y, K (y - x) * Laplacian.laplacian w y := by
  let v := fun z ↦ w (x + z)
  have hv : ContDiff ℝ 2 v := hw.comp (contDiff_const.add contDiff_id)
  have hΔv : ∀ z, Laplacian.laplacian v z = Laplacian.laplacian w (x + z) := by
    intro z
    simpa only [v, one_smul, one_pow, one_mul] using
      laplacian_comp_add_smul n w hw x z 1
  have hdvbound : ∀ z, ‖fderiv ℝ v z‖ ≤ G := by
    intro z
    simpa only [v, fderiv_comp_add_left] using hdwbound (x + z)
  have h := integrable_kernel_source_bound_of_bounded_C2 n K hK C hsource v hv
    (fun z ↦ hwpos _) hW hG (fun z ↦ hwbound _) hdvbound
    (fun z ↦ by rw [hΔv]; exact hΔwbound _)
  have hchange : (∫ y, K (y - x) * Laplacian.laplacian w y) =
      ∫ z, K z * Laplacian.laplacian v z := by
    calc
      _ = ∫ y, (fun z ↦ K z * Laplacian.laplacian w (x + z)) (y - x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y ↦ by
          change K (y - x) * Laplacian.laplacian w y =
            K (y - x) * Laplacian.laplacian w (x + (y - x))
          have hxy : x + (y - x) = y := by abel
          rw [hxy]
      _ = ∫ z, K z * Laplacian.laplacian w (x + z) := by
        exact integral_sub_right_eq_self (μ := volume)
          (fun z : EuclideanSpace ℝ (Fin n) ↦ K z * Laplacian.laplacian w (x + z)) x
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z ↦ by
          change K z * Laplacian.laplacian w (x + z) = K z * Laplacian.laplacian v z
          rw [hΔv]
  simpa only [hchange, v, add_zero] using h

end PartialBalayage
