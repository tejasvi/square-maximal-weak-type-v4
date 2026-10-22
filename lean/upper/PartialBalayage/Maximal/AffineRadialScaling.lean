/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupKernelPairing

/-!
# Affine scaling of radial Laplacian comparisons

The public affine derivative and change-of-variables identities transfer radial kernel
comparisons and compact-density integrability to every positive scale and every center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set

namespace PartialBalayage

/-- A twice continuously differentiable test stays smooth after an affine dilation. -/
theorem contDiff_comp_add_smul (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContDiff ℝ 2 (fun z ↦ w (x + r • z)) := by
  fun_prop

/-- An invertible affine dilation preserves compact support. -/
theorem hasCompactSupport_comp_add_smul (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun z ↦ w (x + r • z)) := by
  convert hw.comp_homeomorph
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)) using 1
  funext z
  simp

/-- The Laplacian acquires precisely two powers of the affine dilation factor. -/
theorem laplacian_comp_add_smul (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x z : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Laplacian.laplacian (fun v ↦ w (x + r • v)) z =
      r ^ 2 * Laplacian.laplacian w (x + r • z) := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun v ↦ w (x + v)
  have hf : ContDiff ℝ 2 f := hw.comp (contDiff_const.add contDiff_id)
  have hscale := iteratedFDeriv_comp_const_smul r hf
  have htrans := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := w) 2 x
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  change (∑ i, iteratedFDeriv ℝ 2 (fun v ↦ f (r • v)) z
    ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
      (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) = _
  rw [congrArg (fun g ↦ g z) hscale]
  simp only [smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show iteratedFDeriv ℝ 2 f (r • z) =
      iteratedFDeriv ℝ 2 w (x + r • z) from htrans (r • z)]

/-- Exact signed radial change of variables, with the two Laplacian scaling powers visible. -/
theorem integral_scaled_radial_mul_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x : EuclideanSpace ℝ (Fin n)) (φ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
        φ (‖y - x‖ / r) * Laplacian.laplacian w y) =
      r ^ n * (∫ z : EuclideanSpace ℝ (Fin n),
        φ ‖z‖ * Laplacian.laplacian (fun v ↦ w (x + r • v)) z) := by
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ w (x + r • z)
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ φ ‖z‖ * Laplacian.laplacian v z
  have hchange : (∫ y : EuclideanSpace ℝ (Fin n), H (r⁻¹ • (y - x))) =
      r ^ n * ∫ z, H z := by
    calc
      _ = ∫ y, H (r⁻¹ • y) :=
        integral_sub_right_eq_self (fun y ↦ H (r⁻¹ • y)) x
      _ = _ := by
        simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
          Measure.integral_comp_inv_smul_of_nonneg (μ := volume) H hr.le
  calc
    _ = ∫ y : EuclideanSpace ℝ (Fin n), H (r⁻¹ • (y - x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      have hnorm : ‖r⁻¹ • (y - x)‖ = ‖y - x‖ / r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
      simp only [H, v, hnorm, laplacian_comp_add_smul n w hw x]
      rw [smul_inv_smul₀ hr.ne']
      have hxy : x + (y - x) = y := by abel
      rw [hxy]
      ring
    _ = _ := hchange

/-- Compact-density radial integrability transfers to every positive affine scale. -/
theorem integrable_scaled_radial_mul_compact (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun z ↦ φ ‖z‖ * g z))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) : Integrable (fun y ↦ φ (‖y - x‖ / r) * g y) := by
  let v := fun z : EuclideanSpace ℝ (Fin n) ↦ g (x + r • z)
  have hv : Continuous v := by fun_prop
  have hvsupp : HasCompactSupport v := hasCompactSupport_comp_add_smul n g hgsupp x hr
  have hi := ((hφ v hv hvsupp).comp_smul (inv_ne_zero hr.ne')).comp_add_left (-x)
  convert hi using 1
  funext y
  have hy : -x + y = y - x := by abel
  have hxy : x + (y - x) = y := by abel
  dsimp [v]
  rw [hy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
    inv_mul_eq_div, smul_inv_smul₀ hr.ne', hxy]

/-- A radial Laplacian comparison transfers to every positive affine scale. -/
theorem scaled_radial_laplacian_pairing_nonneg (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ z, 0 ≤ v z) → v 0 = 0 →
        0 ≤ ∫ z, φ ‖z‖ * Laplacian.laplacian v z)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) {r : ℝ} (hr : 0 < r) :
    0 ≤ ∫ y, φ (‖y - x‖ / r) * Laplacian.laplacian w y := by
  have hv : ContDiff ℝ 2 (fun z ↦ w (x + r • z)) := contDiff_comp_add_smul n w hw x r
  have hvsupp := hasCompactSupport_comp_add_smul n w hsupp x hr
  have hbase := hφ _ hv hvsupp (fun z ↦ hwpos _) (by simpa using hx)
  have h := mul_nonneg (pow_nonneg hr.le n) hbase
  rw [← integral_scaled_radial_mul_laplacian n w hw x φ hr] at h
  exact nonneg_of_mul_nonneg_right h (pow_pos hr 2)

end PartialBalayage
