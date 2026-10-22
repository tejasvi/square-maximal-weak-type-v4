/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallFlux
public import CenteredMaximal.Ball.RadialMassDerivative
public import CenteredMaximal.Ball.PolarSwap

/-!
# Spherical geometry for radial kernel pairings

These definitions keep the actual Euclidean test function visible while arranging the ball
and sphere identities for one-dimensional integration by parts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace PartialBalayage

/-- The unnormalized spherical mean about a specified center. -/
def radialSphereMean (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    w (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)

/-- The radial derivative of the spherical mean. -/
def radialSphereDerivative (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    fderiv ℝ w (x + r • (ω : EuclideanSpace ℝ (Fin n)))
      (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)

/-- The Laplacian mass inside the sphere of radius `r`. -/
def radialBallLaplacian (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ∫ y in ball x r, Laplacian.laplacian w y

/-- The spherical Laplacian mean multiplied by the polar Jacobian. -/
def radialLaplacianDensity (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  r ^ (n - 1) * radialSphereMean n (Laplacian.laplacian w) x r

/-- Differentiating the spherical mean gives the sphere's radial derivative integral. -/
theorem hasDerivAt_radialSphereMean (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt (radialSphereMean n w x) (radialSphereDerivative n w x r) r :=
  CenteredMaximal.Ball.hasDerivAt_sphereIntegral_of_hasCompactSupport n w hw hsupp x r

/-- Differentiating the ball's Laplacian mass gives its radial density. -/
theorem hasDerivAt_radialBallLaplacian (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (radialBallLaplacian n w x) (radialLaplacianDensity n w x r) r :=
  CenteredMaximal.Ball.hasDerivAt_integral_ball_radius n x (Laplacian.laplacian w)
    (CenteredMaximal.Ball.continuous_laplacian n w hw)
    (CenteredMaximal.Ball.hasCompactSupport_laplacian n w hsupp) hr

/-- The divergence theorem identifies the ball mass with spherical radial flux. -/
theorem radialBallLaplacian_eq_flux (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) :
    radialBallLaplacian n w x r = r ^ (n - 1) * radialSphereDerivative n w x r :=
  CenteredMaximal.Ball.integral_laplacian_ball_eq_sphere_flux n w hw hsupp x hr

/-- Continuous test functions have continuous spherical means. -/
theorem continuous_radialSphereMean (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) : Continuous (radialSphereMean n w x) :=
  CenteredMaximal.Ball.continuous_sphereIntegral n w hw x

/-- Spherical means preserve nonnegativity. -/
theorem radialSphereMean_nonneg (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    0 ≤ radialSphereMean n w x r :=
  integral_nonneg (fun _ ↦ hw _)

/-- The spherical mean tends to zero at a zero of the continuous test function. -/
theorem tendsto_radialSphereMean_zero (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    Tendsto (radialSphereMean n w x) (𝓝[>] 0) (𝓝 0) :=
  (CenteredMaximal.Ball.tendsto_sphereIntegral_zero n w hw x hx).mono_left
    nhdsWithin_le_nhds

/-- All relevant sphere terms vanish beyond one radius for a compactly supported test function. -/
theorem exists_radialPairing_support_radius (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n)) {b : ℝ}
    (hb : 0 < b) :
    ∃ R : ℝ, b < R ∧ ∀ r, R ≤ r →
      radialSphereMean n w x r = 0 ∧ radialSphereDerivative n w x r = 0 ∧
        radialSphereMean n (Laplacian.laplacian w) x r = 0 ∧
          radialBallLaplacian n w x r = 0 := by
  let T := tsupport w ∪ tsupport (fderiv ℝ w) ∪ tsupport (Laplacian.laplacian w)
  have hT : IsCompact T := hsupp.isCompact.union (hsupp.fderiv ℝ).isCompact
    |>.union (CenteredMaximal.Ball.hasCompactSupport_laplacian n w hsupp).isCompact
  obtain ⟨R, hbR, hTR⟩ := hT.isBounded.subset_ball_lt b x
  refine ⟨R, hbR, fun r hr ↦ ?_⟩
  have hrpos : 0 < r := hb.trans (hbR.trans_le hr)
  have hy (ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      x + r • (ω : EuclideanSpace ℝ (Fin n)) ∉ T := by
    intro hmem
    have hball := hTR hmem
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hrpos.le] at hball
    have hω : ‖(ω : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    rw [hω, mul_one] at hball
    exact (not_lt_of_ge hr) hball
  have hwzero : radialSphereMean n w x r = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy ω (Or.inl (Or.inl h)))
  have hdwzero : radialSphereDerivative n w x r = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    have hf := image_eq_zero_of_notMem_tsupport (f := fderiv ℝ w)
      (fun h ↦ hy ω (Or.inl (Or.inr h)))
    rw [hf]
    rfl
  have hΔzero : radialSphereMean n (Laplacian.laplacian w) x r = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy ω (Or.inr h))
  refine ⟨hwzero, hdwzero, hΔzero, ?_⟩
  rw [radialBallLaplacian_eq_flux n w hw hsupp x hrpos, hdwzero, mul_zero]

end PartialBalayage
