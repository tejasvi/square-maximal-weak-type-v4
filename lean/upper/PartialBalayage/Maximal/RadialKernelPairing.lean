/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.JoinedRadialKernelIntegrability
public import PartialBalayage.Maximal.RadialFluxComparison
public import PartialBalayage.Maximal.RadialPairingGeometry

/-!
# Laplacian comparison for joined radial kernels

A radial kernel with harmonic inner region, a nonnegative inward-flux drop at the join, and
decreasing outer inward flux pairs nonnegatively with every nonnegative smooth compactly
supported test function that vanishes at the kernel center. The proof includes the singular
center boundary and both compact-support boundaries.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Interval

namespace PartialBalayage

private theorem setIntegral_Ioi_eq_Ioo_of_zero {R : ℝ} (H : ℝ → ℝ)
    (hH : ∀ r, R ≤ r → H r = 0) :
    (∫ r in Ioi (0 : ℝ), H r) = ∫ r in Ioo (0 : ℝ) R, H r := by
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator H r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      by_cases hr : r < R
      · simp only [Set.indicator_of_mem (show r ∈ Iio R from hr)]
      · simp only [Set.indicator_of_notMem (show r ∉ Iio R from hr),
          hH r (le_of_not_gt hr)]
    _ = _ := by rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]

/-- A harmonic inner region and the stated outer flux facts give the actual Euclidean
Laplacian pairing inequality. All differential and geometric boundary terms are included. -/
theorem joinedRadialKernel_laplacian_pairing_nonneg (n : ℕ) (hn : 1 ≤ n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (q d : ℝ)
    (ψO M dψO dM : ℝ → ℝ)
    (hjoin : harmonicRadialTangent n a q d b = ψO b)
    (hψO : ∀ r, 0 < r → HasDerivAt ψO (dψO r) r)
    (hM : ∀ r, 0 < r → HasDerivAt M (dM r) r)
    (hcψO : Continuous ψO) (hcdM : Continuous dM)
    (hfluxO : ∀ r, 0 < r → dψO r * r ^ (n - 1) + 2 * M r = 0)
    (hdecrease : ∀ r, b ≤ r → dM r ≤ 0)
    (hjump : 0 ≤ -d * a ^ ((n : ℝ) / 2) - M b)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    0 ≤ ∫ y, joinedRadialKernel n a q d b ψO ‖y - x‖ * Laplacian.laplacian w y := by
  have : NeZero n := ⟨by omega⟩
  let ψI := harmonicRadialTangent n a q d
  let F := radialBallLaplacian n w x
  let m := radialSphereMean n w x
  let G := radialSphereMean n (Laplacian.laplacian w) x
  let Q := radialLaplacianDensity n w x
  let dm := radialSphereDerivative n w x
  let dψI := fun r : ℝ ↦ 2 * d * r * (r ^ 2 / a) ^ (-(n : ℝ) / 2)
  let k := -d * a ^ ((n : ℝ) / 2)
  have hcG : Continuous G := continuous_radialSphereMean n _
    (CenteredMaximal.Ball.continuous_laplacian n w hw) x
  have hcQ : Continuous Q := (continuous_id.pow (n - 1)).mul hcG
  have hcm : Continuous m := continuous_radialSphereMean n w hw.continuous x
  have hintI : IntegrableOn (fun r ↦ ψI r * Q r) (Ioo 0 b) := by
    have hi := integrableOn_harmonicRadialTangent_mul_pow_mul n hn (b := b) ha q d G hcG
    apply hi.congr_fun
    · intro r _
      dsimp [ψI, Q, radialLaplacianDensity, G]
      ring
    · exact measurableSet_Ioo
  have hψI : ∀ r, 0 < r → HasDerivAt ψI (dψI r) r :=
    fun r hr ↦ hasDerivAt_harmonicRadialTangent n ha hr q d
  have hF : ∀ r, 0 < r → HasDerivAt F (Q r) r :=
    fun r hr ↦ hasDerivAt_radialBallLaplacian n w hw hsupp x hr
  have hm : ∀ r, HasDerivAt m (dm r) r :=
    fun r ↦ hasDerivAt_radialSphereMean n w hw hsupp x r
  have hfluxI : ∀ r, 0 < r → dψI r * F r + 2 * k * dm r = 0 := by
    intro r hr
    have hder := harmonicRadialTangent_deriv_mul_pow n hn ha hr d
    have hball := radialBallLaplacian_eq_flux n w hw hsupp x hr
    change F r = r ^ (n - 1) * dm r at hball
    rw [hball]
    dsimp [k, dψI]
    nlinarith [congrArg (fun t : ℝ ↦ t * dm r) hder]
  have hfluxOuter : ∀ r, 0 < r → dψO r * F r + 2 * M r * dm r = 0 := by
    intro r hr
    have hball := radialBallLaplacian_eq_flux n w hw hsupp x hr
    change F r = r ^ (n - 1) * dm r at hball
    rw [hball]
    nlinarith [congrArg (fun t : ℝ ↦ t * dm r) (hfluxO r hr)]
  obtain ⟨R, hbR, hsupport⟩ := exists_radialPairing_support_radius n w hw hsupp x hb
  have hmR : m R = 0 := (hsupport R le_rfl).1
  have hFR : F R = 0 := (hsupport R le_rfl).2.2.2
  have hintO : IntervalIntegrable (fun r ↦ ψO r * Q r) volume b R :=
    (hcψO.mul hcQ).intervalIntegrable _ _
  have hintM : IntervalIntegrable (fun r ↦ dM r * m r) volume b R :=
    (hcdM.mul hcm).intervalIntegrable _ _
  have hannulus : ∀ δ : ℝ, 0 < δ → δ ≤ b →
      (∫ r in δ..b, ψI r * Q r) + (∫ r in b..R, ψO r * Q r) =
        2 * (k - M b) * m b - 2 * (∫ r in b..R, dM r * m r) -
          ψI δ * F δ - 2 * k * m δ := by
    intro δ hδ hδb
    have hinner : IntervalIntegrable (fun r ↦ ψI r * Q r) volume δ b := by
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hδb).mpr
      exact hintI.mono_set (fun r hr ↦ ⟨hδ.trans hr.1, hr.2⟩)
    have hiPos : ∀ r ∈ uIcc δ b, 0 < r := by
      rw [uIcc_of_le hδb]
      exact fun r hr ↦ hδ.trans_le hr.1
    have hoPos : ∀ r ∈ uIcc b R, 0 < r := by
      rw [uIcc_of_le hbR.le]
      exact fun r hr ↦ hb.trans_le hr.1
    have h := integral_joined_radial_flux_annulus δ b R k ψI ψO F m Q M
      dψI dψO dm dM hjoin (fun r hr ↦ hψI r (hiPos r hr))
      (fun r hr ↦ hF r (hiPos r hr)) (fun r _ ↦ hm r)
      (fun r hr ↦ hfluxI r (hiPos r hr)) (fun r hr ↦ hψO r (hoPos r hr))
      (fun r hr ↦ hF r (hoPos r hr)) (fun r _ ↦ hm r)
      (fun r hr ↦ hM r (hoPos r hr)) (fun r hr ↦ hfluxOuter r (hoPos r hr))
      hinner hintO hintM
    rw [hFR, hmR] at h
    linarith
  have hmzero : Tendsto m (𝓝[>] 0) (𝓝 0) :=
    tendsto_radialSphereMean_zero n w hw.continuous x hx
  obtain ⟨C, hC⟩ := CenteredMaximal.Ball.exists_bound_laplacian n w hw hsupp
  have hcenter : Tendsto (fun δ ↦ ψI δ * F δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_profile_mul_integral_ball_zero n ψI
      (harmonicRadialTangent_mul_pow_tendsto_zero n hn ha q d)
      (Laplacian.laplacian w) x C hC
  have hidentity := integral_joined_radial_flux_of_center_limits hb ψI ψO F m Q M dM
    hintI hannulus hmzero hcenter
  have houterNonneg := neg_integral_radial_flux_deriv_nonneg hbR.le dM m
    (fun r hr ↦ hdecrease r hr.1) (fun r _ ↦ radialSphereMean_nonneg n w hwpos x r)
  have hpairNonneg : 0 ≤ (∫ r in Ioo 0 b, ψI r * Q r) +
      (∫ r in b..R, ψO r * Q r) := by
    rw [hidentity]
    have hjoinNonneg : 0 ≤ (k - M b) * m b :=
      mul_nonneg hjump (radialSphereMean_nonneg n w hwpos x b)
    linarith
  let φ := joinedRadialKernel n a q d b ψO
  have hsplit : (∫ r in Ioo 0 R, φ r * Q r) =
      (∫ r in Ioo 0 b, ψI r * Q r) + (∫ r in b..R, ψO r * Q r) := by
    have heqI : EqOn (fun r ↦ φ r * Q r) (fun r ↦ ψI r * Q r) (Ioo 0 b) := by
      intro r hr
      simp only [φ, joinedRadialKernel, ite_eq_left hr.2, ψI]
    have heqO : EqOn (fun r ↦ φ r * Q r) (fun r ↦ ψO r * Q r) (Ico b R) := by
      intro r hr
      simp only [φ, joinedRadialKernel, ite_eq_right (not_lt.mpr hr.1)]
    have hi : IntegrableOn (fun r ↦ φ r * Q r) (Ioo 0 b) :=
      hintI.congr_fun (fun r hr ↦ (heqI hr).symm) measurableSet_Ioo
    have ho : IntegrableOn (fun r ↦ φ r * Q r) (Ico b R) :=
      ((hcψO.mul hcQ).continuousOn.integrableOn_compact isCompact_Icc
        |>.mono_set Ico_subset_Icc_self).congr_fun
        (fun r hr ↦ (heqO hr).symm) measurableSet_Ico
    rw [← Ioo_union_Ico_eq_Ioo hb hbR.le, setIntegral_union
      (disjoint_left.mpr (fun r hrI hrO ↦ (not_lt_of_ge hrO.1) hrI.2))
      measurableSet_Ico hi ho]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun r hr ↦ heqI hr),
      setIntegral_congr_fun measurableSet_Ico (fun r hr ↦ heqO hr),
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbR.le]
  have hambient := integrable_joinedRadialKernel_mul_compact n hn ha hb q d ψO hcψO
    (Laplacian.laplacian w) (CenteredMaximal.Ball.continuous_laplacian n w hw)
    (CenteredMaximal.Ball.hasCompactSupport_laplacian n w hsupp) x
  rw [CenteredMaximal.Ball.integral_radial_mul_polar_swapped n x φ _ hambient]
  have heq : (fun r : ℝ ↦ r ^ (n - 1) * φ r * G r) =
      (fun r ↦ φ r * Q r) := by
    funext r
    dsimp [Q, radialLaplacianDensity, G]
    ring
  change 0 ≤ ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * φ r * G r
  rw [heq, setIntegral_Ioi_eq_Ioo_of_zero (R := R) (fun r ↦ φ r * Q r)]
  · rw [hsplit]
    exact hpairNonneg
  · intro r hr
    have hGzero : G r = 0 := (hsupport r hr).2.2.1
    simp only [Q, radialLaplacianDensity, G] at hGzero ⊢
    rw [hGzero, mul_zero, mul_zero]

end PartialBalayage
