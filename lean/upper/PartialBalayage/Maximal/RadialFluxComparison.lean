/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic
public import CenteredMaximal.Ball.RadialGreenLimit

/-!
# Radial flux integration by parts

This scalar identity handles both the harmonic inner part and the curved outer part of an
actual radial majorant. The radial inward flux `M` is constant in the harmonic region and
decreases in the outer region. Its downward jump at the joining radius contributes positively
when pairing against a nonnegative test function that vanishes at the center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace PartialBalayage

/-- The finite-annulus radial integration identity, including the variable inward flux. -/
theorem integral_radial_flux_annulus (δ R : ℝ)
    (ψ F m q M dψ dm dM : ℝ → ℝ)
    (hψ : ∀ r ∈ uIcc δ R, HasDerivAt ψ (dψ r) r)
    (hF : ∀ r ∈ uIcc δ R, HasDerivAt F (q r) r)
    (hm : ∀ r ∈ uIcc δ R, HasDerivAt m (dm r) r)
    (hM : ∀ r ∈ uIcc δ R, HasDerivAt M (dM r) r)
    (hflux : ∀ r ∈ uIcc δ R, dψ r * F r + 2 * M r * dm r = 0)
    (hint : IntervalIntegrable (fun r ↦ ψ r * q r) volume δ R)
    (hintM : IntervalIntegrable (fun r ↦ dM r * m r) volume δ R) :
    (∫ r in δ..R, ψ r * q r) =
      ψ R * F R - ψ δ * F δ + 2 * (M R * m R - M δ * m δ) -
        2 * ∫ r in δ..R, dM r * m r := by
  have hder : ∀ r ∈ uIcc δ R,
      HasDerivAt (fun r ↦ ψ r * F r + 2 * (M r * m r))
        (ψ r * q r + 2 * (dM r * m r)) r := by
    intro r hr
    convert ((hψ r hr).mul (hF r hr)).add (((hM r hr).mul (hm r hr)).const_mul 2)
      using 1
    nlinarith [hflux r hr]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hint.add (hintM.const_mul 2))
  rw [intervalIntegral.integral_add hint (hintM.const_mul 2),
    intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- An outward-positive radial Laplacian contributes nonnegatively to the pairing. -/
theorem neg_integral_radial_flux_deriv_nonneg {b R : ℝ} (hbR : b ≤ R)
    (M' m : ℝ → ℝ) (hM : ∀ r ∈ Icc b R, M' r ≤ 0)
    (hm : ∀ r ∈ Icc b R, 0 ≤ m r) :
    0 ≤ -(∫ r in b..R, M' r * m r) := by
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_nonneg hbR
  intro r hr
  exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hM r hr) (hm r hr))

/-- Splitting at a harmonic-to-curved join produces its positive flux-jump contribution. -/
theorem integral_joined_radial_flux_annulus (δ b R k : ℝ)
    (ψI ψO F m q M dψI dψO dm dM : ℝ → ℝ)
    (hjoin : ψI b = ψO b)
    (hψI : ∀ r ∈ uIcc δ b, HasDerivAt ψI (dψI r) r)
    (hFI : ∀ r ∈ uIcc δ b, HasDerivAt F (q r) r)
    (hmI : ∀ r ∈ uIcc δ b, HasDerivAt m (dm r) r)
    (hfluxI : ∀ r ∈ uIcc δ b, dψI r * F r + 2 * k * dm r = 0)
    (hψO : ∀ r ∈ uIcc b R, HasDerivAt ψO (dψO r) r)
    (hFO : ∀ r ∈ uIcc b R, HasDerivAt F (q r) r)
    (hmO : ∀ r ∈ uIcc b R, HasDerivAt m (dm r) r)
    (hM : ∀ r ∈ uIcc b R, HasDerivAt M (dM r) r)
    (hfluxO : ∀ r ∈ uIcc b R, dψO r * F r + 2 * M r * dm r = 0)
    (hintI : IntervalIntegrable (fun r ↦ ψI r * q r) volume δ b)
    (hintO : IntervalIntegrable (fun r ↦ ψO r * q r) volume b R)
    (hintM : IntervalIntegrable (fun r ↦ dM r * m r) volume b R) :
    (∫ r in δ..b, ψI r * q r) + (∫ r in b..R, ψO r * q r) =
      ψO R * F R - ψI δ * F δ + 2 * (M R * m R - k * m δ) +
        2 * (k - M b) * m b - 2 * ∫ r in b..R, dM r * m r := by
  have hi := integral_radial_flux_annulus δ b ψI F m q (fun _ ↦ k) dψI dm (fun _ ↦ 0)
    hψI hFI hmI (fun r _ ↦ hasDerivAt_const r k) hfluxI hintI
    (by simpa only [zero_mul] using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume δ b))
  have ho := integral_radial_flux_annulus b R ψO F m q M dψO dm dM
    hψO hFO hmO hM hfluxO hintO hintM
  simp only [zero_mul, intervalIntegral.integral_zero] at hi
  rw [hjoin] at hi
  nlinarith

/-- Sending the annulus's inner boundary to a zero of the test function leaves the positive
join contribution and the curved outer contribution. -/
theorem integral_joined_radial_flux_of_center_limits {b R k : ℝ} (hb : 0 < b)
    (ψI ψO F m q M dM : ℝ → ℝ)
    (hint : IntegrableOn (fun r ↦ ψI r * q r) (Ioo 0 b))
    (hannulus : ∀ δ : ℝ, 0 < δ → δ ≤ b →
      (∫ r in δ..b, ψI r * q r) + (∫ r in b..R, ψO r * q r) =
        2 * (k - M b) * m b - 2 * (∫ r in b..R, dM r * m r) -
          ψI δ * F δ - 2 * k * m δ)
    (hm₀ : Tendsto m (𝓝[>] 0) (𝓝 0))
    (hboundary : Tendsto (fun δ ↦ ψI δ * F δ) (𝓝[>] 0) (𝓝 0)) :
    (∫ r in Ioo 0 b, ψI r * q r) + (∫ r in b..R, ψO r * q r) =
      2 * (k - M b) * m b - 2 * ∫ r in b..R, dM r * m r := by
  have hleft := (CenteredMaximal.Ball.tendsto_integral_interval_to_Ioo
    (fun r ↦ ψI r * q r) hb hint).add
      (tendsto_const_nhds (x := (∫ r in b..R, ψO r * q r)))
  have hright : Tendsto (fun δ ↦ 2 * (k - M b) * m b -
      2 * (∫ r in b..R, dM r * m r) - ψI δ * F δ - 2 * k * m δ)
      (𝓝[>] 0) (𝓝 (2 * (k - M b) * m b - 2 * ∫ r in b..R, dM r * m r)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub hboundary).sub (hm₀.const_mul (2 * k))
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hδle : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ b :=
    ((eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds).mono (fun δ hδ ↦ hδ.le)
  have heq : (fun δ ↦ (∫ r in δ..b, ψI r * q r) + (∫ r in b..R, ψO r * q r))
      =ᶠ[𝓝[>] 0] (fun δ ↦ 2 * (k - M b) * m b -
        2 * (∫ r in b..R, dM r * m r) - ψI δ * F δ - 2 * k * m δ) := by
    filter_upwards [hδpos, hδle] with δ hpos hle
    exact hannulus δ hpos hle
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end PartialBalayage
