/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.RadialKernelPairing
public import PartialBalayage.Maximal.RadialKernelComparison

/-!
# Heat and Poisson harmonic-majorant kernel comparisons

The exact tangency parameters give actual Euclidean radial kernels. Their Laplacian pairings
are nonnegative against every nonnegative smooth compactly supported test function vanishing
at the kernel center, in every positive dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Constants

namespace PartialBalayage

private theorem continuous_one_add_sq_rpow (p : ℝ) :
    Continuous (fun r : ℝ ↦ (1 + r ^ 2) ^ p) := by
  have hb : Continuous (fun r : ℝ ↦ 1 + r ^ 2) := by fun_prop
  exact hb.rpow_const (fun r ↦ Or.inl (by positivity : 0 < 1 + r ^ 2).ne')

private theorem heatHarmonicTangent_radial (n : ℕ) (a r : ℝ) :
    heatHarmonicTangent n a (r ^ 2) =
      harmonicRadialTangent n a (Real.exp (-a)) (-Real.exp (-a)) r := by
  unfold heatHarmonicTangent heatTangentProfile harmonicRadialTangent
  ring

private theorem poissonHarmonicTangent_radial (n : ℕ) (a r : ℝ) :
    poissonHarmonicTangent n a (r ^ 2) =
      harmonicRadialTangent n a ((1 + a) ^ (-(((n : ℝ) + 1) / 2)))
        (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2))) r := by
  unfold poissonHarmonicTangent poissonTangentProfile harmonicRadialTangent
  rw [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring,
    show (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 by ring]

/-- The squared-radius heat majorant is the same actual ordinary-radius joined kernel. -/
theorem heatMajorantProfile_eq_joinedRadialKernel (n : ℕ) (a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hB2 : B ^ 2 = rho n * a) (hr : 0 ≤ r) :
    heatMajorantProfile n a (r ^ 2) =
      joinedRadialKernel n a (Real.exp (-a)) (-Real.exp (-a)) B
        (fun s ↦ Real.exp (-(s ^ 2))) r := by
  by_cases hrB : r < B
  · have hs : r ^ 2 < rho n * a := by nlinarith [hB2]
    simp only [heatMajorantProfile, joinedRadialKernel, ite_eq_left hs,
      ite_eq_left hrB, heatHarmonicTangent_radial]
  · have hs : ¬r ^ 2 < rho n * a := by nlinarith [hB2, not_lt.mp hrB]
    simp only [heatMajorantProfile, joinedRadialKernel, ite_eq_right hs, ite_eq_right hrB]

/-- The squared-radius Poisson majorant is the same actual ordinary-radius joined kernel. -/
theorem poissonMajorantProfile_eq_joinedRadialKernel (n : ℕ) (a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hB2 : B ^ 2 = rho n * a) (hr : 0 ≤ r) :
    poissonMajorantProfile n a (r ^ 2) =
      joinedRadialKernel n a ((1 + a) ^ (-(((n : ℝ) + 1) / 2)))
        (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2))) B
        (fun s ↦ (1 + s ^ 2) ^ (-(((n : ℝ) + 1) / 2))) r := by
  by_cases hrB : r < B
  · have hs : r ^ 2 < rho n * a := by nlinarith [hB2]
    simp only [poissonMajorantProfile, joinedRadialKernel, ite_eq_left hs,
      ite_eq_left hrB, poissonHarmonicTangent_radial]
  · have hs : ¬r ^ 2 < rho n * a := by nlinarith [hB2, not_lt.mp hrB]
    simp only [poissonMajorantProfile, joinedRadialKernel, ite_eq_right hs, ite_eq_right hrB]

/-- The actual heat majorant has a finite signed pairing with every continuous compact density. -/
theorem integrable_heatMajorantProfile_mul_compact (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsHeatTangencyParameter n a)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ heatMajorantProfile n a (‖y - x‖ ^ 2) * g y) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hba : 0 < rho n * a := mul_pos hρ ha
  have hB : 0 < Real.sqrt (rho n * a) := Real.sqrt_pos.mpr hba
  have hB2 : Real.sqrt (rho n * a) ^ 2 = rho n * a := Real.sq_sqrt hba.le
  have hi := integrable_joinedRadialKernel_mul_compact n hn ha hB (Real.exp (-a))
    (-Real.exp (-a)) (fun r ↦ Real.exp (-(r ^ 2))) (by fun_prop) g hg hgsupp x
  apply hi.congr
  filter_upwards with y
  rw [← heatMajorantProfile_eq_joinedRadialKernel n a hB hB2 (norm_nonneg _)]

/-- The actual Poisson majorant pairs integrably with every continuous compact density. -/
theorem integrable_poissonMajorantProfile_mul_compact (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsPoissonTangencyParameter n a)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ poissonMajorantProfile n a (‖y - x‖ ^ 2) * g y) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hba : 0 < rho n * a := mul_pos hρ ha
  have hB : 0 < Real.sqrt (rho n * a) := Real.sqrt_pos.mpr hba
  have hB2 : Real.sqrt (rho n * a) ^ 2 = rho n * a := Real.sq_sqrt hba.le
  have hi := integrable_joinedRadialKernel_mul_compact n hn ha hB
    ((1 + a) ^ (-(((n : ℝ) + 1) / 2)))
    (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2)))
    (fun r ↦ (1 + r ^ 2) ^ (-(((n : ℝ) + 1) / 2)))
    (continuous_one_add_sq_rpow _) g hg hgsupp x
  apply hi.congr
  filter_upwards with y
  rw [← poissonMajorantProfile_eq_joinedRadialKernel n a hB hB2 (norm_nonneg _)]

/-- The actual heat harmonic-majorant kernel has the required Laplacian comparison property. -/
theorem heatMajorantProfile_laplacian_pairing_nonneg (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsHeatTangencyParameter n a)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    0 ≤ ∫ y, heatMajorantProfile n a (‖y - x‖ ^ 2) * Laplacian.laplacian w y := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hba : 0 < rho n * a := mul_pos hρ ha
  let B := Real.sqrt (rho n * a)
  have hB : 0 < B := Real.sqrt_pos.mpr hba
  have hB2 : B ^ 2 = rho n * a := Real.sq_sqrt hba.le
  let ψO := fun r : ℝ ↦ Real.exp (-(r ^ 2))
  let dψO := fun r : ℝ ↦ -2 * r * Real.exp (-(r ^ 2))
  let dM := fun r : ℝ ↦ r ^ (n - 1) * ((n : ℝ) - 2 * r ^ 2) * Real.exp (-(r ^ 2))
  have hjoin : harmonicRadialTangent n a (Real.exp (-a)) (-Real.exp (-a)) B = ψO B := by
    dsimp only [ψO]
    rw [← heatHarmonicTangent_radial, hB2]
    exact heatHarmonicTangent_join n hn ha hroot
  have hψ : ∀ r, 0 < r → HasDerivAt ψO (dψO r) r := by
    intro r _
    convert ((hasDerivAt_pow 2 r).neg.exp) using 1
    simp only [dψO, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hflux : ∀ r, 0 < r → dψO r * r ^ (n - 1) +
      2 * heatRadialInwardFlux n r = 0 := by
    intro r _
    have hp : r ^ n = r ^ (n - 1) * r := by
      nth_rw 1 [← Nat.sub_add_cancel hn]
      rw [pow_succ]
    dsimp [dψO, heatRadialInwardFlux]
    rw [hp]
    ring
  have hdecrease : ∀ r, B ≤ r → dM r ≤ 0 := by
    intro r hr
    have hrpos := hB.trans_le hr
    have hsq : rho n * a ≤ r ^ 2 := by nlinarith [hB2]
    have hd := (heatRadialInwardFlux_deriv_neg_of_root n hn hroot hrpos hsq).le
    rw [(hasDerivAt_heatRadialInwardFlux n hn r).deriv] at hd
    exact hd
  have hjump : 0 ≤ -(-Real.exp (-a)) * a ^ ((n : ℝ) / 2) -
      heatRadialInwardFlux n B := by
    have h := (heatInnerInwardFlux_sub_outer_pos n hn hroot hB hB2).le
    simpa only [heatInnerInwardFlux, neg_neg, mul_comm] using h
  have hcomparison := joinedRadialKernel_laplacian_pairing_nonneg n hn ha hB
    (Real.exp (-a)) (-Real.exp (-a)) ψO (heatRadialInwardFlux n) dψO dM hjoin hψ
    (fun r _ ↦ hasDerivAt_heatRadialInwardFlux n hn r) (by fun_prop) (by fun_prop)
    hflux hdecrease hjump w hw hsupp hwpos x hx
  have hprofile : ∀ r : ℝ, 0 ≤ r → heatMajorantProfile n a (r ^ 2) =
      joinedRadialKernel n a (Real.exp (-a)) (-Real.exp (-a)) B ψO r := by
    intro r hr
    by_cases hrB : r < B
    · have hs : r ^ 2 < rho n * a := by nlinarith [hB2]
      simp only [heatMajorantProfile, joinedRadialKernel, ite_eq_left hs,
        ite_eq_left hrB, heatHarmonicTangent_radial]
    · have hs : ¬r ^ 2 < rho n * a := by nlinarith [hB2, not_lt.mp hrB]
      simp only [heatMajorantProfile, joinedRadialKernel, ite_eq_right hs,
        ite_eq_right hrB, ψO]
  simpa only [hprofile _ (norm_nonneg _)] using hcomparison

/-- The actual Poisson harmonic-majorant kernel has the required Laplacian comparison property. -/
theorem poissonMajorantProfile_laplacian_pairing_nonneg (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsPoissonTangencyParameter n a)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hwpos : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    0 ≤ ∫ y, poissonMajorantProfile n a (‖y - x‖ ^ 2) * Laplacian.laplacian w y := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hba : 0 < rho n * a := mul_pos hρ ha
  let B := Real.sqrt (rho n * a)
  have hB : 0 < B := Real.sqrt_pos.mpr hba
  have hB2 : B ^ 2 = rho n * a := Real.sq_sqrt hba.le
  let γ := ((n : ℝ) + 1) / 2
  let m := ((n : ℝ) + 3) / 2
  let q := (1 + a) ^ (-γ)
  let d := -γ * (1 + a) ^ (-m)
  let ψO := fun r : ℝ ↦ (1 + r ^ 2) ^ (-γ)
  let dψO := fun r : ℝ ↦ -2 * γ * r * (1 + r ^ 2) ^ (-m)
  let dM := fun r : ℝ ↦ γ * r ^ (n - 1) * ((n : ℝ) - 3 * r ^ 2) *
    (1 + r ^ 2) ^ (-(((n : ℝ) + 5) / 2))
  have hjoin : harmonicRadialTangent n a q d B = ψO B := by
    dsimp only [ψO, q, d, γ, m]
    rw [← poissonHarmonicTangent_radial, hB2]
    exact poissonHarmonicTangent_join n hn ha hroot
  have hψ : ∀ r, 0 < r → HasDerivAt ψO (dψO r) r := by
    intro r _
    have hp : 0 < 1 + r ^ 2 := by positivity
    have hd := (Real.hasDerivAt_rpow_const (p := -γ) (Or.inl hp.ne')).comp r
      ((hasDerivAt_pow 2 r).const_add 1)
    convert hd using 1
    · rfl
    · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      rw [show -γ - 1 = -m by dsimp [γ, m]; ring]
      dsimp [dψO]
      ring
  have hflux : ∀ r, 0 < r → dψO r * r ^ (n - 1) +
      2 * poissonRadialInwardFlux n r = 0 := by
    intro r _
    have hp : r ^ n = r ^ (n - 1) * r := by
      nth_rw 1 [← Nat.sub_add_cancel hn]
      rw [pow_succ]
    dsimp [dψO, poissonRadialInwardFlux, γ, m]
    rw [hp]
    ring
  have hdecrease : ∀ r, B ≤ r → dM r ≤ 0 := by
    intro r hr
    have hrpos := hB.trans_le hr
    have hsq : rho n * a ≤ r ^ 2 := by nlinarith [hB2]
    have hd := (poissonRadialInwardFlux_deriv_neg_of_root n hn hroot hrpos hsq).le
    rw [(hasDerivAt_poissonRadialInwardFlux n hn r).deriv] at hd
    exact hd
  have hjump : 0 ≤ -d * a ^ ((n : ℝ) / 2) - poissonRadialInwardFlux n B := by
    have h := (poissonInnerInwardFlux_sub_outer_pos n hn hroot hB hB2).le
    convert h using 1
    dsimp [d, γ, m, poissonInnerInwardFlux]
    ring
  have hcdM : Continuous dM :=
    (((continuous_id.pow (n - 1)).const_mul γ).mul
      (continuous_const.sub ((continuous_id.pow 2).const_mul 3))).mul
        (continuous_one_add_sq_rpow _)
  have hcomparison := joinedRadialKernel_laplacian_pairing_nonneg n hn ha hB q d ψO
    (poissonRadialInwardFlux n) dψO dM hjoin hψ
    (fun r _ ↦ hasDerivAt_poissonRadialInwardFlux n hn r)
    (continuous_one_add_sq_rpow _) hcdM
    hflux hdecrease hjump w hw hsupp hwpos x hx
  have hprofile : ∀ r : ℝ, 0 ≤ r → poissonMajorantProfile n a (r ^ 2) =
      joinedRadialKernel n a q d B ψO r := by
    intro r hr
    by_cases hrB : r < B
    · have hs : r ^ 2 < rho n * a := by nlinarith [hB2]
      simp only [poissonMajorantProfile, joinedRadialKernel, ite_eq_left hs,
        ite_eq_left hrB, poissonHarmonicTangent_radial, q, d, γ, m]
    · have hs : ¬r ^ 2 < rho n * a := by nlinarith [hB2, not_lt.mp hrB]
      simp only [poissonMajorantProfile, joinedRadialKernel, ite_eq_right hs,
        ite_eq_right hrB, ψO, γ]
  simpa only [hprofile _ (norm_nonneg _)] using hcomparison

end PartialBalayage
