/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.HeatMajorant
public import PartialBalayage.Maximal.PoissonMajorant

/-!
# Inward radial flux of the actual heat and Poisson profiles

The inward flux is one half of the negative radial derivative times `r^(n-1)`.
It is constant in each harmonic tangent region and decreases in the curved outer region.
This calculus is the input for the radial integration-by-parts kernel comparison.
-/

@[expose] public section

noncomputable section

open Set
open PartialBalayage.Constants

namespace PartialBalayage

/-- The inward radial flux of the ordinary heat squared-radius profile. -/
def heatRadialInwardFlux (n : ℕ) (r : ℝ) : ℝ := r ^ n * Real.exp (-(r ^ 2))

/-- The inward radial flux of the ordinary Poisson squared-radius profile. -/
def poissonRadialInwardFlux (n : ℕ) (r : ℝ) : ℝ :=
  ((n : ℝ) + 1) / 2 * r ^ n * (1 + r ^ 2) ^ (-(((n : ℝ) + 3) / 2))

/-- The constant inward flux in the harmonic heat tangent region. -/
def heatInnerInwardFlux (n : ℕ) (a : ℝ) : ℝ :=
  a ^ ((n : ℝ) / 2) * Real.exp (-a)

/-- The constant inward flux in the harmonic Poisson tangent region. -/
def poissonInnerInwardFlux (n : ℕ) (a : ℝ) : ℝ :=
  ((n : ℝ) + 1) / 2 * a ^ ((n : ℝ) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2))

private theorem sq_rpow_half_dimension (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r ^ n = (r ^ 2) ^ ((n : ℝ) / 2) := by
  simpa only [Real.rpow_two, show 2 * ((n : ℝ) / 2) = (n : ℝ) by ring,
    Real.rpow_natCast] using Real.rpow_mul hr.le (2 : ℝ) ((n : ℝ) / 2)

/-- The derivative of heat inward flux changes sign at radius squared `n/2`. -/
theorem hasDerivAt_heatRadialInwardFlux (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (heatRadialInwardFlux n)
      (r ^ (n - 1) * ((n : ℝ) - 2 * r ^ 2) * Real.exp (-(r ^ 2))) r := by
  have hp : r ^ n = r ^ (n - 1) * r := by
    nth_rw 1 [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  convert (hasDerivAt_pow n r).mul ((hasDerivAt_pow 2 r).neg.exp) using 1
  · rfl
  · simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hp]
    ring

/-- Heat inward flux is strictly decreasing beyond squared radius `n/2`. -/
theorem heatRadialInwardFlux_deriv_neg (n : ℕ) (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (hcrit : (n : ℝ) / 2 < r ^ 2) :
    deriv (heatRadialInwardFlux n) r < 0 := by
  rw [(hasDerivAt_heatRadialInwardFlux n hn r).deriv]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (pow_pos hr _) (by linarith)) (Real.exp_pos _)

/-- The derivative of Poisson inward flux changes sign at radius squared `n/3`. -/
theorem hasDerivAt_poissonRadialInwardFlux (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (poissonRadialInwardFlux n)
      ((((n : ℝ) + 1) / 2) * r ^ (n - 1) * ((n : ℝ) - 3 * r ^ 2) *
        (1 + r ^ 2) ^ (-(((n : ℝ) + 5) / 2))) r := by
  have hb : 0 < 1 + r ^ 2 := by positivity
  have hp : r ^ n = r ^ (n - 1) * r := by
    nth_rw 1 [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hd := (Real.hasDerivAt_rpow_const (p := -(((n : ℝ) + 3) / 2))
    (Or.inl hb.ne')).comp r ((hasDerivAt_pow 2 r).const_add 1)
  have he : (1 + r ^ 2) ^ (-(((n : ℝ) + 3) / 2)) =
      (1 + r ^ 2) * (1 + r ^ 2) ^ (-(((n : ℝ) + 5) / 2)) := by
    calc
      _ = (1 + r ^ 2) ^ (1 + (-(((n : ℝ) + 5) / 2))) := by congr 1; ring
      _ = (1 + r ^ 2) ^ (1 : ℝ) * (1 + r ^ 2) ^ (-(((n : ℝ) + 5) / 2)) :=
        Real.rpow_add hb _ _
      _ = _ := by rw [Real.rpow_one]
  convert ((hasDerivAt_pow n r).mul hd).const_mul (((n : ℝ) + 1) / 2) using 1
  · funext s
    dsimp [poissonRadialInwardFlux]
    ring
  · simp only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [show -(((n : ℝ) + 3) / 2) - 1 = -(((n : ℝ) + 5) / 2) by ring, hp, he]
    ring

/-- Poisson inward flux is strictly decreasing beyond squared radius `n/3`. -/
theorem poissonRadialInwardFlux_deriv_neg (n : ℕ) (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (hcrit : (n : ℝ) / 3 < r ^ 2) :
    deriv (poissonRadialInwardFlux n) r < 0 := by
  rw [(hasDerivAt_poissonRadialInwardFlux n hn r).deriv]
  have hγ : 0 < ((n : ℝ) + 1) / 2 := by positivity
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos hγ (pow_pos hr _)) (by linarith))
    (Real.rpow_pos_of_pos (by positivity) _)

/-- The exact heat root places the whole outer region beyond the heat inflection radius. -/
theorem heatRadialInwardFlux_deriv_neg_of_root (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (hroot : IsHeatTangencyParameter n a) (hr : 0 < r) (hb : rho n * a ≤ r ^ 2) :
    deriv (heatRadialInwardFlux n) r < 0 := by
  have hr0 := rho_pos n hn
  have hcrit : (n : ℝ) / 2 < rho n * a := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * rho n)).mp hroot.1.1
    nlinarith
  exact heatRadialInwardFlux_deriv_neg n hn hr (hcrit.trans_le hb)

/-- The exact Poisson root places the whole outer region beyond its inflection radius. -/
theorem poissonRadialInwardFlux_deriv_neg_of_root (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (hr : 0 < r) (hb : rho n * a ≤ r ^ 2) :
    deriv (poissonRadialInwardFlux n) r < 0 := by
  have hr0 := rho_pos n hn
  have hcrit : (n : ℝ) / 3 < rho n * a := by
    have h := (div_lt_iff₀ (by positivity : 0 < 3 * rho n)).mp hroot.1.1
    nlinarith
  exact poissonRadialInwardFlux_deriv_neg n hn hr (hcrit.trans_le hb)

/-- The actual heat radial inward flux has a strictly downward jump at the joining radius. -/
theorem heatInnerInwardFlux_sub_outer_pos (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (hroot : IsHeatTangencyParameter n a) (hr : 0 < r) (hb : r ^ 2 = rho n * a) :
    0 < heatInnerInwardFlux n a - heatRadialInwardFlux n r := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hb0 : 0 < rho n * a := mul_pos hr0 ha
  have hbp : (rho n * a) ^ ((n : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hb0 _).ne'
  have hp := mul_pos (Real.rpow_pos_of_pos hb0 ((n : ℝ) / 2))
    (heatHarmonicTangent_flux_jump_pos n hn hroot)
  have he : (rho n * a) ^ ((n : ℝ) / 2) *
      (-Real.exp (-(rho n * a)) -
        (-Real.exp (-a) * a ^ ((n : ℝ) / 2) * (rho n * a) ^ (-((n : ℝ) / 2)))) =
      heatInnerInwardFlux n a - (rho n * a) ^ ((n : ℝ) / 2) * Real.exp (-(rho n * a)) := by
    unfold heatInnerInwardFlux
    rw [Real.rpow_neg hb0.le]
    field_simp
    ring
  rw [he] at hp
  unfold heatRadialInwardFlux
  rw [sq_rpow_half_dimension n hr, hb]
  exact hp

/-- The actual Poisson radial inward flux has a downward jump at the joining radius. -/
theorem poissonInnerInwardFlux_sub_outer_pos (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (hr : 0 < r) (hb : r ^ 2 = rho n * a) :
    0 < poissonInnerInwardFlux n a - poissonRadialInwardFlux n r := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hb0 : 0 < rho n * a := mul_pos hr0 ha
  have hbp : (rho n * a) ^ ((n : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hb0 _).ne'
  have hp := mul_pos (Real.rpow_pos_of_pos hb0 ((n : ℝ) / 2))
    (poissonHarmonicTangent_flux_jump_pos n hn hroot)
  have he : (rho n * a) ^ ((n : ℝ) / 2) *
      (-(((n : ℝ) + 1) / 2) * (1 + rho n * a) ^ (-(((n : ℝ) + 3) / 2)) -
        (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2)) *
          a ^ ((n : ℝ) / 2) * (rho n * a) ^ (-((n : ℝ) / 2)))) =
      poissonInnerInwardFlux n a - ((n : ℝ) + 1) / 2 * (rho n * a) ^ ((n : ℝ) / 2) *
        (1 + rho n * a) ^ (-(((n : ℝ) + 3) / 2)) := by
    unfold poissonInnerInwardFlux
    rw [Real.rpow_neg hb0.le]
    field_simp
    ring
  rw [he] at hp
  unfold poissonRadialInwardFlux
  rw [sq_rpow_half_dimension n hr, hb]
  exact hp

end PartialBalayage
