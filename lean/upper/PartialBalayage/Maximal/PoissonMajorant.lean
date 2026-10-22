/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import PartialBalayage.Maximal.RadialTangentMass

/-!
# Harmonic majorization of the Poisson profile

The Poisson squared-radius profile is `(1 + z)^(-(n + 1) / 2)`. Its harmonic tangent at the
article's exact Poisson root dominates the profile until the balanced outer joining radius.
The outward derivative increases at that joining radius. The inner tangent also has the exact
weighted mass in the article. These scalar facts do not assert a maximal-operator bound.
-/

@[expose] public section

noncomputable section

open Set
open PartialBalayage.Constants

namespace PartialBalayage

/-- The harmonic Poisson tangent with radial exponent `β`, before choosing the dimension. -/
def poissonTangentProfile (β a z : ℝ) : ℝ :=
  (1 + a) ^ (-(β + 1 / 2)) +
    a * (-(β + 1 / 2) * (1 + a) ^ (-(β + 3 / 2))) * harmonicCoordinate β (z / a)

/-- The radial harmonic tangent to the Poisson profile in squared-radius coordinates. -/
def poissonHarmonicTangent (n : ℕ) (a z : ℝ) : ℝ :=
  poissonTangentProfile ((n : ℝ) / 2) a z

/-- The tangent inside the joining radius and the original Poisson profile outside. -/
def poissonMajorantProfile (n : ℕ) (a z : ℝ) : ℝ :=
  if z < rho n * a then poissonHarmonicTangent n a z
  else (1 + z) ^ (-(((n : ℝ) + 1) / 2))

private theorem poissonTangentProfile_at_tangency {β a : ℝ} (ha : 0 < a) :
    poissonTangentProfile β a a = (1 + a) ^ (-(β + 1 / 2)) := by
  simp [poissonTangentProfile, ha.ne', harmonicCoordinate_one]

private theorem hasDerivAt_poissonTangentProfile {β a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (poissonTangentProfile β a)
      (-(β + 1 / 2) * (1 + a) ^ (-(β + 3 / 2)) * a ^ β * z ^ (-β)) z := by
  have hd := (hasDerivAt_harmonicCoordinate (β := β) (div_pos hz ha)).comp z
    ((hasDerivAt_id z).div_const a)
  convert (hd.const_mul (a * (-(β + 1 / 2) * (1 + a) ^ (-(β + 3 / 2))))).const_add
    ((1 + a) ^ (-(β + 1 / 2))) using 1
  · rfl
  · rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul]
    field_simp

private theorem hasDerivAt_poissonProfile {β z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z : ℝ ↦ (1 + z) ^ (-(β + 1 / 2)))
      (-(β + 1 / 2) * (1 + z) ^ (-(β + 3 / 2))) z := by
  have hb : 0 < 1 + z := by positivity
  convert (Real.hasDerivAt_rpow_const (p := -(β + 1 / 2)) (Or.inl hb.ne')).comp z
    ((hasDerivAt_id z).const_add 1) using 1
  · rfl
  · rw [show -(β + 1 / 2) - 1 = -(β + 3 / 2) by ring]
    ring

private def poissonWeightedSlope (β z : ℝ) : ℝ :=
  (β + 1 / 2) * Real.exp (poissonWeightLog β z)

private theorem poissonWeightedSlope_lt {β x y : ℝ} (hβ : 0 < β) (hx : 0 < x)
    (hxy : x < y) (hy : y ≤ 2 * β / 3) :
    poissonWeightedSlope β x < poissonWeightedSlope β y := by
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (poissonWeightLog_lt hβ hx hxy hy))
    (by linarith)

private theorem poissonWeightedSlope_gt {β x y : ℝ} (hβ : 0 < β)
    (hx : 2 * β / 3 ≤ x) (hxy : x < y) :
    poissonWeightedSlope β y < poissonWeightedSlope β x := by
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (poissonWeightLog_gt hβ hx hxy))
    (by linarith)

private theorem harmonicCoordinate_strictMonoOn (β : ℝ) :
    StrictMonoOn (harmonicCoordinate β) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro z hz
    exact ((hasDerivAt_harmonicCoordinate (β := β) hz).continuousAt).continuousWithinAt
  · intro z hz
    have hz0 : 0 < z := by simpa using hz
    rw [(hasDerivAt_harmonicCoordinate (β := β) hz0).deriv]
    exact Real.rpow_pos_of_pos hz0 _

private theorem poissonDifference_harmonic_meanValue {β a x y : ℝ} (ha : 0 < a)
    (hx : 0 < x) (hxy : x < y) :
    ∃ c ∈ Ioo x y,
      (harmonicCoordinate β y - harmonicCoordinate β x) *
          (poissonWeightedSlope β c - poissonWeightedSlope β a) =
        (poissonTangentProfile β a y - (1 + y) ^ (-(β + 1 / 2))) -
          (poissonTangentProfile β a x - (1 + x) ^ (-(β + 1 / 2))) := by
  let f : ℝ → ℝ := fun z ↦ poissonTangentProfile β a z - (1 + z) ^ (-(β + 1 / 2))
  let d : ℝ → ℝ := fun z ↦
    (poissonWeightedSlope β z - poissonWeightedSlope β a) * z ^ (-β)
  have hd : ∀ z ∈ Icc x y, HasDerivAt f (d z) z := by
    intro z hz
    have hz0 : 0 < z := hx.trans_le hz.1
    convert (hasDerivAt_poissonTangentProfile ha hz0).sub
      (hasDerivAt_poissonProfile hz0) using 1
    dsimp [d, poissonWeightedSlope]
    rw [poissonWeightLog_exp hz0, poissonWeightLog_exp ha, Real.rpow_neg hz0.le]
    field_simp
    ring
  have hf : ContinuousOn f (Icc x y) := fun z hz ↦
    ((hd z hz).continuousAt).continuousWithinAt
  have hg : ContinuousOn (harmonicCoordinate β) (Icc x y) := fun z hz ↦
    ((hasDerivAt_harmonicCoordinate (β := β)
      (hx.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f d hxy hf
    (fun z hz ↦ hd z ⟨hz.1.le, hz.2.le⟩) (harmonicCoordinate β)
    (fun z ↦ z ^ (-β)) hg
    (fun z hz ↦ hasDerivAt_harmonicCoordinate (hx.trans hz.1))
  have hcp : c ^ (-β) ≠ 0 := (Real.rpow_pos_of_pos (hx.trans hc.1) _).ne'
  refine ⟨c, hc, ?_⟩
  dsimp [f, d] at he
  apply (mul_right_cancel₀ hcp)
  convert he using 1
  ring

private theorem poissonTangentProfile_majorizes_of_join {β a b z : ℝ}
    (hβ : 0 < β) (ha : 0 < a) (haβ : a < 2 * β / 3) (_hab : a < b)
    (hjoin : poissonTangentProfile β a b = (1 + b) ^ (-(β + 1 / 2)))
    (hz : z ∈ Ioo 0 b) : (1 + z) ^ (-(β + 1 / 2)) ≤ poissonTangentProfile β a z := by
  by_cases hza : z = a
  · subst z
    exact (poissonTangentProfile_at_tangency ha).ge
  by_cases hza' : z < a
  · obtain ⟨c, hc, he⟩ := poissonDifference_harmonic_meanValue (β := β) ha hz.1 hza'
    have hw := poissonWeightedSlope_lt hβ (hz.1.trans hc.1) hc.2 haβ.le
    have hH : 0 < harmonicCoordinate β a - harmonicCoordinate β z :=
      sub_pos.mpr (harmonicCoordinate_strictMonoOn β hz.1 ha hza')
    have hprod := mul_neg_of_pos_of_neg hH (sub_neg.mpr hw)
    rw [he, poissonTangentProfile_at_tangency ha] at hprod
    linarith
  have haz : a < z := lt_of_le_of_ne (le_of_not_gt hza') (Ne.symm hza)
  by_contra h
  have hneg : poissonTangentProfile β a z - (1 + z) ^ (-(β + 1 / 2)) < 0 := by linarith
  obtain ⟨c, hc, he⟩ := poissonDifference_harmonic_meanValue (β := β) ha ha haz
  rw [poissonTangentProfile_at_tangency ha] at he
  simp only [sub_self, sub_zero] at he
  have hH : 0 < harmonicCoordinate β z - harmonicCoordinate β a :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β ha hz.1 haz)
  have hwc : poissonWeightedSlope β c < poissonWeightedSlope β a := by
    have hp : (harmonicCoordinate β z - harmonicCoordinate β a) *
        (poissonWeightedSlope β c - poissonWeightedSlope β a) < 0 := by
      rw [he]
      exact hneg
    exact sub_neg.mp ((mul_lt_mul_iff_right₀ hH).mp (by
      simpa only [zero_mul, mul_comm] using hp))
  have hβc : 2 * β / 3 < c := by
    by_contra h
    have hw := poissonWeightedSlope_lt hβ ha hc.1 (le_of_not_gt h)
    linarith
  obtain ⟨d, hd, he'⟩ := poissonDifference_harmonic_meanValue (β := β) ha hz.1 hz.2
  rw [hjoin] at he'
  simp only [sub_self, zero_sub] at he'
  have hH' : 0 < harmonicCoordinate β b - harmonicCoordinate β z :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β hz.1 (hz.1.trans hz.2) hz.2)
  have hwd : poissonWeightedSlope β a < poissonWeightedSlope β d := by
    have hp : 0 < (harmonicCoordinate β b - harmonicCoordinate β z) *
        (poissonWeightedSlope β d - poissonWeightedSlope β a) := by
      rw [he']
      linarith
    exact sub_pos.mp ((mul_lt_mul_iff_right₀ hH').mp (by
      simpa only [zero_mul, mul_comm] using hp))
  have hwcd := poissonWeightedSlope_gt hβ hβc.le (hc.2.trans hd.1)
  linarith

private theorem poissonTangentProfile_flux_pos_of_join {β a b : ℝ}
    (hβ : 0 < β) (ha : 0 < a) (hab : a < b)
    (hjoin : poissonTangentProfile β a b = (1 + b) ^ (-(β + 1 / 2))) :
    0 < -(β + 1 / 2) * (1 + b) ^ (-(β + 3 / 2)) -
      (-(β + 1 / 2) * (1 + a) ^ (-(β + 3 / 2)) * a ^ β * b ^ (-β)) := by
  obtain ⟨c, hc, he⟩ := poissonDifference_harmonic_meanValue (β := β) ha ha hab
  rw [hjoin, poissonTangentProfile_at_tangency ha] at he
  simp only [sub_self] at he
  have hH : 0 < harmonicCoordinate β b - harmonicCoordinate β a :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β ha (ha.trans hab) hab)
  have hwc : poissonWeightedSlope β c = poissonWeightedSlope β a :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hH.ne')
  have hβc : 2 * β / 3 < c := by
    by_contra h
    have hw := poissonWeightedSlope_lt hβ ha hc.1 (le_of_not_gt h)
    linarith
  have hwb := poissonWeightedSlope_gt hβ hβc.le hc.2
  rw [hwc] at hwb
  dsimp [poissonWeightedSlope] at hwb
  rw [poissonWeightLog_exp (ha.trans hab), poissonWeightLog_exp ha] at hwb
  have hbp : 0 < b ^ (-β) := Real.rpow_pos_of_pos (ha.trans hab) _
  have hp := mul_lt_mul_of_pos_right hwb hbp
  have hcancel : (β + 1 / 2) * (b ^ β * (1 + b) ^ (-(β + 3 / 2))) * b ^ (-β) =
      (β + 1 / 2) * (1 + b) ^ (-(β + 3 / 2)) := by
    rw [Real.rpow_neg (ha.trans hab).le]
    have hbp' : b ^ β ≠ 0 := (Real.rpow_pos_of_pos (ha.trans hab) _).ne'
    field_simp
  rw [hcancel] at hp
  linarith

private theorem poissonTangentProfile_at_balance {β r a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hbalance : harmonicCoordinate β r = 1 / β) :
    poissonTangentProfile β a (r * a) = (1 - a / (2 * β)) / (1 + a) ^ (β + 3 / 2) := by
  unfold poissonTangentProfile
  rw [mul_div_cancel_right₀ _ ha.ne', hbalance, poisson_tangent_identity hβ ha]
  ring

/-- The article's exact Poisson tangency parameter exists and is unique. -/
theorem existsUnique_isPoissonTangencyParameter (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, IsPoissonTangencyParameter n a := existsUnique_poissonRoot n hn

/-- Outside dimension two the unified Poisson tangent is the power harmonic tangent. -/
theorem poissonHarmonicTangent_eq_power (n : ℕ) (hn2 : n ≠ 2) (a z : ℝ) :
    poissonHarmonicTangent n a z =
      powerHarmonicTangent ((n : ℝ) / 2) a ((1 + a) ^ (-(((n : ℝ) + 1) / 2)))
        (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2))) z := by
  have hβ : (n : ℝ) / 2 ≠ 1 := by
    intro h
    apply hn2
    exact_mod_cast (show (n : ℝ) = 2 by linarith)
  simp only [poissonHarmonicTangent, poissonTangentProfile, harmonicCoordinate, ite_eq_right hβ,
    powerHarmonicTangent]
  rw [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring,
    show (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 by ring]
  ring

/-- In dimension two the unified Poisson tangent is the logarithmic harmonic tangent. -/
theorem poissonHarmonicTangent_two (a z : ℝ) :
    poissonHarmonicTangent 2 a z =
      logHarmonicTangent a ((1 + a) ^ (-(3 / 2 : ℝ)))
        (-(3 / 2 : ℝ) * (1 + a) ^ (-(5 / 2 : ℝ))) z := by
  norm_num [poissonHarmonicTangent, poissonTangentProfile, harmonicCoordinate, logHarmonicTangent]

/-- The inner harmonic Poisson majorant has the exact weighted mass used by the article. -/
theorem integral_weighted_poissonHarmonicTangent (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    (∫ z in 0..rho n * a, poissonHarmonicTangent n a z * z ^ ((n : ℝ) / 2 - 1)) =
      2 * (rho n * a) ^ ((n : ℝ) / 2) * (1 + a) ^ (-(((n : ℝ) + 1) / 2)) / (n : ℝ) := by
  by_cases hn2 : n = 2
  · subst n
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) / 2 - 1 = 0 by norm_num,
      show (2 : ℝ) / 2 = 1 by norm_num, show ((2 : ℝ) + 1) / 2 = 3 / 2 by norm_num,
      Real.rpow_zero, Real.rpow_one, mul_one]
    simp_rw [poissonHarmonicTangent_two]
    rw [integral_logHarmonicTangent_rho ha]
    ring
  · simp_rw [poissonHarmonicTangent_eq_power n hn2]
    exact integral_powerHarmonicTangent_rho n hn hn2 ha _ _

/-- The exact Poisson root makes the tangent continuous at the outer joining radius. -/
theorem poissonHarmonicTangent_join (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a)
    (hroot : IsPoissonTangencyParameter n a) :
    poissonHarmonicTangent n a (rho n * a) =
      (1 + rho n * a) ^ (-(((n : ℝ) + 1) / 2)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hβ : 0 < (n : ℝ) / 2 := by positivity
  have hbalance : harmonicCoordinate ((n : ℝ) / 2) (rho n) = 1 / ((n : ℝ) / 2) := by
    simpa only [one_div, inv_div] using harmonicCoordinate_rho n hn
  have hb : 0 < 1 + rho n * a := by have hr0 := rho_pos n hn; positivity
  calc
    _ = (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) := by
      simpa only [poissonHarmonicTangent, show 2 * ((n : ℝ) / 2) = (n : ℝ) by ring,
        show (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 by ring] using
        poissonTangentProfile_at_balance hβ ha hbalance
    _ = 1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2) := hroot.2
    _ = _ := by rw [Real.rpow_neg hb.le, one_div]

/-- The harmonic Poisson tangent dominates the Poisson profile throughout its inner region. -/
theorem poissonHarmonicTangent_majorizes (n : ℕ) (hn : 1 ≤ n) {a z : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (hz : z ∈ Ioo 0 (rho n * a)) :
    (1 + z) ^ (-(((n : ℝ) + 1) / 2)) ≤ poissonHarmonicTangent n a z := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hab : a < rho n * a := by nlinarith [one_lt_rho n hn]
  have haβ : a < 2 * ((n : ℝ) / 2) / 3 := by
    rw [show 2 * ((n : ℝ) / 2) = (n : ℝ) by ring]
    exact hroot.1.2
  have hjoin : poissonTangentProfile ((n : ℝ) / 2) a (rho n * a) =
      (1 + rho n * a) ^ (-((n : ℝ) / 2 + 1 / 2)) := by
    simpa only [poissonHarmonicTangent,
      show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring] using
      poissonHarmonicTangent_join n hn ha hroot
  simpa only [poissonHarmonicTangent,
    show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring] using
    poissonTangentProfile_majorizes_of_join (by positivity) ha haβ hab hjoin hz

/-- The joined profile dominates the Poisson profile at every positive squared radius. -/
theorem poissonMajorantProfile_majorizes (n : ℕ) (hn : 1 ≤ n) {a z : ℝ}
    (hroot : IsPoissonTangencyParameter n a) (hz : 0 < z) :
    (1 + z) ^ (-(((n : ℝ) + 1) / 2)) ≤ poissonMajorantProfile n a z := by
  unfold poissonMajorantProfile
  split_ifs with hb
  · exact poissonHarmonicTangent_majorizes n hn hroot ⟨hz, hb⟩
  · exact le_rfl

/-- The inner Poisson tangent has the harmonic derivative at every positive squared radius. -/
theorem hasDerivAt_poissonHarmonicTangent (n : ℕ) {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (poissonHarmonicTangent n a)
      (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2)) *
        a ^ ((n : ℝ) / 2) * z ^ (-((n : ℝ) / 2))) z := by
  change HasDerivAt (poissonTangentProfile ((n : ℝ) / 2) a) _ z
  simpa only [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring,
    show (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 by ring] using
    hasDerivAt_poissonTangentProfile (β := (n : ℝ) / 2) ha hz

/-- The outward squared-radius derivative has a strictly positive jump at the joining radius. -/
theorem poissonHarmonicTangent_flux_jump_pos (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsPoissonTangencyParameter n a) :
    0 < -(((n : ℝ) + 1) / 2) * (1 + rho n * a) ^ (-(((n : ℝ) + 3) / 2)) -
      (-(((n : ℝ) + 1) / 2) * (1 + a) ^ (-(((n : ℝ) + 3) / 2)) *
        a ^ ((n : ℝ) / 2) * (rho n * a) ^ (-((n : ℝ) / 2))) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hab : a < rho n * a := by nlinarith [one_lt_rho n hn]
  have hjoin : poissonTangentProfile ((n : ℝ) / 2) a (rho n * a) =
      (1 + rho n * a) ^ (-((n : ℝ) / 2 + 1 / 2)) := by
    simpa only [poissonHarmonicTangent,
      show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring] using
      poissonHarmonicTangent_join n hn ha hroot
  simpa only [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring,
    show (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 by ring] using
    poissonTangentProfile_flux_pos_of_join (by positivity) ha hab hjoin

end PartialBalayage
