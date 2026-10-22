/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import PartialBalayage.Maximal.RadialTangentMass

/-!
# Harmonic majorization of the heat profile

In squared-radius coordinates, the heat profile is `exp (-z)`. Its harmonic tangent at the
article's exact heat root dominates the profile until the balanced outer joining radius.
The outward derivative increases at that joining radius. These are scalar profile facts;
they do not yet assert a distributional inequality or a maximal-operator bound.
-/

@[expose] public section

noncomputable section

open Set
open PartialBalayage.Constants

namespace PartialBalayage

/-- The harmonic tangent with radial exponent `β`, before specializing the dimension. -/
def heatTangentProfile (β a z : ℝ) : ℝ :=
  Real.exp (-a) * (1 - a * harmonicCoordinate β (z / a))

/-- The radial harmonic tangent to the heat profile in squared-radius coordinates. -/
def heatHarmonicTangent (n : ℕ) (a z : ℝ) : ℝ := heatTangentProfile ((n : ℝ) / 2) a z

/-- The tangent inside the outer joining radius and the original heat profile outside. -/
def heatMajorantProfile (n : ℕ) (a z : ℝ) : ℝ :=
  if z < rho n * a then heatHarmonicTangent n a z else Real.exp (-z)

private theorem heatTangentProfile_at_tangency {β a : ℝ} (ha : 0 < a) :
    heatTangentProfile β a a = Real.exp (-a) := by
  simp [heatTangentProfile, ha.ne', harmonicCoordinate_one]

private theorem hasDerivAt_heatTangentProfile {β a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (heatTangentProfile β a) (-Real.exp (-a) * a ^ β * z ^ (-β)) z := by
  have hd := (hasDerivAt_harmonicCoordinate (β := β) (div_pos hz ha)).comp z
    ((hasDerivAt_id z).div_const a)
  convert ((hasDerivAt_const z (1 : ℝ)).sub (hd.const_mul a)).const_mul
    (Real.exp (-a)) using 1
  · rfl
  · rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul]
    field_simp
    ring

private def heatWeightLog (β z : ℝ) : ℝ := β * Real.log z - z

private theorem hasDerivAt_heatWeightLog {β z : ℝ} (hz : 0 < z) :
    HasDerivAt (heatWeightLog β) ((β - z) / z) z := by
  convert ((Real.hasDerivAt_log hz.ne').const_mul β).sub (hasDerivAt_id z) using 1
  · rfl
  · field_simp

private theorem heatWeightLog_lt {β x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ β) :
    heatWeightLog β x < heatWeightLog β y := by
  have hc : ContinuousOn (heatWeightLog β) (Icc x y) := fun z hz ↦
    ((hasDerivAt_heatWeightLog (β := β) (hx.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope (heatWeightLog β)
    (fun z ↦ (β - z) / z) hxy hc
    (fun z hz ↦ hasDerivAt_heatWeightLog (hx.trans hz.1))
  have hder : 0 < (β - z) / z := div_pos (by linarith [hz.2]) (hx.trans hz.1)
  rw [he] at hder
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hxy)).mp hder)

private theorem heatWeightLog_gt {β x y : ℝ} (hx0 : 0 < x) (hx : β ≤ x)
    (hxy : x < y) : heatWeightLog β y < heatWeightLog β x := by
  have hc : ContinuousOn (heatWeightLog β) (Icc x y) := fun z hz ↦
    ((hasDerivAt_heatWeightLog (β := β) (hx0.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope (heatWeightLog β)
    (fun z ↦ (β - z) / z) hxy hc
    (fun z hz ↦ hasDerivAt_heatWeightLog (hx0.trans hz.1))
  have hder : (β - z) / z < 0 :=
    div_neg_of_neg_of_pos (by linarith [hz.1]) (hx0.trans hz.1)
  rw [he] at hder
  have hnum := (div_lt_iff₀ (sub_pos.mpr hxy)).mp hder
  simpa only [zero_mul, sub_neg] using hnum

private theorem heatWeightLog_exp {β z : ℝ} (hz : 0 < z) :
    Real.exp (heatWeightLog β z) = z ^ β * Real.exp (-z) := by
  rw [Real.rpow_def_of_pos hz, ← Real.exp_add]
  congr 1
  dsimp [heatWeightLog]
  ring

private theorem harmonicCoordinate_strictMonoOn (β : ℝ) :
    StrictMonoOn (harmonicCoordinate β) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro z hz
    exact ((hasDerivAt_harmonicCoordinate (β := β) hz).continuousAt).continuousWithinAt
  · intro z hz
    have hz0 : 0 < z := by simpa using hz
    rw [(hasDerivAt_harmonicCoordinate (β := β) hz0).deriv]
    exact Real.rpow_pos_of_pos hz0 _

private theorem heatDifference_harmonic_meanValue {β a x y : ℝ} (ha : 0 < a)
    (hx : 0 < x) (hxy : x < y) :
    ∃ c ∈ Ioo x y,
      (harmonicCoordinate β y - harmonicCoordinate β x) *
          (Real.exp (heatWeightLog β c) - Real.exp (heatWeightLog β a)) =
        (heatTangentProfile β a y - Real.exp (-y)) -
          (heatTangentProfile β a x - Real.exp (-x)) := by
  let f : ℝ → ℝ := fun z ↦ heatTangentProfile β a z - Real.exp (-z)
  let d : ℝ → ℝ := fun z ↦
    (Real.exp (heatWeightLog β z) - Real.exp (heatWeightLog β a)) * z ^ (-β)
  have hd : ∀ z ∈ Icc x y, HasDerivAt f (d z) z := by
    intro z hz
    have hz0 : 0 < z := hx.trans_le hz.1
    convert (hasDerivAt_heatTangentProfile ha hz0).sub
      ((hasDerivAt_id z).neg.exp) using 1
    · rfl
    · dsimp [d]
      rw [heatWeightLog_exp hz0, heatWeightLog_exp ha,
        Real.rpow_neg hz0.le]
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

private theorem heatTangentProfile_majorizes_of_join {β a b z : ℝ}
    (ha : 0 < a) (haβ : a < β) (_hab : a < b)
    (hjoin : heatTangentProfile β a b = Real.exp (-b)) (hz : z ∈ Ioo 0 b) :
    Real.exp (-z) ≤ heatTangentProfile β a z := by
  by_cases hza : z = a
  · subst z
    exact (heatTangentProfile_at_tangency ha).ge
  by_cases hza' : z < a
  · obtain ⟨c, hc, he⟩ := heatDifference_harmonic_meanValue (β := β) ha hz.1 hza'
    have hw := Real.exp_lt_exp.mpr (heatWeightLog_lt (hz.1.trans hc.1) hc.2 haβ.le)
    have hH : 0 < harmonicCoordinate β a - harmonicCoordinate β z :=
      sub_pos.mpr (harmonicCoordinate_strictMonoOn β hz.1 ha hza')
    have hprod := mul_neg_of_pos_of_neg hH (sub_neg.mpr hw)
    rw [he, heatTangentProfile_at_tangency ha] at hprod
    linarith
  have haz : a < z := lt_of_le_of_ne (le_of_not_gt hza') (Ne.symm hza)
  by_contra h
  have hneg : heatTangentProfile β a z - Real.exp (-z) < 0 := by linarith
  obtain ⟨c, hc, he⟩ := heatDifference_harmonic_meanValue (β := β) ha ha haz
  rw [heatTangentProfile_at_tangency ha] at he
  simp only [sub_self, sub_zero] at he
  have hH : 0 < harmonicCoordinate β z - harmonicCoordinate β a :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β ha hz.1 haz)
  have hwc : Real.exp (heatWeightLog β c) < Real.exp (heatWeightLog β a) := by
    have hp : (harmonicCoordinate β z - harmonicCoordinate β a) *
        (Real.exp (heatWeightLog β c) - Real.exp (heatWeightLog β a)) < 0 := by
      rw [he]
      exact hneg
    exact sub_neg.mp ((mul_lt_mul_iff_right₀ hH).mp (by
      simpa only [zero_mul, mul_comm] using hp))
  have hβc : β < c := by
    by_contra h
    have hw := Real.exp_lt_exp.mpr (heatWeightLog_lt ha hc.1 (le_of_not_gt h))
    linarith
  obtain ⟨d, hd, he'⟩ := heatDifference_harmonic_meanValue (β := β) ha hz.1 hz.2
  rw [hjoin] at he'
  simp only [sub_self, zero_sub] at he'
  have hH' : 0 < harmonicCoordinate β b - harmonicCoordinate β z :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β hz.1 (hz.1.trans hz.2) hz.2)
  have hwd : Real.exp (heatWeightLog β a) < Real.exp (heatWeightLog β d) := by
    have hp : 0 < (harmonicCoordinate β b - harmonicCoordinate β z) *
        (Real.exp (heatWeightLog β d) - Real.exp (heatWeightLog β a)) := by
      rw [he']
      linarith
    exact sub_pos.mp ((mul_lt_mul_iff_right₀ hH').mp (by
      simpa only [zero_mul, mul_comm] using hp))
  have hwcd := Real.exp_lt_exp.mpr
    (heatWeightLog_gt (ha.trans hc.1) hβc.le (hc.2.trans hd.1))
  linarith

private theorem heatTangentProfile_flux_pos_of_join {β a b : ℝ}
    (ha : 0 < a) (_haβ : a < β) (hab : a < b)
    (hjoin : heatTangentProfile β a b = Real.exp (-b)) :
    0 < -Real.exp (-b) - (-Real.exp (-a) * a ^ β * b ^ (-β)) := by
  obtain ⟨c, hc, he⟩ := heatDifference_harmonic_meanValue (β := β) ha ha hab
  rw [hjoin, heatTangentProfile_at_tangency ha] at he
  simp only [sub_self] at he
  have hH : 0 < harmonicCoordinate β b - harmonicCoordinate β a :=
    sub_pos.mpr (harmonicCoordinate_strictMonoOn β ha (ha.trans hab) hab)
  have hwc : Real.exp (heatWeightLog β c) = Real.exp (heatWeightLog β a) :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hH.ne')
  have hβc : β < c := by
    by_contra h
    have hw := Real.exp_lt_exp.mpr (heatWeightLog_lt ha hc.1 (le_of_not_gt h))
    linarith
  have hwb := Real.exp_lt_exp.mpr (heatWeightLog_gt (ha.trans hc.1) hβc.le hc.2)
  rw [hwc, heatWeightLog_exp (ha.trans hab), heatWeightLog_exp ha] at hwb
  have hbp : 0 < b ^ (-β) := Real.rpow_pos_of_pos (ha.trans hab) _
  have hp := mul_lt_mul_of_pos_right hwb hbp
  have hcancel : b ^ β * Real.exp (-b) * b ^ (-β) = Real.exp (-b) := by
    rw [Real.rpow_neg (ha.trans hab).le]
    have hbp' : b ^ β ≠ 0 := (Real.rpow_pos_of_pos (ha.trans hab) _).ne'
    field_simp
  rw [hcancel] at hp
  linarith

/-- The article's exact heat tangency parameter exists and is unique. -/
theorem existsUnique_isHeatTangencyParameter (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, IsHeatTangencyParameter n a := existsUnique_heatRoot n hn

/-- Outside dimension two the unified heat tangent is the power harmonic tangent. -/
theorem heatHarmonicTangent_eq_power (n : ℕ) (hn2 : n ≠ 2) (a z : ℝ) :
    heatHarmonicTangent n a z =
      powerHarmonicTangent ((n : ℝ) / 2) a (Real.exp (-a)) (-Real.exp (-a)) z := by
  have hβ : (n : ℝ) / 2 ≠ 1 := by
    intro h
    apply hn2
    exact_mod_cast (show (n : ℝ) = 2 by linarith)
  simp only [heatHarmonicTangent, heatTangentProfile, harmonicCoordinate, ite_eq_right hβ,
    powerHarmonicTangent]
  ring

/-- In dimension two the unified heat tangent is the logarithmic harmonic tangent. -/
theorem heatHarmonicTangent_two (a z : ℝ) :
    heatHarmonicTangent 2 a z =
      logHarmonicTangent a (Real.exp (-a)) (-Real.exp (-a)) z := by
  norm_num [heatHarmonicTangent, heatTangentProfile, harmonicCoordinate, logHarmonicTangent]
  ring

/-- The power case agrees with the explicit heat majorant formula in the article. -/
theorem heatHarmonicTangent_power_formula (n : ℕ) (hn2 : n ≠ 2) (a z : ℝ) :
    heatHarmonicTangent n a z = Real.exp (-a) *
      (1 + 2 * a / ((n : ℝ) - 2) * ((z / a) ^ (1 - (n : ℝ) / 2) - 1)) := by
  have hn2R : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn2)
  have hden : 1 - (n : ℝ) / 2 ≠ 0 := by
    intro h
    apply hn2R
    linarith
  have hden' : (2 : ℝ) - n ≠ 0 := by
    intro h
    apply hn2R
    linarith
  rw [heatHarmonicTangent_eq_power n hn2]
  unfold powerHarmonicTangent
  have hc : a * -Real.exp (-a) / (1 - (n : ℝ) / 2) =
      Real.exp (-a) * (2 * a / ((n : ℝ) - 2)) := by
    field_simp
    ring
  rw [hc]
  ring

/-- The planar case agrees with the article's logarithmic heat majorant formula. -/
theorem heatHarmonicTangent_log_formula (a z : ℝ) :
    heatHarmonicTangent 2 a z = Real.exp (-a) * (1 - a * Real.log (z / a)) := by
  rw [heatHarmonicTangent_two]
  unfold logHarmonicTangent
  ring

/-- The inner harmonic heat majorant has the exact weighted mass used by the article. -/
theorem integral_weighted_heatHarmonicTangent (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    (∫ z in 0..rho n * a, heatHarmonicTangent n a z * z ^ ((n : ℝ) / 2 - 1)) =
      2 * (rho n * a) ^ ((n : ℝ) / 2) * Real.exp (-a) / (n : ℝ) := by
  by_cases hn2 : n = 2
  · subst n
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) / 2 - 1 = 0 by norm_num,
      show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_zero, Real.rpow_one, mul_one]
    simp_rw [heatHarmonicTangent_two]
    rw [integral_logHarmonicTangent_rho ha]
    ring
  · simp_rw [heatHarmonicTangent_eq_power n hn2]
    exact integral_powerHarmonicTangent_rho n hn hn2 ha _ _

/-- The exact heat root makes the tangent continuous at the outer joining radius. -/
theorem heatHarmonicTangent_join (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a)
    (hroot : IsHeatTangencyParameter n a) :
    heatHarmonicTangent n a (rho n * a) = Real.exp (-(rho n * a)) := by
  unfold heatHarmonicTangent heatTangentProfile
  rw [mul_div_cancel_right₀ _ ha.ne', harmonicCoordinate_rho n hn]
  have hid : a * (2 / (n : ℝ)) = 2 * a / (n : ℝ) := by ring
  rw [hid, ← hroot.2, ← Real.exp_add]
  congr 1
  ring

/-- The harmonic heat tangent dominates the heat profile throughout its inner region. -/
theorem heatHarmonicTangent_majorizes (n : ℕ) (hn : 1 ≤ n) {a z : ℝ}
    (hroot : IsHeatTangencyParameter n a) (hz : z ∈ Ioo 0 (rho n * a)) :
    Real.exp (-z) ≤ heatHarmonicTangent n a z := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hab : a < rho n * a := by nlinarith [one_lt_rho n hn]
  exact heatTangentProfile_majorizes_of_join ha hroot.1.2 hab
    (heatHarmonicTangent_join n hn ha hroot) hz

/-- The joined profile dominates the heat profile at every positive squared radius. -/
theorem heatMajorantProfile_majorizes (n : ℕ) (hn : 1 ≤ n) {a z : ℝ}
    (hroot : IsHeatTangencyParameter n a) (hz : 0 < z) :
    Real.exp (-z) ≤ heatMajorantProfile n a z := by
  unfold heatMajorantProfile
  split_ifs with hb
  · exact heatHarmonicTangent_majorizes n hn hroot ⟨hz, hb⟩
  · exact le_rfl

/-- The inner tangent has the harmonic radial derivative at every positive squared radius. -/
theorem hasDerivAt_heatHarmonicTangent (n : ℕ) {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (heatHarmonicTangent n a)
      (-Real.exp (-a) * a ^ ((n : ℝ) / 2) * z ^ (-((n : ℝ) / 2))) z :=
  hasDerivAt_heatTangentProfile ha hz

/-- The outward squared-radius derivative has a strictly positive jump at the joining radius. -/
theorem heatHarmonicTangent_flux_jump_pos (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (hroot : IsHeatTangencyParameter n a) :
    0 < -Real.exp (-(rho n * a)) -
      (-Real.exp (-a) * a ^ ((n : ℝ) / 2) * (rho n * a) ^ (-((n : ℝ) / 2))) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have ha : 0 < a := lt_trans (by positivity) hroot.1.1
  have hab : a < rho n * a := by nlinarith [one_lt_rho n hn]
  exact heatTangentProfile_flux_pos_of_join ha hroot.1.2 hab
    (heatHarmonicTangent_join n hn ha hroot)

end PartialBalayage
