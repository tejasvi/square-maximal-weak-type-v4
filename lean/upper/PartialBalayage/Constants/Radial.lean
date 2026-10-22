/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.TableDefinitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Parameters for radial harmonic majorants

The dimension parameter `rho` gives the ratio of the joining radius squared to the
tangency radius squared for the Poisson and heat majorants.
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PartialBalayage.Constants

/-- In dimension one the squared-radius ratio is four. -/
theorem rho_one : rho 1 = 4 := by
  norm_num [rho, Real.rpow_neg_natCast]

/-- The logarithmic planar majorant has squared-radius ratio `exp 1`. -/
theorem rho_two : rho 2 = Real.exp 1 := by
  simp [rho]

/-- Every positive dimension has a positive radial ratio. -/
theorem rho_pos (n : ℕ) (hn : 1 ≤ n) : 0 < rho n := by
  unfold rho
  split_ifs
  · exact Real.exp_pos _
  · apply Real.rpow_pos_of_pos
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity

/-- The outer joining radius exceeds the tangency radius in every positive dimension. -/
theorem one_lt_rho (n : ℕ) (hn : 1 ≤ n) : 1 < rho n := by
  rcases eq_or_lt_of_le hn with hn | hn
  · subst n
    norm_num [rho_one]
  · by_cases hn2 : n = 2
    · rw [hn2, rho_two]
      exact Real.one_lt_exp_iff.mpr zero_lt_one
    · have hn3 : 3 ≤ n := by omega
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      simp only [rho, ite_eq_right hn2]
      exact Real.one_lt_rpow (by linarith) (div_pos (by norm_num) (by linarith))

/-- The radial parameter is characterized by the harmonic exponent outside dimension two. -/
theorem rho_rpow_one_sub_half (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≠ 2) :
    rho n ^ (1 - (n : ℝ) / 2) = 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn2)
  simp only [rho, ite_eq_right hn2]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) / 2)]
  have he : 2 / ((n : ℝ) - 2) * (1 - (n : ℝ) / 2) = -1 := by
    field_simp
    ring
  rw [he, Real.rpow_neg_one]
  field_simp

/-- The heat root equation initially decreases from its zero at the origin. -/
theorem one_add_two_div_lt_rho (n : ℕ) (hn : 1 ≤ n) : 1 + 2 / (n : ℝ) < rho n := by
  rcases eq_or_lt_of_le hn with hn | hn
  · subst n
    norm_num [rho_one]
  · by_cases hn2 : n = 2
    · subst n
      simpa [rho_two] using Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    · have hn3 : 3 ≤ n := by omega
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hn0 : (0 : ℝ) < n := by linarith
      have hbase : 0 < (n : ℝ) / 2 := by positivity
      have hlog : 1 - 2 / (n : ℝ) ≤ Real.log ((n : ℝ) / 2) := by
        simpa only [inv_div] using Real.one_sub_inv_le_log_of_pos hbase
      have ht : 2 / (n : ℝ) ≤ Real.log ((n : ℝ) / 2) * (2 / ((n : ℝ) - 2)) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ (by linarith : (0 : ℝ) < n - 2)).mpr
        have he : 2 / (n : ℝ) * ((n : ℝ) - 2) = 2 * (1 - 2 / (n : ℝ)) := by
          field_simp
        rw [he]
        nlinarith
      rw [rho, ite_eq_right hn2, Real.rpow_def_of_pos hbase]
      have hexp : 1 + 2 / (n : ℝ) < Real.exp (2 / (n : ℝ)) := by
        simpa [add_comm] using Real.add_one_lt_exp (by positivity : 2 / (n : ℝ) ≠ 0)
      exact hexp.trans_le (Real.exp_le_exp.mpr ht)

/-- An exponential curve meets an affine line through `(0, 1)` at at most one positive point. -/
theorem eq_of_exp_affine_eq {c d x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hex : Real.exp (-c * x) = 1 - d * x)
    (hey : Real.exp (-c * y) = 1 - d * y) : x = y := by
  wlog hxy : x < y generalizing x y
  · rcases lt_trichotomy x y with h | h | h
    · exact this hx hy hex hey h
    · exact h
    · exact (this hy hx hey hex h).symm
  have hcx : -c * x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc.ne') hx.ne'
  have hcy : -c * y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc.ne') hy.ne'
  have h := strictConvexOn_exp.secant_strict_mono
    (a := 0) (x := -c * y) (y := -c * x) (by simp) (by simp) (by simp)
    hcy hcx (by nlinarith)
  simp only [Real.exp_zero, sub_zero, hex, hey] at h
  have h₁ : (1 - d * y - 1) / (-c * y) = d / c := by
    field_simp
    ring
  have h₂ : (1 - d * x - 1) / (-c * x) = d / c := by
    field_simp
    ring
  rw [h₁, h₂] at h
  exact (lt_irrefl _ h).elim

/-- Opposite endpoint signs locate the unique positive exponential-affine intersection. -/
theorem existsUnique_exp_affine_eq_of_signs {c d l r : ℝ} (hc : 0 < c)
    (hl : 0 < l) (hlr : l < r)
    (hlneg : Real.exp (-c * l) < 1 - d * l)
    (hrpos : 1 - d * r < Real.exp (-c * r)) :
    ∃! a : ℝ, a ∈ Ioo l r ∧ Real.exp (-c * a) = 1 - d * a := by
  let F : ℝ → ℝ := fun a ↦ Real.exp (-c * a) - (1 - d * a)
  have hF : Continuous F := by fun_prop
  obtain ⟨a, ha, he⟩ := intermediate_value_Ioo hlr.le hF.continuousOn
    (show 0 ∈ Ioo (F l) (F r) by constructor <;> dsimp [F] <;> linarith)
  have heq : Real.exp (-c * a) = 1 - d * a := sub_eq_zero.mp he
  refine ⟨a, ⟨ha, heq⟩, fun b hb ↦ ?_⟩
  exact eq_of_exp_affine_eq hc (hl.trans hb.1.1) (hl.trans ha.1) hb.2 heq

private theorem exists_neg_of_hasDerivAt_neg {F : ℝ → ℝ} {D R : ℝ}
    (hF : HasDerivAt F D 0) (hF0 : F 0 = 0) (hD : D < 0) (hR : 0 < R) :
    ∃ a ∈ Ioo 0 R, F a < 0 := by
  have hneg : ∀ᶠ a in 𝓝 (0 : ℝ),
      Function.update (fun x ↦ (F x - F 0) / (x - 0)) 0 D a < 0 :=
    hF.continuousAt_div.tendsto.eventually (by simpa using eventually_lt_nhds hD)
  have hneg' := hneg.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  obtain ⟨a, ha, haR, haneg⟩ := (hpos.and (hsmall.and hneg')).exists
  rw [Function.update_of_ne ha.ne', hF0, sub_zero, sub_zero] at haneg
  exact ⟨a, ⟨ha, haR⟩, by simpa using (div_lt_iff₀ ha).mp haneg⟩

/-- If the exponential initially falls faster than the affine line, their positive
intersection exists and lies before the affine line becomes zero. -/
theorem existsUnique_exp_affine_eq {c d : ℝ} (hd : 0 < d) (hdc : d < c) :
    ∃! a : ℝ, a ∈ Ioo 0 d⁻¹ ∧ Real.exp (-c * a) = 1 - d * a := by
  let F : ℝ → ℝ := fun a ↦ Real.exp (-c * a) - (1 - d * a)
  have hderiv : HasDerivAt F (d - c) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-c)).exp).sub
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).const_mul d))
      using 1
    · ext a
      simp [F]
    · simp
      ring
  obtain ⟨l, hl, hlneg⟩ := exists_neg_of_hasDerivAt_neg hderiv (by simp [F])
    (by linarith) (inv_pos.mpr hd)
  obtain ⟨a, ha, -⟩ := existsUnique_exp_affine_eq_of_signs (d := d) (hd.trans hdc) hl.1 hl.2
    (by dsimp [F] at hlneg; linarith)
    (by simp [hd.ne', Real.exp_pos])
  exact ⟨a, ⟨⟨hl.1.trans ha.1.1, ha.1.2⟩, ha.2⟩,
    fun b hb ↦ eq_of_exp_affine_eq (hd.trans hdc) hb.1.1 (hl.1.trans ha.1.1) hb.2 ha.2⟩

/-- In every positive dimension the heat tangency equation has exactly one positive root
before `n / 2`. -/
theorem existsUnique_heatRoot_positive (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, a ∈ Ioo 0 ((n : ℝ) / 2) ∧
      Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd : 0 < 2 / (n : ℝ) := by positivity
  have hdc : 2 / (n : ℝ) < rho n - 1 := by linarith [one_add_two_div_lt_rho n hn]
  simpa only [inv_div, div_mul_eq_mul_div] using existsUnique_exp_affine_eq hd hdc

/-- The one-dimensional Poisson equation has the exact tangency parameter `1 / 5`. -/
theorem existsUnique_poissonRoot_one :
    ∃! a : ℝ, a ∈ Ioo (1 / 12) (1 / 3) ∧
      (1 - a) / (1 + a) ^ 2 = 1 / (1 + 4 * a) := by
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro a ha
  have ha0 : 0 < a := by linarith [ha.1.1]
  have h₁ : 1 + a ≠ 0 := by positivity
  have h₂ : 1 + 4 * a ≠ 0 := by positivity
  have he := ha.2
  field_simp at he
  have hf : a * (1 - 5 * a) = 0 := by nlinarith
  have h := (mul_eq_zero.mp hf).resolve_left ha0.ne'
  linarith

/-- A primitive of the positive radial harmonic weight `z^(-β)`. -/
def harmonicCoordinate (β z : ℝ) : ℝ :=
  if β = 1 then Real.log z else (z ^ (1 - β) - 1) / (1 - β)

/-- The harmonic coordinate is normalized to vanish at one. -/
theorem harmonicCoordinate_one (β : ℝ) : harmonicCoordinate β 1 = 0 := by
  by_cases hβ : β = 1 <;> simp [harmonicCoordinate, hβ]

/-- Differentiating the harmonic coordinate recovers its positive radial weight. -/
theorem hasDerivAt_harmonicCoordinate {β z : ℝ} (hz : 0 < z) :
    HasDerivAt (harmonicCoordinate β) (z ^ (-β)) z := by
  by_cases hβ : β = 1
  · subst β
    unfold harmonicCoordinate
    simpa [Real.rpow_neg_one] using Real.hasDerivAt_log hz.ne'
  · have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
    have hder := Real.hasDerivAt_rpow_const (p := 1 - β) (Or.inl hz.ne')
    convert (hder.sub_const 1).div_const (1 - β) using 1
    · funext x
      simp [harmonicCoordinate, hβ]
    · rw [show 1 - β - 1 = -β by ring, mul_div_cancel_left₀ _ hβ']

private theorem exp_neg_ratio_mul_lt_rpow {β r z : ℝ} (hβ : 0 < β)
    (hz1 : 1 < z) (hzr : z < r) :
    z ^ (-β) < Real.exp (-(β / r) * (z - 1)) := by
  have hz0 : 0 < z := zero_lt_one.trans hz1
  have hr0 : 0 < r := hz0.trans hzr
  have hlog := Real.one_sub_inv_le_log_of_pos hz0
  have hid : β * (1 - z⁻¹) = β * (z - 1) / z := by
    field_simp
  have hlt : β / r * (z - 1) < β * (1 - z⁻¹) := by
    rw [hid, div_mul_eq_mul_div]
    exact div_lt_div_of_pos_left (mul_pos hβ (sub_pos.mpr hz1)) hz0 hzr
  have hlt' := hlt.trans_le (mul_le_mul_of_nonneg_left hlog hβ.le)
  rw [Real.rpow_def_of_pos hz0]
  apply Real.exp_lt_exp.mpr
  nlinarith

private theorem exp_neg_harmonicRatio_lt {β r : ℝ} (hβ : 0 < β) (hr : 1 < r)
    (hbalance : harmonicCoordinate β r = 1 / β) :
    Real.exp (-(β / r) * (r - 1)) < 1 - 1 / r := by
  let a : ℝ := β / r
  let f : ℝ → ℝ := fun z ↦ Real.exp (-a * (z - 1))
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hf : Continuous f := by fun_prop
  have hdf : ∀ z ∈ Ioo 1 r, HasDerivAt f (-a * f z) z := by
    intro z hz
    simpa [f, mul_comm] using (((hasDerivAt_id z).sub_const 1).const_mul (-a)).exp
  have hg : ContinuousOn (harmonicCoordinate β) (Icc 1 r) := by
    intro z hz
    exact ((hasDerivAt_harmonicCoordinate (β := β)
      (zero_lt_one.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f (fun z ↦ -a * f z)
    hr hf.continuousOn hdf (harmonicCoordinate β) (fun z ↦ z ^ (-β)) hg
    (fun z hz ↦ hasDerivAt_harmonicCoordinate (zero_lt_one.trans hz.1))
  simp only [hbalance, harmonicCoordinate_one, sub_zero] at he
  have hf1 : f 1 = 1 := by simp [f]
  rw [hf1] at he
  have hpower : z ^ (-β) < f z := exp_neg_ratio_mul_lt_rpow hβ hz.1 hz.2
  have hpower0 : 0 < z ^ (-β) := Real.rpow_pos_of_pos (zero_lt_one.trans hz.1) _
  have hrewrite : 1 / β * (-a * f z) = -(1 / r) * f z := by
    dsimp [a]
    field_simp
  rw [hrewrite] at he
  have hmul := mul_lt_mul_of_pos_left hpower (one_div_pos.mpr hr0)
  change f r < 1 - 1 / r
  by_contra h
  have hnonneg : 0 ≤ f r - 1 + 1 / r := by linarith
  have hprod := mul_nonneg hnonneg hpower0.le
  nlinarith

/-- The article's radius ratio has harmonic coordinate `2 / n`. -/
theorem harmonicCoordinate_rho (n : ℕ) (hn : 1 ≤ n) :
    harmonicCoordinate ((n : ℝ) / 2) (rho n) = 2 / (n : ℝ) := by
  by_cases hn2 : n = 2
  · subst n
    norm_num [harmonicCoordinate, rho_two, Real.log_exp]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hβ : (n : ℝ) / 2 ≠ 1 := by
      intro h
      apply hn2
      exact_mod_cast (show (n : ℝ) = 2 by linarith)
    have hden : 1 - (n : ℝ) / 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
    have hden' : (2 : ℝ) - n ≠ 0 := by
      intro h
      apply hβ
      linarith
    rw [harmonicCoordinate, ite_eq_right hβ, rho_rpow_one_sub_half n hn hn2]
    field_simp

/-- At the lower endpoint stated in the article, the exponential lies below the affine line. -/
theorem heatRoot_lower_endpoint_neg (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-(rho n - 1) * ((n : ℝ) / (2 * rho n))) < 1 - 1 / rho n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have hβ : 0 < (n : ℝ) / 2 := by positivity
  have hbalance : harmonicCoordinate ((n : ℝ) / 2) (rho n) = 1 / ((n : ℝ) / 2) := by
    simpa only [one_div, inv_div] using harmonicCoordinate_rho n hn
  convert exp_neg_harmonicRatio_lt hβ (one_lt_rho n hn) hbalance using 1
  congr 1
  field_simp

/-- The heat tangency equation has its unique nonzero root in the article's precise interval. -/
theorem existsUnique_heatRoot (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, a ∈ Ioo ((n : ℝ) / (2 * rho n)) ((n : ℝ) / 2) ∧
      Real.exp (-(rho n - 1) * a) = 1 - 2 * a / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have hrl : 1 < rho n := one_lt_rho n hn
  have hc : 0 < rho n - 1 := by linarith
  have hl : 0 < (n : ℝ) / (2 * rho n) := by positivity
  have hlr : (n : ℝ) / (2 * rho n) < (n : ℝ) / 2 :=
    div_lt_div_of_pos_left hn0 (by norm_num) (by linarith)
  have hid : 2 / (n : ℝ) * ((n : ℝ) / (2 * rho n)) = 1 / rho n := by
    field_simp
  have hr : 1 - 2 / (n : ℝ) * ((n : ℝ) / 2) <
      Real.exp (-(rho n - 1) * ((n : ℝ) / 2)) := by
    have hid' : 2 / (n : ℝ) * ((n : ℝ) / 2) = 1 := by field_simp
    rw [hid', sub_self]
    exact Real.exp_pos _
  simpa only [div_mul_eq_mul_div] using existsUnique_exp_affine_eq_of_signs
    (d := 2 / (n : ℝ)) hc hl hlr (by rw [hid]; exact heatRoot_lower_endpoint_neg n hn) hr

private def poissonLogProfile (N r a : ℝ) : ℝ :=
  Real.log (1 - a / N) - (N + 3) / 2 * Real.log (1 + a) +
    (N + 1) / 2 * Real.log (1 + r * a)

private theorem hasDerivAt_poissonLogProfile {N r a : ℝ} (hN : 0 < N)
    (hr : 0 < r) (ha : a ∈ Ico 0 N) :
    HasDerivAt (poissonLogProfile N r)
      (((N + 1) / 2) * (N * r - N - 2 + (1 - 3 * r) * a) /
        ((N - a) * (1 + a) * (1 + r * a))) a := by
  have h₁ : 0 < 1 - a / N := by rw [sub_pos, div_lt_one hN]; exact ha.2
  have h₂ : 0 < 1 + a := by linarith [ha.1]
  have ha0 := ha.1
  have h₃ : 0 < 1 + r * a := by positivity
  have hd₁ := ((hasDerivAt_const a (1 : ℝ)).sub ((hasDerivAt_id a).div_const N)).log h₁.ne'
  have hd₂ := ((hasDerivAt_id a).const_add 1).log h₂.ne'
  have hd₃ := (((hasDerivAt_id a).const_mul r).const_add 1).log h₃.ne'
  convert (hd₁.sub (hd₂.const_mul ((N + 3) / 2))).add
    (hd₃.const_mul ((N + 1) / 2)) using 1
  · rfl
  · have hNa : N - a ≠ 0 := by linarith [ha.2]
    dsimp
    field_simp
    ring

private theorem poissonLogProfile_eq_zero_of_root {N r a : ℝ} (hN : 0 < N)
    (hr : 0 < r) (ha : a ∈ Ioo 0 N)
    (he : (1 - a / N) / (1 + a) ^ ((N + 3) / 2) =
      1 / (1 + r * a) ^ ((N + 1) / 2)) : poissonLogProfile N r a = 0 := by
  have h₁ : 0 < 1 - a / N := by rw [sub_pos, div_lt_one hN]; exact ha.2
  have h₂ : 0 < 1 + a := by linarith [ha.1]
  have ha0 := ha.1
  have h₃ : 0 < 1 + r * a := by positivity
  have hlog := congrArg Real.log he
  rw [Real.log_div h₁.ne' (Real.rpow_pos_of_pos h₂ _).ne',
    Real.log_div one_ne_zero (Real.rpow_pos_of_pos h₃ _).ne', Real.log_one,
    Real.log_rpow h₂, Real.log_rpow h₃] at hlog
  dsimp [poissonLogProfile]
  linarith

private theorem eq_of_poissonRoot {N r x y : ℝ} (hN : 0 < N) (hr : 1 < r)
    (hx : x ∈ Ioo 0 N) (hy : y ∈ Ioo 0 N)
    (hex : (1 - x / N) / (1 + x) ^ ((N + 3) / 2) =
      1 / (1 + r * x) ^ ((N + 1) / 2))
    (hey : (1 - y / N) / (1 + y) ^ ((N + 3) / 2) =
      1 / (1 + r * y) ^ ((N + 1) / 2)) : x = y := by
  wlog hxy : x < y generalizing x y
  · rcases lt_trichotomy x y with h | h | h
    · exact this hx hy hex hey h
    · exact h
    · exact (this hy hx hey hex h).symm
  have hr0 : 0 < r := zero_lt_one.trans hr
  let d : ℝ → ℝ := fun a ↦ ((N + 1) / 2) *
    (N * r - N - 2 + (1 - 3 * r) * a) / ((N - a) * (1 + a) * (1 + r * a))
  have hd : ∀ a ∈ Ico 0 N, HasDerivAt (poissonLogProfile N r) (d a) a :=
    fun a ha ↦ hasDerivAt_poissonLogProfile hN hr0 ha
  have hc : ContinuousOn (poissonLogProfile N r) (Icc 0 y) := by
    intro a ha
    exact ((hd a ⟨ha.1, ha.2.trans_lt hy.2⟩).continuousAt).continuousWithinAt
  have hx0 := poissonLogProfile_eq_zero_of_root hN hr0 hx hex
  have hy0 := poissonLogProfile_eq_zero_of_root hN hr0 hy hey
  have hzero : poissonLogProfile N r 0 = 0 := by simp [poissonLogProfile]
  obtain ⟨u, hu, heu⟩ := exists_hasDerivAt_eq_zero hx.1
    (hc.mono (Icc_subset_Icc le_rfl hxy.le)) (hzero.trans hx0.symm)
    (fun a ha ↦ hd a ⟨ha.1.le, ha.2.trans hx.2⟩)
  obtain ⟨v, hv, hev⟩ := exists_hasDerivAt_eq_zero hxy
    (hc.mono (Icc_subset_Icc hx.1.le le_rfl)) (hx0.trans hy0.symm)
    (fun a ha ↦ hd a ⟨(hx.1.trans ha.1).le, ha.2.trans hy.2⟩)
  have hu0 : N * r - N - 2 + (1 - 3 * r) * u = 0 := by
    have huN : N - u ≠ 0 := by linarith [hu.2, hx.2]
    have hu1 : 1 + u ≠ 0 := by linarith [hu.1]
    have hur : 1 + r * u ≠ 0 := by have hu0 := hu.1; positivity
    dsimp [d] at heu
    have he₁ := (div_eq_zero_iff.mp heu).resolve_right
      (mul_ne_zero (mul_ne_zero huN hu1) hur)
    exact (mul_eq_zero.mp he₁).resolve_left (by positivity)
  have hv0 : N * r - N - 2 + (1 - 3 * r) * v = 0 := by
    have hvN : N - v ≠ 0 := by linarith [hv.2, hy.2]
    have hv1 : 1 + v ≠ 0 := by linarith [hv.1, hx.1]
    have hvr : 1 + r * v ≠ 0 := by have hv0 : 0 < v := hx.1.trans hv.1; positivity
    dsimp [d] at hev
    have he₁ := (div_eq_zero_iff.mp hev).resolve_right
      (mul_ne_zero (mul_ne_zero hvN hv1) hvr)
    exact (mul_eq_zero.mp he₁).resolve_left (by positivity)
  have huv : u < v := hu.2.trans hv.1
  nlinarith

/-- Logarithm of the magnitude of the Poisson profile's weighted derivative, up to a constant. -/
def poissonWeightLog (β z : ℝ) : ℝ :=
  β * Real.log z - (β + 3 / 2) * Real.log (1 + z)

private theorem hasDerivAt_poissonWeightLog {β z : ℝ} (hz : 0 < z) :
    HasDerivAt (poissonWeightLog β) ((β - 3 * z / 2) / (z * (1 + z))) z := by
  have hz1 : 0 < 1 + z := by positivity
  convert ((Real.hasDerivAt_log hz.ne').const_mul β).sub
    ((((hasDerivAt_id z).const_add 1).log hz1.ne').const_mul (β + 3 / 2)) using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The Poisson weighted derivative increases up to its inflection radius squared. -/
theorem poissonWeightLog_lt {β x y : ℝ} (_hβ : 0 < β) (hx : 0 < x)
    (hxy : x < y) (hy : y ≤ 2 * β / 3) :
    poissonWeightLog β x < poissonWeightLog β y := by
  have hc : ContinuousOn (poissonWeightLog β) (Icc x y) := by
    intro z hz
    exact ((hasDerivAt_poissonWeightLog (β := β)
      (hx.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope (poissonWeightLog β)
    (fun z ↦ (β - 3 * z / 2) / (z * (1 + z))) hxy hc
    (fun z hz ↦ hasDerivAt_poissonWeightLog (hx.trans hz.1))
  have hder : 0 < (β - 3 * z / 2) / (z * (1 + z)) := by
    apply div_pos
    · linarith [hz.2]
    · have hz0 := hx.trans hz.1
      positivity
  rw [he] at hder
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hxy)).mp hder)

/-- The Poisson weighted derivative decreases beyond its inflection radius squared. -/
theorem poissonWeightLog_gt {β x y : ℝ} (hβ : 0 < β)
    (hx : 2 * β / 3 ≤ x) (hxy : x < y) :
    poissonWeightLog β y < poissonWeightLog β x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hc : ContinuousOn (poissonWeightLog β) (Icc x y) := by
    intro z hz
    exact ((hasDerivAt_poissonWeightLog (β := β)
      (hx0.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope (poissonWeightLog β)
    (fun z ↦ (β - 3 * z / 2) / (z * (1 + z))) hxy hc
    (fun z hz ↦ hasDerivAt_poissonWeightLog (hx0.trans hz.1))
  have hder : (β - 3 * z / 2) / (z * (1 + z)) < 0 := by
    apply div_neg_of_neg_of_pos
    · linarith [hz.1]
    · have hz0 := hx0.trans hz.1
      positivity
  rw [he] at hder
  have hnum := (div_lt_iff₀ (sub_pos.mpr hxy)).mp hder
  simpa only [zero_mul, sub_neg] using hnum

/-- Exponentiating the logarithmic Poisson weight recovers the weighted derivative. -/
theorem poissonWeightLog_exp {β z : ℝ} (hz : 0 < z) :
    Real.exp (poissonWeightLog β z) = z ^ β * (1 + z) ^ (-(β + 3 / 2)) := by
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos (by positivity : 0 < 1 + z),
    ← Real.exp_add]
  congr 1
  dsimp [poissonWeightLog]
  ring

private theorem poisson_harmonic_meanValue {β r a : ℝ} (_hβ : 0 < β) (hr : 1 < r)
    (ha : 0 < a) (hbalance : harmonicCoordinate β r = 1 / β) :
    ∃ z ∈ Ioo 1 r,
      ((1 + a * r) ^ (-(β + 1 / 2)) - (1 + a) ^ (-(β + 1 / 2))) * a ^ β =
        -((β + 1 / 2) * a / β) * Real.exp (poissonWeightLog β (a * z)) := by
  let f : ℝ → ℝ := fun z ↦ (1 + a * z) ^ (-(β + 1 / 2))
  let d : ℝ → ℝ := fun z ↦ -(β + 1 / 2) * a * (1 + a * z) ^ (-(β + 3 / 2))
  have hdf : ∀ z ∈ Icc 1 r, HasDerivAt f (d z) z := by
    intro z hz
    have hz0 : 0 < z := zero_lt_one.trans_le hz.1
    have hz1 : 0 < 1 + a * z := by positivity
    have hd := (Real.hasDerivAt_rpow_const (p := -(β + 1 / 2))
      (Or.inl hz1.ne')).comp z (((hasDerivAt_id z).const_mul a).const_add 1)
    convert hd using 1
    · rfl
    · dsimp [d]
      rw [show -(β + 1 / 2) - 1 = -(β + 3 / 2) by ring]
      ring
  have hf : ContinuousOn f (Icc 1 r) := fun z hz ↦
    ((hdf z hz).continuousAt).continuousWithinAt
  have hg : ContinuousOn (harmonicCoordinate β) (Icc 1 r) := fun z hz ↦
    ((hasDerivAt_harmonicCoordinate (β := β)
      (zero_lt_one.trans_le hz.1)).continuousAt).continuousWithinAt
  obtain ⟨z, hz, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f d hr hf
    (fun z hz ↦ hdf z ⟨hz.1.le, hz.2.le⟩) (harmonicCoordinate β)
    (fun z ↦ z ^ (-β)) hg
    (fun z hz ↦ hasDerivAt_harmonicCoordinate (zero_lt_one.trans hz.1))
  simp only [hbalance, harmonicCoordinate_one, sub_zero] at he
  have hz0 : 0 < z := zero_lt_one.trans hz.1
  have hp : 0 < z ^ β := Real.rpow_pos_of_pos hz0 _
  have he' := congrArg (fun v : ℝ ↦ v * z ^ β * a ^ β) he
  rw [Real.rpow_neg hz0.le] at he'
  simp only [mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] at he'
  refine ⟨z, hz, ?_⟩
  rw [poissonWeightLog_exp (mul_pos ha hz0), Real.mul_rpow ha.le hz0.le]
  dsimp [f, d] at he'
  simp only [mul_one] at he'
  convert he'.symm using 1
  ring

/-- The balanced Poisson harmonic tangent has the value used in the root equation. -/
theorem poisson_tangent_identity {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    (1 - a / (2 * β)) / (1 + a) ^ (β + 3 / 2) =
      (1 + a) ^ (-(β + 1 / 2)) -
        ((β + 1 / 2) * a / β) * (1 + a) ^ (-(β + 3 / 2)) := by
  have hb : 0 < 1 + a := by positivity
  have he : (1 + a) ^ (-(β + 1 / 2)) =
      (1 + a) * (1 + a) ^ (-(β + 3 / 2)) := by
    calc
      _ = (1 + a) ^ (1 + (-(β + 3 / 2))) := by congr 1; ring
      _ = (1 + a) ^ (1 : ℝ) * (1 + a) ^ (-(β + 3 / 2)) := Real.rpow_add hb _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he, Real.rpow_neg hb.le]
  field_simp
  ring

private theorem poisson_tangent_lower_sign {β r a : ℝ} (hβ : 0 < β) (hr : 1 < r)
    (ha : 0 < a) (har : a * r ≤ 2 * β / 3)
    (hbalance : harmonicCoordinate β r = 1 / β) :
    (1 + a * r) ^ (-(β + 1 / 2)) <
      (1 - a / (2 * β)) / (1 + a) ^ (β + 3 / 2) := by
  obtain ⟨z, hz, he⟩ := poisson_harmonic_meanValue hβ hr ha hbalance
  have hz0 : 0 < z := zero_lt_one.trans hz.1
  have haw : a < a * z := by nlinarith [hz.1]
  have hzcrit : a * z ≤ 2 * β / 3 := by nlinarith [hz.2]
  have hw := Real.exp_lt_exp.mpr (poissonWeightLog_lt hβ ha haw hzcrit)
  have hK : 0 < (β + 1 / 2) * a / β := by positivity
  have hmul := mul_lt_mul_of_neg_left hw (neg_neg_of_pos hK)
  rw [poissonWeightLog_exp ha] at hmul
  have hap : 0 < a ^ β := Real.rpow_pos_of_pos ha _
  rw [poisson_tangent_identity hβ ha]
  nlinarith

private theorem poisson_tangent_upper_sign {β r a : ℝ} (hβ : 0 < β) (hr : 1 < r)
    (ha : 2 * β / 3 ≤ a) (hbalance : harmonicCoordinate β r = 1 / β) :
    (1 - a / (2 * β)) / (1 + a) ^ (β + 3 / 2) <
      (1 + a * r) ^ (-(β + 1 / 2)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  obtain ⟨z, hz, he⟩ := poisson_harmonic_meanValue hβ hr ha0 hbalance
  have haw : a < a * z := by nlinarith [hz.1]
  have hw := Real.exp_lt_exp.mpr (poissonWeightLog_gt hβ ha haw)
  have hK : 0 < (β + 1 / 2) * a / β := by positivity
  have hmul := mul_lt_mul_of_neg_left hw (neg_neg_of_pos hK)
  rw [poissonWeightLog_exp ha0] at hmul
  have hap : 0 < a ^ β := Real.rpow_pos_of_pos ha0 _
  rw [poisson_tangent_identity hβ ha0]
  nlinarith

/-- The Poisson tangency equation has its unique nonzero root in the article's precise interval. -/
theorem existsUnique_poissonRoot (n : ℕ) (hn : 1 ≤ n) :
    ∃! a : ℝ, a ∈ Ioo ((n : ℝ) / (3 * rho n)) ((n : ℝ) / 3) ∧
      (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) =
        1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 := rho_pos n hn
  have hr := one_lt_rho n hn
  let l : ℝ := (n : ℝ) / (3 * rho n)
  let u : ℝ := (n : ℝ) / 3
  have hl : 0 < l := by dsimp [l]; positivity
  have hu : u < (n : ℝ) := by dsimp [u]; linarith
  have hlu : l < u := by
    dsimp [l, u]
    exact div_lt_div_of_pos_left hN (by norm_num) (by linarith)
  have hβ : 0 < (n : ℝ) / 2 := by positivity
  have hbalance : harmonicCoordinate ((n : ℝ) / 2) (rho n) = 1 / ((n : ℝ) / 2) := by
    simpa only [one_div, inv_div] using harmonicCoordinate_rho n hn
  have har : l * rho n ≤ 2 * ((n : ℝ) / 2) / 3 := by
    dsimp [l]
    field_simp
    norm_num
  have haul : 2 * ((n : ℝ) / 2) / 3 ≤ u := by dsimp [u]; linarith
  have hlow := poisson_tangent_lower_sign hβ hr hl har hbalance
  have hupp := poisson_tangent_upper_sign hβ hr haul hbalance
  have he₁ : (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 := by ring
  have he₃ : (n : ℝ) / 2 + 3 / 2 = ((n : ℝ) + 3) / 2 := by ring
  simp only [show 2 * ((n : ℝ) / 2) = (n : ℝ) by ring, he₁, he₃, mul_comm l,
    mul_comm u] at hlow hupp
  let F : ℝ → ℝ := fun a ↦ (1 + rho n * a) ^ (-(((n : ℝ) + 1) / 2)) -
    (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2)
  have hF : ContinuousOn F (Icc l u) := by
    intro a ha
    have ha0 : 0 < a := hl.trans_le ha.1
    have hb : 1 + a ≠ 0 := by positivity
    have hbr : 1 + rho n * a ≠ 0 := by positivity
    have hNne := hN.ne'
    have hbp : (1 + a) ^ (((n : ℝ) + 3) / 2) ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop (disch := aesop)
  obtain ⟨a, ha, he⟩ := intermediate_value_Ioo hlu.le hF
    (show 0 ∈ Ioo (F l) (F u) by constructor <;> dsimp [F] <;> linarith)
  have ha0 : 0 < a := hl.trans ha.1
  have har0 : 0 < 1 + rho n * a := by positivity
  have heq : (1 - a / (n : ℝ)) / (1 + a) ^ (((n : ℝ) + 3) / 2) =
      1 / (1 + rho n * a) ^ (((n : ℝ) + 1) / 2) := by
    dsimp [F] at he
    rw [Real.rpow_neg har0.le, ← one_div] at he
    linarith
  refine ⟨a, ⟨ha, heq⟩, fun b hb ↦ ?_⟩
  exact eq_of_poissonRoot hN hr ⟨hl.trans hb.1.1, hb.1.2.trans hu⟩
    ⟨ha0, ha.2.trans hu⟩ hb.2 heq

end PartialBalayage.Constants
