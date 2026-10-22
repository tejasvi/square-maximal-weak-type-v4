/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

/-!
# Actual normalized mollification in `L²`

Convolution by a nonnegative compactly supported continuous probability density is an actual
`L²` contraction. The proof uses the nonnegative variance integral, then integrates the
pointwise estimate. These estimates support approximation of genuine weak derivative graphs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped Convolution RealInnerProductSpace ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The genuine scalar variance estimate for a normalized compactly supported kernel. -/
theorem sq_convolution_le_convolution_sq
    {ρ f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) (hf : MemLp f 2 volume)
    (x : EuclideanSpace ℝ (Fin d)) :
    (ρ ⋆ f) x ^ 2 ≤ (ρ ⋆ (fun y ↦ f y ^ 2)) x := by
  let c := (ρ ⋆ f) x
  have hρint : Integrable ρ volume := hρ.integrable_of_hasCompactSupport hρc
  have hpf : Integrable (fun y ↦ ρ y * f (x - y)) volume := by
    exact hρc.convolutionExists_left (lsmul ℝ ℝ) hρ (hf.locallyIntegrable (by norm_num)) x
  obtain ⟨C, hC⟩ := hρc.exists_bound_of_continuous hρ
  have hpsq : Integrable (fun y ↦ ρ y * f (x - y) ^ 2) volume :=
    (hf.integrable_sq.comp_sub_left x).bdd_mul hρ.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hmid : Integrable (fun y ↦ -(2 * c) * (ρ y * f (x - y))) volume :=
    hpf.const_mul (-(2 * c))
  have hend : Integrable (fun y ↦ c ^ 2 * ρ y) volume := hρint.const_mul (c ^ 2)
  have hsum : Integrable (fun y ↦ ρ y * f (x - y) ^ 2 +
      -(2 * c) * (ρ y * f (x - y))) volume := hpsq.add hmid
  have hsplit : (∫ y, ρ y * (f (x - y) - c) ^ 2) =
      (∫ y, ρ y * f (x - y) ^ 2) - 2 * c * (∫ y, ρ y * f (x - y)) +
        c ^ 2 * (∫ y, ρ y) := by
    calc
      _ = ∫ y, (ρ y * f (x - y) ^ 2 + -(2 * c) * (ρ y * f (x - y))) +
          c ^ 2 * ρ y := by
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ = _ := by
        rw [integral_add hsum hend, integral_add hpsq hmid,
          integral_const_mul, integral_const_mul]
        ring
  have hnonneg : 0 ≤ ∫ y, ρ y * (f (x - y) - c) ^ 2 :=
    integral_nonneg (fun y ↦ mul_nonneg (hρ0 y) (sq_nonneg _))
  have hc : (∫ y, ρ y * f (x - y)) = c := rfl
  rw [hsplit, hc, hρ1] at hnonneg
  change c ^ 2 ≤ ∫ y, ρ y * f (x - y) ^ 2
  nlinarith

/-- Normalized compactly supported convolution constructs a genuine `L²` function. -/
theorem memLp_normalized_convolution
    {ρ f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) (hf : MemLp f 2 volume) :
    MemLp (ρ ⋆ f) 2 volume := by
  have hc := hρc.continuous_convolution_left (L := lsmul ℝ ℝ) hρ
    (hf.locallyIntegrable (by norm_num))
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hsqint := (hρ.integrable_of_hasCompactSupport (μ := volume) hρc).integrable_convolution
    (lsmul ℝ ℝ) hf.integrable_sq
  apply hsqint.mono' (hc.aestronglyMeasurable.pow 2)
  filter_upwards with x
  change ‖(ρ ⋆ f) x ^ 2‖ ≤ (ρ ⋆ (fun y ↦ f y ^ 2)) x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_convolution_le_convolution_sq hρ hρc hρ0 hρ1 hf x

/-- The squared integral estimate retains the exact contraction constant one. -/
theorem integral_sq_normalized_convolution_le
    {ρ f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) (hf : MemLp f 2 volume) :
    (∫ x, (ρ ⋆ f) x ^ 2) ≤ ∫ x, f x ^ 2 := by
  have hρint : Integrable ρ volume := hρ.integrable_of_hasCompactSupport hρc
  calc
    _ ≤ ∫ x, (ρ ⋆ (fun y ↦ f y ^ 2)) x :=
      integral_mono (memLp_normalized_convolution hρ hρc hρ0 hρ1 hf).integrable_sq
        (hρint.integrable_convolution (lsmul ℝ ℝ) hf.integrable_sq)
        (sq_convolution_le_convolution_sq hρ hρc hρ0 hρ1 hf)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ) hρint hf.integrable_sq, hρ1]
      simp

/-- Scalar `L²` norms equal the ordinary square integrals for the actual class representatives. -/
theorem real_L2_norm_sq_eq_integral
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖a‖ ^ 2 = ∫ x, (a x : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.inner_apply, pow_two]

/-- The actual `L²` class constructed by normalized convolution is a contraction. -/
theorem norm_normalized_convolution_toLp_le
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖(memLp_normalized_convolution hρ hρc hρ0 hρ1 (Lp.memLp a)).toLp (ρ ⋆ a)‖ ≤ ‖a‖ := by
  let h := memLp_normalized_convolution hρ hρc hρ0 hρ1 (Lp.memLp a)
  have heq : ‖h.toLp (ρ ⋆ a)‖ ^ 2 = ∫ x, (ρ ⋆ a) x ^ 2 := by
    rw [real_L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hbound := integral_sq_normalized_convolution_le hρ hρc hρ0 hρ1 (Lp.memLp a)
  rw [← real_L2_norm_sq_eq_integral, ← heq] at hbound
  change ‖h.toLp (ρ ⋆ a)‖ ≤ ‖a‖
  nlinarith [norm_nonneg a, norm_nonneg (h.toLp (ρ ⋆ a))]

/-- The actual `L²` convolution operator, with its probability-density data. -/
def normalizedConvolutionL2 {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  (memLp_normalized_convolution hρ hρc hρ0 hρ1 (Lp.memLp a)).toLp (ρ ⋆ a)

theorem normalizedConvolutionL2_ae {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    normalizedConvolutionL2 hρ hρc hρ0 hρ1 a =ᵐ[volume] ρ ⋆ a :=
  MemLp.coeFn_toLp _

theorem normalizedConvolutionL2_add {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    normalizedConvolutionL2 hρ hρc hρ0 hρ1 (a + b) =
      normalizedConvolutionL2 hρ hρc hρ0 hρ1 a +
        normalizedConvolutionL2 hρ hρc hρ0 hρ1 b := by
  have hconv : ρ ⋆ (a + b) = ρ ⋆ a + ρ ⋆ b := by
    rw [convolution_congr (lsmul ℝ ℝ) (Filter.EventuallyEq.refl (ae volume) ρ)
      (Lp.coeFn_add a b)]
    exact (hρc.convolutionExists_left (lsmul ℝ ℝ) hρ
      ((Lp.memLp a).locallyIntegrable (by norm_num))).distrib_add
      (hρc.convolutionExists_left (lsmul ℝ ℝ) hρ
        ((Lp.memLp b).locallyIntegrable (by norm_num)))
  apply Lp.ext
  filter_upwards [normalizedConvolutionL2_ae hρ hρc hρ0 hρ1 (a + b),
    normalizedConvolutionL2_ae hρ hρc hρ0 hρ1 a,
    normalizedConvolutionL2_ae hρ hρc hρ0 hρ1 b,
    Lp.coeFn_add (normalizedConvolutionL2 hρ hρc hρ0 hρ1 a)
      (normalizedConvolutionL2 hρ hρc hρ0 hρ1 b)] with x hx ha hb hab
  rw [hx, hab]
  simp only [Pi.add_apply]
  rw [ha, hb, hconv]
  rfl

theorem normalizedConvolutionL2_smul {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (c : ℝ) (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    normalizedConvolutionL2 hρ hρc hρ0 hρ1 (c • a) =
      c • normalizedConvolutionL2 hρ hρc hρ0 hρ1 a := by
  have hconv : ρ ⋆ (c • a) = c • (ρ ⋆ a) := by
    rw [convolution_congr (lsmul ℝ ℝ) (Filter.EventuallyEq.refl (ae volume) ρ)
      (Lp.coeFn_smul c a), convolution_smul]
  apply Lp.ext
  filter_upwards [normalizedConvolutionL2_ae hρ hρc hρ0 hρ1 (c • a),
    normalizedConvolutionL2_ae hρ hρc hρ0 hρ1 a,
    Lp.coeFn_smul c (normalizedConvolutionL2 hρ hρc hρ0 hρ1 a)] with x hx ha hs
  rw [hx, hs]
  simp only [Pi.smul_apply]
  rw [ha, hconv]
  rfl

/-- Normalized convolution is a genuine bounded linear operator on scalar real `L²`. -/
def normalizedConvolutionL2CLM {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  ({ toFun := normalizedConvolutionL2 hρ hρc hρ0 hρ1
     map_add' := normalizedConvolutionL2_add hρ hρc hρ0 hρ1
     map_smul' := normalizedConvolutionL2_smul hρ hρc hρ0 hρ1 } :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))).mkContinuous 1 (fun a ↦ by
        change ‖normalizedConvolutionL2 hρ hρc hρ0 hρ1 a‖ ≤ 1 * ‖a‖
        rw [one_mul]
        exact norm_normalized_convolution_toLp_le hρ hρc hρ0 hρ1 a)

theorem dist_normalizedConvolutionL2_le {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    dist (normalizedConvolutionL2 hρ hρc hρ0 hρ1 a)
      (normalizedConvolutionL2 hρ hρc hρ0 hρ1 b) ≤ dist a b := by
  change dist (normalizedConvolutionL2CLM hρ hρc hρ0 hρ1 a)
    (normalizedConvolutionL2CLM hρ hρc hρ0 hρ1 b) ≤ dist a b
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  change ‖normalizedConvolutionL2 hρ hρc hρ0 hρ1 (a - b)‖ ≤ ‖a - b‖
  exact norm_normalized_convolution_toLp_le hρ hρc hρ0 hρ1 (a - b)

end PartialBalayage.Linear
