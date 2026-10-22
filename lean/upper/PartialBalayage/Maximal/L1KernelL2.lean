/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.MollifierL2

/-!
# Genuine L¹ kernels acting on scalar L²

Tonelli supplies almost everywhere finite weighted second moments. The elementary estimate
`|f| ≤ f² + 1` then supplies actual convolution existence, and the nonnegative variance
integral proves Young's L² estimate without compactness or boundedness of the kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Filter
open scoped Convolution ENNReal Topology

namespace PartialBalayage

variable {n : ℕ}

/-- A finite weighted second moment gives a genuine finite weighted first moment. -/
theorem integrable_weighted_of_integrable_weighted_sq
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : AEStronglyMeasurable f volume)
    (hfsq : Integrable (fun y ↦ K y * f y ^ 2)) :
    Integrable (fun y ↦ K y * f y) := by
  apply (hfsq.add hK).mono' (hK.aestronglyMeasurable.mul hf)
  filter_upwards [hK0] with y hy
  change ‖K y * f y‖ ≤ K y * f y ^ 2 + K y
  rw [norm_mul, Real.norm_of_nonneg hy]
  have hnorm : ‖f y‖ ≤ f y ^ 2 + 1 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|f y| - 1), sq_abs (f y)]
  exact (mul_le_mul_of_nonneg_left hnorm hy).trans_eq (by ring)

/-- An actual nonnegative L¹ kernel has a well-defined convolution with an L² input a.e. -/
theorem ae_convolution_exists_of_nonneg_L1_L2
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ConvolutionExistsAt K f x (lsmul ℝ ℝ) volume := by
  filter_upwards [hK.ae_convolution_exists (lsmul ℝ ℝ) hf.integrable_sq] with x hx
  exact integrable_weighted_of_integrable_weighted_sq hK hK0
    (hf.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x)) hx

/-- The actual scalar variance estimate with the exact total kernel mass. -/
theorem ae_sq_convolution_le_mass_mul_convolution_sq
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, (K ⋆[lsmul ℝ ℝ, volume] f) x ^ 2 ≤
      (∫ y, K y) * (K ⋆[lsmul ℝ ℝ, volume] (fun y ↦ f y ^ 2)) x := by
  let m := ∫ y, K y
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hK0
  by_cases hm : m = 0
  · have hzero : K =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg_ae hK0 hK).mp hm
    have hconv : K ⋆[lsmul ℝ ℝ, volume] f = 0 := by
      rw [convolution_congr (lsmul ℝ ℝ) hzero (EventuallyEq.refl (ae volume) f)]
      exact zero_convolution
    exact Eventually.of_forall fun x ↦ by simp only [hconv, Pi.zero_apply, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, m, hm, zero_mul, le_refl]
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  filter_upwards [hK.ae_convolution_exists (lsmul ℝ ℝ) hf.integrable_sq,
    ae_convolution_exists_of_nonneg_L1_L2 hK hK0 hf] with x hpsq hpf
  have hpsq' : Integrable (fun y ↦ K y * f (x - y) ^ 2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using hpsq
  have hpf' : Integrable (fun y ↦ K y * f (x - y)) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using hpf
  let c := (K ⋆[lsmul ℝ ℝ, volume] f) x / m
  have hc : c * m = (K ⋆[lsmul ℝ ℝ, volume] f) x := div_mul_cancel₀ _ hm
  have hmid : Integrable (fun y ↦ -(2 * c) * (K y * f (x - y))) :=
    hpf'.const_mul (-(2 * c))
  have hend : Integrable (fun y ↦ c ^ 2 * K y) := hK.const_mul (c ^ 2)
  have hsum : Integrable (fun y ↦ K y * f (x - y) ^ 2 +
      -(2 * c) * (K y * f (x - y))) := hpsq'.add hmid
  have hsplit : (∫ y, K y * (f (x - y) - c) ^ 2) =
      (K ⋆[lsmul ℝ ℝ, volume] (fun y ↦ f y ^ 2)) x -
        2 * c * (K ⋆[lsmul ℝ ℝ, volume] f) x + c ^ 2 * m := by
    calc
      _ = ∫ y, (K y * f (x - y) ^ 2 + -(2 * c) * (K y * f (x - y))) +
          c ^ 2 * K y := by
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ = _ := by
        rw [integral_add hsum hend, integral_add hpsq' hmid,
          integral_const_mul, integral_const_mul]
        simp only [convolution_def, lsmul_apply, smul_eq_mul, m]
        ring
  have hnonneg : 0 ≤ ∫ y, K y * (f (x - y) - c) ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [hK0] with y hy
    exact mul_nonneg hy (sq_nonneg _)
  have hp := mul_nonneg hmpos.le hnonneg
  rw [hsplit] at hp
  have hidentity : m * ((K ⋆[lsmul ℝ ℝ, volume] (fun y ↦ f y ^ 2)) x -
      2 * c * (K ⋆[lsmul ℝ ℝ, volume] f) x + c ^ 2 * m) =
      m * (K ⋆[lsmul ℝ ℝ, volume] (fun y ↦ f y ^ 2)) x -
        (K ⋆[lsmul ℝ ℝ, volume] f) x ^ 2 := by
    rw [← hc]
    ring
  rw [hidentity] at hp
  exact sub_nonneg.mp hp

/-- Young's inequality constructs an actual L² convolution for every nonnegative L¹ kernel. -/
theorem memLp_convolution_of_nonneg_L1_L2
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : MemLp f 2 volume) :
    MemLp (K ⋆[lsmul ℝ ℝ, volume] f) 2 volume := by
  have hc := hK.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hc).mpr
  have hsqint := (hK.integrable_convolution (lsmul ℝ ℝ) hf.integrable_sq).const_mul (∫ y, K y)
  apply hsqint.mono' (hc.pow 2)
  filter_upwards [ae_sq_convolution_le_mass_mul_convolution_sq hK hK0 hf] with x hx
  change ‖(K ⋆[lsmul ℝ ℝ, volume] f) x ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

/-- The exact squared Young estimate retains two factors of the actual kernel mass. -/
theorem integral_sq_convolution_le_mass_sq_mul
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : MemLp f 2 volume) :
    (∫ x, (K ⋆[lsmul ℝ ℝ, volume] f) x ^ 2) ≤ (∫ y, K y) ^ 2 * ∫ x, f x ^ 2 := by
  calc
    _ ≤ ∫ x, (∫ y, K y) * (K ⋆[lsmul ℝ ℝ, volume] (fun y ↦ f y ^ 2)) x :=
      integral_mono_ae (memLp_convolution_of_nonneg_L1_L2 hK hK0 hf).integrable_sq
        ((hK.integrable_convolution (lsmul ℝ ℝ) hf.integrable_sq).const_mul _)
        (ae_sq_convolution_le_mass_mul_convolution_sq hK hK0 hf)
    _ = _ := by
      rw [integral_const_mul, integral_convolution (lsmul ℝ ℝ) hK hf.integrable_sq]
      simp only [lsmul_apply, smul_eq_mul]
      ring

/-- The actual scalar L² class of convolution by a nonnegative integrable kernel. -/
def nonnegKernelConvolutionL2 {K : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (memLp_convolution_of_nonneg_L1_L2 hK hK0 (Lp.memLp a)).toLp (K ⋆[lsmul ℝ ℝ, volume] a)

theorem nonnegKernelConvolutionL2_ae {K : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    nonnegKernelConvolutionL2 hK hK0 a =ᵐ[volume] K ⋆[lsmul ℝ ℝ, volume] a :=
  MemLp.coeFn_toLp _

/-- The L² operator bound is the actual total kernel mass. -/
theorem norm_nonnegKernelConvolutionL2_le {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : Integrable K) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖nonnegKernelConvolutionL2 hK hK0 a‖ ≤ (∫ y, K y) * ‖a‖ := by
  have heq : ‖nonnegKernelConvolutionL2 hK hK0 a‖ ^ 2 =
      ∫ x, (K ⋆[lsmul ℝ ℝ, volume] a) x ^ 2 := by
    rw [Linear.real_L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [nonnegKernelConvolutionL2_ae hK hK0 a] with x hx
    rw [hx]
  have h := integral_sq_convolution_le_mass_sq_mul hK hK0 (Lp.memLp a)
  rw [← Linear.real_L2_norm_sq_eq_integral, ← heq] at h
  have hm : 0 ≤ ∫ y, K y := integral_nonneg_of_ae hK0
  nlinarith [norm_nonneg a, norm_nonneg (nonnegKernelConvolutionL2 hK hK0 a),
    mul_nonneg hm (norm_nonneg a)]

theorem nonnegKernelConvolutionL2_add {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : Integrable K) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    (a b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    nonnegKernelConvolutionL2 hK hK0 (a + b) =
      nonnegKernelConvolutionL2 hK hK0 a + nonnegKernelConvolutionL2 hK hK0 b := by
  have hconv : K ⋆[lsmul ℝ ℝ, volume] (a + b) =
      K ⋆[lsmul ℝ ℝ, volume] ((a : _ → ℝ) + (b : _ → ℝ)) :=
    convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl (ae volume) K) (Lp.coeFn_add a b)
  apply Lp.ext
  filter_upwards [nonnegKernelConvolutionL2_ae hK hK0 (a + b),
    nonnegKernelConvolutionL2_ae hK hK0 a, nonnegKernelConvolutionL2_ae hK hK0 b,
    Lp.coeFn_add (nonnegKernelConvolutionL2 hK hK0 a) (nonnegKernelConvolutionL2 hK hK0 b),
    ae_convolution_exists_of_nonneg_L1_L2 hK hK0 (Lp.memLp a),
    ae_convolution_exists_of_nonneg_L1_L2 hK hK0 (Lp.memLp b)] with x hx ha hb hab hca hcb
  rw [hx, hab]
  simp only [Pi.add_apply]
  rw [ha, hb, hconv]
  exact hca.distrib_add hcb

theorem nonnegKernelConvolutionL2_smul {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : Integrable K) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (c : ℝ)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    nonnegKernelConvolutionL2 hK hK0 (c • a) = c • nonnegKernelConvolutionL2 hK hK0 a := by
  have hconv : K ⋆[lsmul ℝ ℝ, volume] (c • a) = c • (K ⋆[lsmul ℝ ℝ, volume] a) := by
    rw [convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl (ae volume) K)
      (Lp.coeFn_smul c a), convolution_smul]
  apply Lp.ext
  filter_upwards [nonnegKernelConvolutionL2_ae hK hK0 (c • a),
    nonnegKernelConvolutionL2_ae hK hK0 a,
    Lp.coeFn_smul c (nonnegKernelConvolutionL2 hK hK0 a)] with x hx ha hs
  rw [hx, hs]
  simp only [Pi.smul_apply]
  rw [ha, hconv]
  rfl

/-- Every actual nonnegative L¹ kernel defines a bounded linear operator on real L². -/
def nonnegKernelConvolutionL2CLM {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : Integrable K) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  ({ toFun := nonnegKernelConvolutionL2 hK hK0
     map_add' := nonnegKernelConvolutionL2_add hK hK0
     map_smul' := nonnegKernelConvolutionL2_smul hK hK0 } :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).mkContinuous (∫ y, K y)
        (norm_nonnegKernelConvolutionL2_le hK hK0)

/-- Strong L² convergence survives convolution by the actual L¹ kernel. -/
theorem tendsto_nonnegKernelConvolutionL2 {K : EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : Integrable K) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    {a : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    {b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun k ↦ nonnegKernelConvolutionL2 hK hK0 (a k)) atTop
      (𝓝 (nonnegKernelConvolutionL2 hK hK0 b)) :=
  (nonnegKernelConvolutionL2CLM hK hK0).continuous.continuousAt.tendsto.comp ha

end PartialBalayage
