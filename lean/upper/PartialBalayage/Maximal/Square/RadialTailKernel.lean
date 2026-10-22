/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponents for alpha = 47/40 (1 + alpha = 87/40, 2 alpha = 47/20, 2 alpha + 1 = 67/20). -/
module

public import PartialBalayage.Maximal.Square.RadialGeneratorDefinitions
public import PartialBalayage.Maximal.Square.RadialTailMoments

/-!
# Actual incoming-tail integrability and pointwise lower bounds

Positive improper shifted-power integrals prove actual tail integrability.
The genuine binomial expansions give every finite rational truncation as
a lower bound on the physical three-term incoming kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Maximal.Square

/-- The genuine incoming coordinate-power kernel. -/
def radialIncomingPowerKernel (r d q : ℝ) : ℝ :=
  2 * (q - r) ^ (-87 / 40 : ℝ) + (q - d) ^ (-87 / 40 : ℝ) +
    (q + d) ^ (-87 / 40 : ℝ)

theorem radialIncomingTail_eq_integral_powerKernel (R r d : ℝ) :
    radialIncomingTail (47 / 40) R r d =
      ∫ q in Ioi R, (R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ)) *
        radialIncomingPowerKernel r d q := by
  simp only [radialIncomingTail, radialIncomingPowerKernel,
    show (-1 : ℝ) - 47 / 40 = -87 / 40 by norm_num,
    show -(47 / 40 : ℝ) = -47 / 40 by ring]

/-- Each actual shifted power is integrable beyond the strict diamond support. -/
theorem integrableOn_radialIncomingPowerKernel {R r d : ℝ}
    (hr : r < R) (hd : |d| < R) :
    IntegrableOn (radialIncomingPowerKernel r d) (Ioi R) := by
  have hi₁ := integrableOn_add_rpow_Ioi_of_lt
    (by norm_num : (-87 / 40 : ℝ) < -1) (by simpa using hr : -(-r) < R)
  have hi₂ := integrableOn_add_rpow_Ioi_of_lt
    (by norm_num : (-87 / 40 : ℝ) < -1)
    (by simpa using (le_abs_self d).trans_lt hd : -(-d) < R)
  have hi₃ := integrableOn_add_rpow_Ioi_of_lt
    (by norm_num : (-87 / 40 : ℝ) < -1) ((neg_le_abs d).trans_lt hd)
  apply IntegrableOn.congr_fun (((hi₁.const_mul (2 : ℝ)).add hi₂).add hi₃)
    _ measurableSet_Ioi
  intro q _
  change 2 * (q + -r) ^ (-87 / 40 : ℝ) + (q + -d) ^ (-87 / 40 : ℝ) +
    (q + d) ^ (-87 / 40 : ℝ) = radialIncomingPowerKernel r d q
  simp only [radialIncomingPowerKernel, sub_eq_add_neg]

/-- The actual incoming-tail integrand is genuinely integrable. -/
theorem integrableOn_radialIncomingTail_integrand {R r d : ℝ} (hR : 0 < R)
    (hr : r < R) (hd : |d| < R) :
    IntegrableOn (fun q : ℝ ↦ (R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ)) *
      radialIncomingPowerKernel r d q) (Ioi R) := by
  have hK := integrableOn_radialIncomingPowerKernel hr hd
  apply hK.bdd_mul
  · have hm : AEStronglyMeasurable
        (fun q : ℝ ↦ R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ)) volume :=
      (by fun_prop : Measurable
        (fun q : ℝ ↦ R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ))).aestronglyMeasurable
    exact hm.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    have hw : 0 ≤ R ^ (-47 / 40 : ℝ) - q ^ (-47 / 40 : ℝ) := by
      exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hR hq.le (by norm_num))
    rw [Real.norm_eq_abs, abs_of_nonneg hw]
    exact sub_le_self _ (Real.rpow_nonneg (hR.trans hq).le _)

/-- Actual powers factor through the true positive ratio. -/
theorem rpow_sub_eq_mul_ratio {q a : ℝ} (hq : 0 < q) (ha : a < q) (p : ℝ) :
    (q - a) ^ p = q ^ p * (1 - a / q) ^ p := by
  have hratio : 0 ≤ 1 - a / q := by
    have h := (div_lt_one hq).mpr ha
    linarith
  rw [← Real.mul_rpow hq.le hratio]
  congr 1
  field_simp

/-- A genuine frequency-free ratio monomial has its actual power normalization. -/
theorem rpow_mul_div_nat {q : ℝ} (hq : 0 < q) (a p : ℝ) (n : ℕ) :
    q ^ p * (a / q) ^ n = a ^ n * q ^ (p - n) := by
  have hp : (q ^ n)⁻¹ = q ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg hq.le, Real.rpow_natCast]
  calc
    q ^ p * (a / q) ^ n = a ^ n * (q ^ p * (q ^ n)⁻¹) := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ = a ^ n * (q ^ p * q ^ (-(n : ℝ))) := by rw [hp]
    _ = a ^ n * q ^ (p - n) := by rw [← Real.rpow_add hq]; rfl

/-- The actual three-term power kernel dominates every finite rational tail truncation. -/
theorem radialIncomingPowerKernel_ge_sum {q r d : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (hrq : r < q) (hdq : |d| < q) (N : ℕ) :
    (∑ n ∈ Finset.range N, (radialTailBinomialCoefficient n : ℝ) *
      (2 * r ^ n + d ^ n + (-d) ^ n) * q ^ (-87 / 40 - (n : ℝ))) ≤
        radialIncomingPowerKernel r d q := by
  have hrdiv : 0 ≤ r / q := div_nonneg hr hq.le
  have hrdiv₁ : r / q < 1 := (div_lt_one hq).mpr hrq
  have hddiv : |d / q| < 1 := by
    rw [abs_div, abs_of_pos hq]
    exact (div_lt_one hq).mpr hdq
  have hb := mul_le_mul_of_nonneg_left
    (radialTailBinomial_combined_sum_le hrdiv hrdiv₁ hddiv N)
    (Real.rpow_nonneg hq.le (-87 / 40 : ℝ))
  have hleft : q ^ (-87 / 40 : ℝ) *
      (∑ n ∈ Finset.range N, (radialTailBinomialCoefficient n : ℝ) *
        (2 * (r / q) ^ n + (d / q) ^ n + (-(d / q)) ^ n)) =
      ∑ n ∈ Finset.range N, (radialTailBinomialCoefficient n : ℝ) *
        (2 * r ^ n + d ^ n + (-d) ^ n) * q ^ (-87 / 40 - (n : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← neg_div]
    calc
      _ = (radialTailBinomialCoefficient n : ℝ) *
          (2 * (q ^ (-87 / 40 : ℝ) * (r / q) ^ n) +
            q ^ (-87 / 40 : ℝ) * (d / q) ^ n +
            q ^ (-87 / 40 : ℝ) * ((-d) / q) ^ n) := by ring
      _ = _ := by
        rw [rpow_mul_div_nat hq r, rpow_mul_div_nat hq d, rpow_mul_div_nat hq (-d)]
        ring
  have hright : q ^ (-87 / 40 : ℝ) *
      (2 * (1 - r / q) ^ (-87 / 40 : ℝ) +
        (1 - d / q) ^ (-87 / 40 : ℝ) + (1 + d / q) ^ (-87 / 40 : ℝ)) =
      radialIncomingPowerKernel r d q := by
    have hdr : d < q := (le_abs_self d).trans_lt hdq
    have hndr : -d < q := (neg_le_abs d).trans_lt hdq
    rw [radialIncomingPowerKernel, rpow_sub_eq_mul_ratio hq hrq,
      rpow_sub_eq_mul_ratio hq hdr, show q + d = q - (-d) by ring,
      rpow_sub_eq_mul_ratio hq hndr]
    simp only [neg_div, sub_neg_eq_add]
    ring
  simpa only [hleft, hright] using hb

end PartialBalayage.Maximal.Square
