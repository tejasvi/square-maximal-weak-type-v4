/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandProfile
public import PartialBalayage.Maximal.Square.BandBinomial

/-!
# Positive series lower bounds for the exterior line integrals

With `q = v ± s` the corner integrals become `∫_v^R F(q) ((X - q)^(-p) + (q + Z)^(-p)) dq`
with `X = u + v`, `Z = u - v`. Writing `q + Z = W - (R - q)`, `W = R + Z`, both powers have
nonnegative binomial expansions, so every truncation (also with rounded coefficients) of the
termwise integrated series is a lower bound. The moments are elementary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius

/-- The `q`-form of the exterior line integral. -/
theorem bandLine_q {u v : ℝ} (hv : 0 < v) (hvR : v < Rs) (hr : Rs < u + v) :
    bandLine u v = ∫ q in v..Rs, bandPsi q *
      ((u + v - q) ^ (-1 - (47 / 40 : ℝ)) + (q + (u - v)) ^ (-1 - (47 / 40 : ℝ))) := by
  unfold bandLine
  rw [line_eq_q_form (g := fun s ↦ (u - s) ^ (-1 - (47 / 40 : ℝ))) (F := bandPsi) hv hvR
    (continuousOn_bandIntegrand hv hr)]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  rw [show u - (q - v) = u + v - q by ring, show u - (v - q) = q + (u - v) by ring]

/-- The `q`-form of the first slope integral. -/
theorem bandSlopeU_q {u v : ℝ} (hv : 0 < v) (hvR : v < Rs) (hr : Rs < u + v) :
    bandSlopeU u v = ∫ q in v..Rs, bandPsi q * ((1 + 47 / 40) *
      ((u + v - q) ^ (-2 - (47 / 40 : ℝ)) + (q + (u - v)) ^ (-2 - (47 / 40 : ℝ)))) := by
  unfold bandSlopeU
  have hc : ContinuousOn (fun s ↦ ((1 + 47 / 40) * (u - s) ^ (-2 - (47 / 40 : ℝ))) * bandPsi (|s| + v))
      (Icc (v - Rs) (Rs - v)) := by
    apply ContinuousOn.mul (continuousOn_const.mul ?_) (continuous_bandPsi_comp hv).continuousOn
    apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
    intro s hs; left; exact (show (0 : ℝ) < u - s by linarith [hs.2]).ne'
  have h := line_eq_q_form (g := fun s ↦ (1 + 47 / 40) * (u - s) ^ (-2 - (47 / 40 : ℝ)))
    (F := bandPsi) hv hvR hc
  rw [h]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  rw [show u - (q - v) = u + v - q by ring, show u - (v - q) = q + (u - v) by ring]
  ring

/-- The second slope integral with the continuous profile slope (they differ at one point). -/
theorem bandSlopeV_eq_continuous {u v : ℝ} (hv : 0 < v) (hvR : v < Rs) :
    bandSlopeV u v = ∫ s in (v - Rs)..(Rs - v),
      (47 / 40) * (u - s) ^ (-1 - (47 / 40 : ℝ)) * (|s| + v) ^ (-1 - (47 / 40 : ℝ)) := by
  unfold bandSlopeV
  apply intervalIntegral.integral_congr_ae
  rw [ae_iff]
  apply measure_mono_null _ (measure_singleton (Rs - v))
  intro s hs
  simp only [mem_setOf_eq, not_imp] at hs
  obtain ⟨hmem, hne⟩ := hs
  rw [uIoc_of_le (by linarith)] at hmem
  by_contra hns
  apply hne
  have hlt : |s| + v < Rs := by
    have h₂ : s < Rs - v := lt_of_le_of_ne hmem.2 hns
    rcases le_or_gt 0 s with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith [hmem.1]
  simp only [bandPsiSlope, hlt, ↓reduceIte]

/-- The `q`-form of the second slope integral. -/
theorem bandSlopeV_q {u v : ℝ} (hv : 0 < v) (hvR : v < Rs) (hr : Rs < u + v) :
    bandSlopeV u v = ∫ q in v..Rs, q ^ (-1 - (47 / 40 : ℝ)) * ((47 / 40) *
      ((u + v - q) ^ (-1 - (47 / 40 : ℝ)) + (q + (u - v)) ^ (-1 - (47 / 40 : ℝ)))) := by
  rw [bandSlopeV_eq_continuous hv hvR]
  have hc : ContinuousOn (fun s ↦ ((47 / 40) * (u - s) ^ (-1 - (47 / 40 : ℝ))) *
      (fun q : ℝ ↦ q ^ (-1 - (47 / 40 : ℝ))) (|s| + v)) (Icc (v - Rs) (Rs - v)) := by
    apply ContinuousOn.mul (continuousOn_const.mul ?_) ?_
    · apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      intro s hs; left; exact (show (0 : ℝ) < u - s by linarith [hs.2]).ne'
    · apply Continuous.continuousOn
      apply Continuous.rpow_const (continuous_abs.add continuous_const)
      intro s; left; exact (show (0 : ℝ) < |s| + v by linarith [abs_nonneg s]).ne'
  have h := line_eq_q_form (g := fun s ↦ (47 / 40) * (u - s) ^ (-1 - (47 / 40 : ℝ)))
    (F := fun q : ℝ ↦ q ^ (-1 - (47 / 40 : ℝ))) hv hvR hc
  rw [h]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  rw [show u - (q - v) = u + v - q by ring, show u - (v - q) = q + (u - v) by ring]
  ring

/-- The generic two-part series lower bound for `∫_v^R F(q)((X - q)^(-p) + (q + Z)^(-p)) dq`. -/
theorem q_series_le {F : ℝ → ℝ} {v X Z : ℝ} {p : ℚ} (P N₁ N₂ : ℕ) (hp : 0 ≤ p) (hv : 0 < v)
    (hvR : v < Rs) (hX : Rs < X) (hZ : 0 < v + Z)
    (hF : ContinuousOn F (Icc v Rs)) (hF₀ : ∀ q ∈ Icc v Rs, 0 ≤ F q) :
    (∑ n ∈ Finset.range N₁, (roundedRising P p n : ℝ) * X ^ (-(p : ℝ) - n) *
        ∫ q in v..Rs, F q * q ^ n) +
      (∑ n ∈ Finset.range N₂, (roundedRising P p n : ℝ) * (Rs + Z) ^ (-(p : ℝ) - n) *
        ∫ q in v..Rs, F q * (Rs - q) ^ n) ≤
      ∫ q in v..Rs, F q * ((X - q) ^ (-(p : ℝ)) + (q + Z) ^ (-(p : ℝ))) := by
  have hle : v ≤ Rs := hvR.le
  have hXq : ∀ q ∈ Icc v Rs, 0 < X - q := fun q hq ↦ by linarith [hq.2]
  have hWq : ∀ q ∈ Icc v Rs, 0 < q + Z := fun q hq ↦ by linarith [hq.1]
  -- pointwise series bounds
  have hpt : ∀ q ∈ Icc v Rs,
      F q * (∑ n ∈ Finset.range N₁, (roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n)) +
        F q * (∑ n ∈ Finset.range N₂, (roundedRising P p n : ℝ) * (Rs - q) ^ n *
          (Rs + Z) ^ (-(p : ℝ) - n)) ≤
      F q * ((X - q) ^ (-(p : ℝ)) + (q + Z) ^ (-(p : ℝ))) := by
    intro q hq
    have h₁ := sum_le_sub_rpow P hp (by linarith [hq.1] : (0 : ℝ) ≤ q) (by linarith [hq.2] : q < X) N₁
    have h₂ := sum_le_sub_rpow P hp (by linarith [hq.2] : (0 : ℝ) ≤ Rs - q)
      (by linarith [hq.1] : Rs - q < Rs + Z) N₂
    rw [show Rs + Z - (Rs - q) = q + Z by ring] at h₂
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (hF₀ q hq)
  have hcA : ∀ n : ℕ, ContinuousOn (fun q ↦ F q * q ^ n) (Icc v Rs) := fun n ↦
    hF.mul (continuousOn_id.pow n)
  have hcB : ∀ n : ℕ, ContinuousOn (fun q ↦ F q * (Rs - q) ^ n) (Icc v Rs) := fun n ↦
    hF.mul ((continuousOn_const.sub continuousOn_id).pow n)
  have hcX : ContinuousOn (fun q ↦ (X - q) ^ (-(p : ℝ))) (Icc v Rs) :=
    (continuousOn_const.sub continuousOn_id).rpow_const (fun q hq ↦ Or.inl (hXq q hq).ne')
  have hcW : ContinuousOn (fun q ↦ (q + Z) ^ (-(p : ℝ))) (Icc v Rs) :=
    (continuousOn_id.add continuousOn_const).rpow_const (fun q hq ↦ Or.inl (hWq q hq).ne')
  have iL : IntervalIntegrable (fun q ↦
      F q * (∑ n ∈ Finset.range N₁, (roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n)) +
        F q * (∑ n ∈ Finset.range N₂, (roundedRising P p n : ℝ) * (Rs - q) ^ n *
          (Rs + Z) ^ (-(p : ℝ) - n))) volume v Rs := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    apply ContinuousOn.add
    · exact hF.mul (continuousOn_finsetSum _ fun n _ ↦
        (continuousOn_const.mul (continuousOn_id.pow n)).mul continuousOn_const)
    · exact hF.mul (continuousOn_finsetSum _ fun n _ ↦
        (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul continuousOn_const)
  have iR : IntervalIntegrable (fun q ↦ F q * ((X - q) ^ (-(p : ℝ)) + (q + Z) ^ (-(p : ℝ))))
      volume v Rs :=
    (hF.mul (hcX.add hcW)).intervalIntegrable_of_Icc hle
  have hmono := intervalIntegral.integral_mono_on hle iL iR hpt
  refine le_trans (le_of_eq ?_) hmono
  have iA : ∀ n ∈ Finset.range N₁, IntervalIntegrable
      (fun q ↦ F q * ((roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n))) volume v Rs :=
    fun n _ ↦ (hF.mul ((continuousOn_const.mul (continuousOn_id.pow n)).mul
      continuousOn_const)).intervalIntegrable_of_Icc hle
  have iB : ∀ n ∈ Finset.range N₂, IntervalIntegrable
      (fun q ↦ F q * ((roundedRising P p n : ℝ) * (Rs - q) ^ n * (Rs + Z) ^ (-(p : ℝ) - n)))
        volume v Rs :=
    fun n _ ↦ (hF.mul ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul
      continuousOn_const)).intervalIntegrable_of_Icc hle
  have iS₁ : IntervalIntegrable (fun q ↦ F q * (∑ n ∈ Finset.range N₁,
      (roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n))) volume v Rs :=
    (hF.mul (continuousOn_finsetSum _ fun n _ ↦
      (continuousOn_const.mul (continuousOn_id.pow n)).mul continuousOn_const)).intervalIntegrable_of_Icc hle
  have iS₂ : IntervalIntegrable (fun q ↦ F q * (∑ n ∈ Finset.range N₂,
      (roundedRising P p n : ℝ) * (Rs - q) ^ n * (Rs + Z) ^ (-(p : ℝ) - n))) volume v Rs :=
    (hF.mul (continuousOn_finsetSum _ fun n _ ↦
      (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul
        continuousOn_const)).intervalIntegrable_of_Icc hle
  rw [intervalIntegral.integral_add iS₁ iS₂]
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum iA, intervalIntegral.integral_finsetSum iB]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring
  · apply Finset.sum_congr rfl
    intro n _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring

end PartialBalayage.Maximal.Square
