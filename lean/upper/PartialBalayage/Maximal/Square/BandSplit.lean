/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandCorner

/-!
# Fast-converging split of the exterior line integrals

`∫_v^R F(q) (X - q)^(-p) dq` is split at `c ∈ [v, R]`. On `[v, c]` the binomial series in `q / X`
converges with ratio `c / X`. On `[c, R]` the profile is expanded in `(R - q) / R` with
nonnegative coefficients and integrated exactly against `(X - q)^(-p)`; with `w = R - q`,
`ε = X - R` the integrals `∫_0^η w^k (ε + w)^(-p) dw` are elementary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

/-- The first part of the series bound on `[v, c]`. -/
theorem q_series_le_X {F : ℝ → ℝ} {v c X : ℝ} {p : ℚ} (P N : ℕ) (hp : 0 ≤ p) (hv : 0 < v)
    (hvc : v ≤ c) (hcX : c < X) (hF : ContinuousOn F (Icc v c)) (hF₀ : ∀ q ∈ Icc v c, 0 ≤ F q) :
    (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * X ^ (-(p : ℝ) - n) *
        ∫ q in v..c, F q * q ^ n) ≤
      ∫ q in v..c, F q * (X - q) ^ (-(p : ℝ)) := by
  have hpt : ∀ q ∈ Icc v c,
      F q * (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n)) ≤
        F q * (X - q) ^ (-(p : ℝ)) := fun q hq ↦
    mul_le_mul_of_nonneg_left (sum_le_sub_rpow P hp (by linarith [hq.1]) (by linarith [hq.2]) N)
      (hF₀ q hq)
  have iL : IntervalIntegrable (fun q ↦ F q * (∑ n ∈ Finset.range N,
      (roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n))) volume v c :=
    (hF.mul (continuousOn_finsetSum _ fun n _ ↦
      (continuousOn_const.mul (continuousOn_id.pow n)).mul continuousOn_const)).intervalIntegrable_of_Icc hvc
  have iR : IntervalIntegrable (fun q ↦ F q * (X - q) ^ (-(p : ℝ))) volume v c :=
    (hF.mul ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun q hq ↦ Or.inl (by linarith [hq.2] : (0 : ℝ) < X - q).ne'))).intervalIntegrable_of_Icc hvc
  refine le_trans (le_of_eq ?_) (intervalIntegral.integral_mono_on hvc iL iR hpt)
  have iA : ∀ n ∈ Finset.range N, IntervalIntegrable
      (fun q ↦ F q * ((roundedRising P p n : ℝ) * q ^ n * X ^ (-(p : ℝ) - n))) volume v c :=
    fun n _ ↦ (hF.mul ((continuousOn_const.mul (continuousOn_id.pow n)).mul
      continuousOn_const)).intervalIntegrable_of_Icc hvc
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum iA]
  apply Finset.sum_congr rfl
  intro n _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  ring

/-- The elementary near integral `∫_c^R (R - q)^k (X - q)^(-p) dq`. -/
theorem integral_near (k : ℕ) {c X r : ℝ} (hcR : c ≤ Rs) (hX : Rs < X) (hr : ∀ j : ℕ, (j : ℝ) - r ≠ -1) :
    (∫ q in c..Rs, (Rs - q) ^ k * (X - q) ^ (-r)) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (-(X - Rs)) ^ (k - j) *
        (((X - c) ^ ((j : ℝ) + 1 - r) - (X - Rs) ^ ((j : ℝ) + 1 - r)) / ((j : ℝ) + 1 - r)) := by
  have hε : 0 < X - Rs := by linarith
  -- substitute q = X - z
  have hsub : (∫ q in c..Rs, (Rs - q) ^ k * (X - q) ^ (-r)) =
      ∫ z in (X - Rs)..(X - c), (z - (X - Rs)) ^ k * z ^ (-r) := by
    rw [← intervalIntegral.integral_comp_sub_left (fun z ↦ (z - (X - Rs)) ^ k * z ^ (-r)) X]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring_nf
  rw [hsub]
  have hexp : ∀ z : ℝ, (z - (X - Rs)) ^ k = ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * (-(X - Rs)) ^ (k - j) * z ^ j := by
    intro z
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hle : X - Rs ≤ X - c := by linarith
  simp_rw [hexp, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have hpow : ∀ z ∈ uIcc (X - Rs) (X - c),
        (k.choose j : ℝ) * (-(X - Rs)) ^ (k - j) * z ^ j * z ^ (-r) =
          (k.choose j : ℝ) * (-(X - Rs)) ^ (k - j) * z ^ ((j : ℝ) - r) := by
      intro z hz
      rw [uIcc_of_le hle] at hz
      have hz0 : 0 < z := hε.trans_le hz.1
      rw [mul_assoc, show z ^ j = z ^ (j : ℝ) from (Real.rpow_natCast z j).symm,
        ← Real.rpow_add hz0]
      ring_nf
    rw [intervalIntegral.integral_congr hpow, intervalIntegral.integral_const_mul,
      integral_rpow]
    · ring_nf
    · right
      refine ⟨hr j, ?_⟩
      rw [uIcc_of_le hle]
      intro h
      exact absurd h.1 (not_le.mpr hε)
  · intro j _
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    apply ContinuousOn.mul (continuousOn_const.mul (continuousOn_id.pow j))
    apply ContinuousOn.rpow_const continuousOn_id
    intro z hz; left; exact (hε.trans_le hz.1).ne'

/-- Near the support radius the profile is above its truncated expansion. -/
theorem bandPsi_near_ge (K : ℕ) {q : ℝ} (hq : Rs / 2 ≤ q) (hqR : q ≤ Rs) :
    Rs ^ (-α) * (∑ k ∈ Finset.range K, (if k = 0 then 0 else (roundedRising 96 (47 / 40) k : ℝ)) *
      ((Rs - q) / Rs) ^ k) ≤ bandPsi q := by
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  have hq0 : 0 < q := by linarith
  have ht0 : 0 ≤ (Rs - q) / Rs := div_nonneg (by linarith) hR.le
  have ht1 : (Rs - q) / Rs < 1 := by rw [div_lt_one hR]; linarith
  have hs := roundedRising_sum_le_rpow 96 (p := 47 / 40) (by norm_num) ht0 ht1 K
  have h1 : 1 - (Rs - q) / Rs = q / Rs := by field_simp; ring
  rw [h1] at hs
  rw [bandPsi_eq_on hq0 hqR]
  have hpow : q ^ (-α) = Rs ^ (-α) * (q / Rs) ^ (-α) := by
    rw [Real.div_rpow hq0.le hR.le, Real.rpow_neg hR.le, Real.rpow_neg hq0.le]
    field_simp
  rw [hpow]
  have hcast : ((47 / 40 : ℚ) : ℝ) = α := by push_cast; ring
  rw [hcast] at hs
  have hsplit : (∑ k ∈ Finset.range K, (if k = 0 then 0 else (roundedRising 96 (47 / 40) k : ℝ)) *
      ((Rs - q) / Rs) ^ k) ≤ (∑ k ∈ Finset.range K, (roundedRising 96 (47 / 40) k : ℝ) *
      ((Rs - q) / Rs) ^ k) - 1 + (if K = 0 then 1 else 0) := by
    cases K with
    | zero => simp
    | succ K =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp [roundedRising]
  calc
    _ ≤ Rs ^ (-α) * ((q / Rs) ^ (-α) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hR.le _)
      refine hsplit.trans ?_
      split_ifs with hK
      · subst hK; simp only [Finset.range_zero, Finset.sum_empty]
        have : (1 : ℝ) ≤ (q / Rs) ^ (-α) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hq0 hR) ((div_le_one hR).mpr hqR)
            (by norm_num)
        linarith
      · linarith
    _ = _ := by ring

/-- Near the support radius the profile slope is above its truncated expansion. -/
theorem slopePow_near_ge (K : ℕ) {q : ℝ} (hq : Rs / 2 ≤ q) (hqR : q ≤ Rs) :
    Rs ^ (-1 - α) * (∑ k ∈ Finset.range K, (roundedRising 96 (87 / 40) k : ℝ) *
      ((Rs - q) / Rs) ^ k) ≤ q ^ (-1 - α) := by
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  have hq0 : 0 < q := by linarith
  have ht0 : 0 ≤ (Rs - q) / Rs := div_nonneg (by linarith) hR.le
  have ht1 : (Rs - q) / Rs < 1 := by rw [div_lt_one hR]; linarith
  have hs := roundedRising_sum_le_rpow 96 (p := 87 / 40) (by norm_num) ht0 ht1 K
  have h1 : 1 - (Rs - q) / Rs = q / Rs := by field_simp; ring
  rw [h1] at hs
  have hcast : -((87 / 40 : ℚ) : ℝ) = -1 - α := by push_cast; ring
  rw [hcast] at hs
  have hpow : q ^ (-1 - α) = Rs ^ (-1 - α) * (q / Rs) ^ (-1 - α) := by
    rw [Real.div_rpow hq0.le hR.le]
    have : (0 : ℝ) < Rs ^ (-1 - α) := Real.rpow_pos_of_pos hR _
    field_simp
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hR.le _)

/-- The second part of the series bound on `[v, R]`. -/
theorem q_series_le_W {F : ℝ → ℝ} {v Z : ℝ} {p : ℚ} (P N : ℕ) (hp : 0 ≤ p) (hv : 0 < v)
    (hvR : v ≤ Rs) (hZ : 0 < v + Z) (hF : ContinuousOn F (Icc v Rs))
    (hF₀ : ∀ q ∈ Icc v Rs, 0 ≤ F q) :
    (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * (Rs + Z) ^ (-(p : ℝ) - n) *
        ∫ q in v..Rs, F q * (Rs - q) ^ n) ≤
      ∫ q in v..Rs, F q * (q + Z) ^ (-(p : ℝ)) := by
  have hpt : ∀ q ∈ Icc v Rs,
      F q * (∑ n ∈ Finset.range N, (roundedRising P p n : ℝ) * (Rs - q) ^ n *
        (Rs + Z) ^ (-(p : ℝ) - n)) ≤ F q * (q + Z) ^ (-(p : ℝ)) := by
    intro q hq
    have h₂ := sum_le_sub_rpow P hp (by linarith [hq.2] : (0 : ℝ) ≤ Rs - q)
      (by linarith [hq.1] : Rs - q < Rs + Z) N
    rw [show Rs + Z - (Rs - q) = q + Z by ring] at h₂
    exact mul_le_mul_of_nonneg_left h₂ (hF₀ q hq)
  have iL : IntervalIntegrable (fun q ↦ F q * (∑ n ∈ Finset.range N,
      (roundedRising P p n : ℝ) * (Rs - q) ^ n * (Rs + Z) ^ (-(p : ℝ) - n))) volume v Rs :=
    (hF.mul (continuousOn_finsetSum _ fun n _ ↦
      (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul
        continuousOn_const)).intervalIntegrable_of_Icc hvR
  have iR : IntervalIntegrable (fun q ↦ F q * (q + Z) ^ (-(p : ℝ))) volume v Rs :=
    (hF.mul ((continuousOn_id.add continuousOn_const).rpow_const
      (fun q hq ↦ Or.inl (by linarith [hq.1] : (0 : ℝ) < q + Z).ne'))).intervalIntegrable_of_Icc hvR
  refine le_trans (le_of_eq ?_) (intervalIntegral.integral_mono_on hvR iL iR hpt)
  have iB : ∀ n ∈ Finset.range N, IntervalIntegrable
      (fun q ↦ F q * ((roundedRising P p n : ℝ) * (Rs - q) ^ n * (Rs + Z) ^ (-(p : ℝ) - n)))
        volume v Rs :=
    fun n _ ↦ (hF.mul ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow n)).mul
      continuousOn_const)).intervalIntegrable_of_Icc hvR
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum iB]
  apply Finset.sum_congr rfl
  intro n _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  ring

/-- The near part: pointwise expansion integrated against `(X - q)^(-p)`. -/
theorem near_series_le {F : ℝ → ℝ} {c X r : ℝ} (K : ℕ) (a : ℕ → ℝ) (hc : Rs / 2 ≤ c)
    (hcR : c ≤ Rs) (hX : Rs < X) (hF : ContinuousOn F (Icc c Rs))
    (hexp : ∀ q ∈ Icc c Rs, (∑ k ∈ Finset.range K, a k * (Rs - q) ^ k) ≤ F q) :
    (∑ k ∈ Finset.range K, a k * ∫ q in c..Rs, (Rs - q) ^ k * (X - q) ^ (-r)) ≤
      ∫ q in c..Rs, F q * (X - q) ^ (-r) := by
  have hXq : ∀ q ∈ Icc c Rs, 0 < X - q := fun q hq ↦ by linarith [hq.2]
  have hcont : ContinuousOn (fun q ↦ (X - q) ^ (-r)) (Icc c Rs) :=
    (continuousOn_const.sub continuousOn_id).rpow_const (fun q hq ↦ Or.inl (hXq q hq).ne')
  have hpt : ∀ q ∈ Icc c Rs,
      (∑ k ∈ Finset.range K, a k * (Rs - q) ^ k) * (X - q) ^ (-r) ≤ F q * (X - q) ^ (-r) :=
    fun q hq ↦ mul_le_mul_of_nonneg_right (hexp q hq) (Real.rpow_nonneg (hXq q hq).le _)
  have iL : IntervalIntegrable (fun q ↦ (∑ k ∈ Finset.range K, a k * (Rs - q) ^ k) * (X - q) ^ (-r))
      volume c Rs :=
    ((continuousOn_finsetSum _ fun k _ ↦ continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).pow k)).mul hcont).intervalIntegrable_of_Icc hcR
  have iR : IntervalIntegrable (fun q ↦ F q * (X - q) ^ (-r)) volume c Rs :=
    (hF.mul hcont).intervalIntegrable_of_Icc hcR
  refine le_trans (le_of_eq ?_) (intervalIntegral.integral_mono_on hcR iL iR hpt)
  have iA : ∀ k ∈ Finset.range K, IntervalIntegrable
      (fun q ↦ a k * (Rs - q) ^ k * (X - q) ^ (-r)) volume c Rs :=
    fun k _ ↦ ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow k)).mul
      hcont).intervalIntegrable_of_Icc hcR
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum iA]
  apply Finset.sum_congr rfl
  intro k _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q _
  simp only
  ring

end PartialBalayage.Maximal.Square
