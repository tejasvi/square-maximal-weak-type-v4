/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandSplitBounds

/-!
# Corner data for the split bounds of the exterior line integrals
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

/-- Enclosures of `R^(-7/40)`, `R^(-47/40)`, `R^(-87/40)`. -/
structure BandConstants where
  pow1 : RationalInterval
  pow0 : RationalInterval
  powS : RationalInterval

namespace BandConstants

def IsValid (C : BandConstants) : Prop :=
  IsPowerEnclosureDeg 40 (33 / 20) (-7) C.pow1.lower C.pow1.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20) (-47) C.pow0.lower C.pow0.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20) (-87) C.powS.lower C.powS.upper

instance (C : BandConstants) : Decidable C.IsValid := by
  unfold IsValid IsPowerEnclosureDeg; infer_instance

def toPowers (C : BandConstants) : BandRadiusPowers := ⟨C.pow1, C.pow0⟩

theorem toPowers_valid {C : BandConstants} (hC : C.IsValid) : C.toPowers.IsValid := ⟨hC.1, hC.2.1⟩

theorem powS_contains {C : BandConstants} (hC : C.IsValid) : C.powS.Contains (Rs ^ (-1 - α)) := by
  have h := hC.2.2.rpow_bounds (by norm_num) (by norm_num)
  simp only [supportRadius]
  refine ⟨?_, ?_⟩ <;> [convert h.1 using 2; convert h.2 using 2] <;> push_cast <;> norm_num

end BandConstants

/-- Corner data of one exterior line integral for the split bounds. -/
structure BandLineData2 where
  a : ℚ
  b : ℚ
  c : ℚ
  n₁ : ℕ
  n₂ : ℕ
  K : ℕ
  xp1 : RationalInterval
  xp2 : RationalInterval
  wp1 : RationalInterval
  wp2 : RationalInterval
  b1 : RationalInterval
  b0 : RationalInterval
  c1 : RationalInterval
  c0 : RationalInterval
  e1 : RationalInterval
  e2 : RationalInterval
  f1 : RationalInterval
  f2 : RationalInterval

namespace BandLineData2

def IsValid (D : BandLineData2) : Prop :=
  0 < D.b ∧ D.b ≤ D.c ∧ D.c ≤ 33 / 20 ∧ 33 / 40 ≤ D.c ∧ D.b < 33 / 20 ∧ 33 / 20 < D.a + D.b ∧
    IsPowerEnclosureDeg 40 (D.a + D.b) (-87) D.xp1.lower D.xp1.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b) (-127) D.xp2.lower D.xp2.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20 + D.a - D.b) (-87) D.wp1.lower D.wp1.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20 + D.a - D.b) (-127) D.wp2.lower D.wp2.upper ∧
    IsPowerEnclosureDeg 40 D.b (-7) D.b1.lower D.b1.upper ∧
    IsPowerEnclosureDeg 40 D.b (-47) D.b0.lower D.b0.upper ∧
    IsPowerEnclosureDeg 40 D.c (-7) D.c1.lower D.c1.upper ∧
    IsPowerEnclosureDeg 40 D.c (-47) D.c0.lower D.c0.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b - 33 / 20) (-47) D.e1.lower D.e1.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b - 33 / 20) (-87) D.e2.lower D.e2.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b - D.c) (-47) D.f1.lower D.f1.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b - D.c) (-87) D.f2.lower D.f2.upper

instance (D : BandLineData2) : Decidable D.IsValid := by
  unfold IsValid IsPowerEnclosureDeg; infer_instance

/-- Interval of the profile moment on `[b, c]`. -/
def profileMomentBetween (C : BandConstants) (b c : ℚ) (B1 C1 : RationalInterval) (n : ℕ) :
    RationalInterval :=
  (((C1.scale (c ^ n)).add (B1.scale (-(b ^ n)))).scale (1 / ((n : ℚ) + 1 - 47 / 40))).add
    (C.pow0.scale (-((c ^ (n + 1) - b ^ (n + 1)) / ((n : ℚ) + 1))))

/-- Interval of the slope moment on `[b, c]`. -/
def slopeMomentBetween (b c : ℚ) (B0 C0 : RationalInterval) (n : ℕ) : RationalInterval :=
  ((C0.scale (c ^ n)).add (B0.scale (-(b ^ n)))).scale (1 / ((n : ℚ) - 47 / 40))

/-- Near coefficients of the profile. -/
def psiCoef (C : BandConstants) (k : ℕ) : RationalInterval :=
  C.pow0.scale (if k = 0 then 0 else roundedRising 96 (47 / 40) k / (33 / 20) ^ k)

/-- Near coefficients of the profile slope. -/
def slopeCoef (C : BandConstants) (k : ℕ) : RationalInterval :=
  C.powS.scale (roundedRising 96 (87 / 40) k / (33 / 20) ^ k)

def lineLower (C : BandConstants) (D : BandLineData2) : ℚ :=
  splitLower (87 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) (D.a + D.b - 33 / 20) (D.a + D.b - D.c)
    D.xp1 D.wp1 D.e1 D.f1 (profileMomentBetween C D.b D.c D.b1 D.c1)
    (profileMomentInterval C.toPowers D.b D.b1) (psiCoef C) D.n₁ D.n₂ D.K

def slopeULower (C : BandConstants) (D : BandLineData2) : ℚ :=
  (1 + 47 / 40) * splitLower (127 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) (D.a + D.b - 33 / 20)
    (D.a + D.b - D.c) D.xp2 D.wp2 D.e2 D.f2 (profileMomentBetween C D.b D.c D.b1 D.c1)
    (profileMomentInterval C.toPowers D.b D.b1) (psiCoef C) D.n₁ D.n₂ D.K

def slopeVLower (C : BandConstants) (D : BandLineData2) : ℚ :=
  (47 / 40) * splitLower (87 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) (D.a + D.b - 33 / 20)
    (D.a + D.b - D.c) D.xp1 D.wp1 D.e1 D.f1 (slopeMomentBetween D.b D.c D.b0 D.c0)
    (slopeMomentInterval C.toPowers D.b D.b0) (slopeCoef C) D.n₁ D.n₂ D.K

theorem profileMomentBetween_contains (C : BandConstants) (hC : C.IsValid) {b c : ℚ}
    (hb : 0 < (b : ℝ)) (hbc : (b : ℝ) ≤ c) (hcR : (c : ℝ) ≤ Rs) {B1 C1 : RationalInterval}
    (hB1 : B1.Contains ((b : ℝ) ^ (1 - α))) (hC1 : C1.Contains ((c : ℝ) ^ (1 - α))) (n : ℕ) :
    (profileMomentBetween C b c B1 C1 n).Contains (∫ q in (b : ℝ)..c, bandPsi q * q ^ n) := by
  rw [integral_bandPsi_mul_pow_between hb hbc hcR]
  have hc0 : (0 : ℝ) < c := hb.trans_le hbc
  have h1 := hC1.scale (c ^ n)
  have h2 := hB1.scale (-(b ^ n))
  have h3 := (h1.add h2).scale (1 / ((n : ℚ) + 1 - 47 / 40))
  have h4 := (C.toPowers.pow0_contains (C.toPowers_valid hC)).scale
    (-((c ^ (n + 1) - b ^ (n + 1)) / ((n : ℚ) + 1)))
  have h5 := h3.add h4
  unfold profileMomentBetween
  convert h5 using 1
  · rfl
  rw [show (n : ℝ) + 1 - α = (n : ℝ) + (1 - α) by ring, rpow_add_nat_mul hc0, rpow_add_nat_mul hb]
  push_cast
  ring

theorem slopeMomentBetween_contains {b c : ℚ} (hb : 0 < (b : ℝ)) (hbc : (b : ℝ) ≤ c)
    {B0 C0 : RationalInterval} (hB0 : B0.Contains ((b : ℝ) ^ (-α)))
    (hC0 : C0.Contains ((c : ℝ) ^ (-α))) (n : ℕ) :
    (slopeMomentBetween b c B0 C0 n).Contains (∫ q in (b : ℝ)..c, q ^ (-1 - α) * q ^ n) := by
  rw [integral_slope_mul_pow_between hb hbc]
  have hc0 : (0 : ℝ) < c := hb.trans_le hbc
  have h1 := hC0.scale (c ^ n)
  have h2 := hB0.scale (-(b ^ n))
  have h3 := (h1.add h2).scale (1 / ((n : ℚ) - 47 / 40))
  unfold slopeMomentBetween
  convert h3 using 1
  rw [show (n : ℝ) - α = (n : ℝ) + (-α) by ring, rpow_add_nat_mul hc0, rpow_add_nat_mul hb]
  push_cast
  ring

theorem psi_expansion {q : ℝ} (hq : Rs / 2 ≤ q) (hqR : q ≤ Rs) (K : ℕ) :
    (∑ k ∈ Finset.range K, (Rs ^ (-α) * ((if k = 0 then 0 else
      (roundedRising 96 (47 / 40) k : ℝ)) / Rs ^ k)) * (Rs - q) ^ k) ≤ bandPsi q := by
  have h := bandPsi_near_ge K hq hqR
  refine le_trans (le_of_eq ?_) h
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  field_simp

theorem slope_expansion {q : ℝ} (hq : Rs / 2 ≤ q) (hqR : q ≤ Rs) (K : ℕ) :
    (∑ k ∈ Finset.range K, (Rs ^ (-1 - α) * ((roundedRising 96 (87 / 40) k : ℝ) / Rs ^ k)) *
      (Rs - q) ^ k) ≤ q ^ (-1 - α) := by
  have h := slopePow_near_ge K hq hqR
  refine le_trans (le_of_eq ?_) h
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  field_simp

theorem psiCoef_contains (C : BandConstants) (hC : C.IsValid) (k : ℕ) :
    (psiCoef C k).Contains (Rs ^ (-α) * ((if k = 0 then 0 else
      (roundedRising 96 (47 / 40) k : ℝ)) / Rs ^ k)) := by
  have h := (C.toPowers.pow0_contains (C.toPowers_valid hC)).scale
    (if k = 0 then 0 else roundedRising 96 (47 / 40) k / (33 / 20) ^ k)
  unfold psiCoef
  convert h using 1
  · rfl
  split_ifs <;> simp only [supportRadius, Rat.cast_zero, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    zero_div, mul_zero, zero_mul] <;> ring

theorem psiCoef_lower_nonneg (C : BandConstants) (hC : C.IsValid) (k : ℕ) : 0 ≤ (psiCoef C k).lower := by
  unfold psiCoef RationalInterval.scale
  have h0 : 0 ≤ (if k = 0 then 0 else roundedRising 96 (47 / 40) k / (33 / 20) ^ k : ℚ) := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (roundedRising_nonneg 96 (by norm_num) k) (by positivity)
  rw [if_pos h0]
  exact mul_nonneg h0 hC.2.1.1

theorem slopeCoef_contains (C : BandConstants) (hC : C.IsValid) (k : ℕ) :
    (slopeCoef C k).Contains (Rs ^ (-1 - α) * ((roundedRising 96 (87 / 40) k : ℝ) / Rs ^ k)) := by
  have h := (C.powS_contains hC).scale (roundedRising 96 (87 / 40) k / (33 / 20) ^ k)
  unfold slopeCoef
  convert h using 1
  simp only [supportRadius, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  ring

theorem slopeCoef_lower_nonneg (C : BandConstants) (hC : C.IsValid) (k : ℕ) :
    0 ≤ (slopeCoef C k).lower := by
  unfold slopeCoef RationalInterval.scale
  have h0 : 0 ≤ (roundedRising 96 (87 / 40) k / (33 / 20) ^ k : ℚ) :=
    div_nonneg (roundedRising_nonneg 96 (by norm_num) k) (by positivity)
  rw [if_pos h0]
  exact mul_nonneg h0 hC.2.2.1

/-- Splitting the `q`-form into the three parts of the split bound. -/
theorem q_form_split {F : ℝ → ℝ} {b c X Z r : ℝ} (hb : 0 < b) (hbc : b ≤ c) (hcR : c ≤ Rs)
    (hX : Rs < X) (hZ : 0 < b + Z) (hF : ContinuousOn F (Icc b Rs)) :
    (∫ q in b..Rs, F q * ((X - q) ^ (-r) + (q + Z) ^ (-r))) =
      (∫ q in b..c, F q * (X - q) ^ (-r)) + (∫ q in c..Rs, F q * (X - q) ^ (-r)) +
        ∫ q in b..Rs, F q * (q + Z) ^ (-r) := by
  have hbR : b ≤ Rs := hbc.trans hcR
  have hcX : ContinuousOn (fun q ↦ F q * (X - q) ^ (-r)) (Icc b Rs) :=
    hF.mul ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun q hq ↦ Or.inl (by linarith [hq.2] : (0 : ℝ) < X - q).ne'))
  have hcW : ContinuousOn (fun q ↦ F q * (q + Z) ^ (-r)) (Icc b Rs) :=
    hF.mul ((continuousOn_id.add continuousOn_const).rpow_const
      (fun q hq ↦ Or.inl (by linarith [hq.1] : (0 : ℝ) < q + Z).ne'))
  have e1 : (∫ q in b..Rs, F q * ((X - q) ^ (-r) + (q + Z) ^ (-r))) =
      (∫ q in b..Rs, F q * (X - q) ^ (-r)) + ∫ q in b..Rs, F q * (q + Z) ^ (-r) := by
    rw [← intervalIntegral.integral_add (hcX.intervalIntegrable_of_Icc hbR)
      (hcW.intervalIntegrable_of_Icc hbR)]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals
    ((hcX.mono (Icc_subset_Icc le_rfl hcR)).intervalIntegrable_of_Icc hbc)
    ((hcX.mono (Icc_subset_Icc hbc le_rfl)).intervalIntegrable_of_Icc hcR)]

variable {C : BandConstants} {D : BandLineData2}

private theorem facts (hD : D.IsValid) :
    (0 : ℝ) < D.b ∧ (D.b : ℝ) ≤ D.c ∧ (D.c : ℝ) ≤ Rs ∧ Rs / 2 ≤ (D.c : ℝ) ∧ (D.b : ℝ) < Rs ∧
      Rs < (D.a : ℝ) + D.b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hD
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_, ?_, ?_, ?_⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr h3; simp only [supportRadius]; push_cast at h; exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr h4; simp only [supportRadius]; push_cast at h ⊢; linarith
  · have h := (Rat.cast_lt (K := ℝ)).mpr h5; simp only [supportRadius]; push_cast at h; exact h
  · have h := (Rat.cast_lt (K := ℝ)).mpr h6; simp only [supportRadius]; push_cast at h; exact h

private theorem enc_c {q : ℚ} (hq : 0 < q) {n : ℤ} {I : RationalInterval}
    (h : IsPowerEnclosureDeg 40 q n I.lower I.upper) : I.Contains ((q : ℝ) ^ ((n : ℝ) / 40)) := by
  have := h.rpow_bounds (by norm_num) hq.le
  exact ⟨by simpa using this.1, by simpa using this.2⟩

private theorem hpj87 : ∀ j : ℕ, (j : ℝ) - ((87 / 40 : ℚ) : ℝ) ≠ -1 := by
  intro j h
  push_cast at h
  have h2 : (40 : ℝ) * j = 47 := by linarith
  have h3 : (40 * j : ℕ) = 47 := by exact_mod_cast h2
  omega

private theorem hpj127 : ∀ j : ℕ, (j : ℝ) - ((127 / 40 : ℚ) : ℝ) ≠ -1 := by
  intro j h
  push_cast at h
  have h2 : (40 : ℝ) * j = 87 := by linarith
  have h3 : (40 * j : ℕ) = 87 := by exact_mod_cast h2
  omega

/-- The common enclosure facts of a valid corner. -/
private theorem encs (hD : D.IsValid) :
    D.xp1.Contains ((((D.a + D.b : ℚ) : ℝ)) ^ (-((87 / 40 : ℚ) : ℝ))) ∧
    D.xp2.Contains ((((D.a + D.b : ℚ) : ℝ)) ^ (-((127 / 40 : ℚ) : ℝ))) ∧
    D.wp1.Contains ((((33 / 20 + D.a - D.b : ℚ) : ℝ)) ^ (-((87 / 40 : ℚ) : ℝ))) ∧
    D.wp2.Contains ((((33 / 20 + D.a - D.b : ℚ) : ℝ)) ^ (-((127 / 40 : ℚ) : ℝ))) ∧
    D.b1.Contains ((D.b : ℝ) ^ (1 - α)) ∧ D.b0.Contains ((D.b : ℝ) ^ (-α)) ∧
    D.c1.Contains ((D.c : ℝ) ^ (1 - α)) ∧ D.c0.Contains ((D.c : ℝ) ^ (-α)) ∧
    D.e1.Contains ((((D.a + D.b : ℚ) : ℝ) - Rs) ^ (1 - ((87 / 40 : ℚ) : ℝ))) ∧
    D.e2.Contains ((((D.a + D.b : ℚ) : ℝ) - Rs) ^ (1 - ((127 / 40 : ℚ) : ℝ))) ∧
    D.f1.Contains ((((D.a + D.b : ℚ) : ℝ) - D.c) ^ (1 - ((87 / 40 : ℚ) : ℝ))) ∧
    D.f2.Contains ((((D.a + D.b : ℚ) : ℝ) - D.c) ^ (1 - ((127 / 40 : ℚ) : ℝ))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, x1, x2, w1, w2, b1, b0, c1, c0, e1, e2, f1, f2⟩ := hD
  have hX : (0 : ℚ) < D.a + D.b := by linarith
  have hW : (0 : ℚ) < 33 / 20 + D.a - D.b := by linarith
  have hE : (0 : ℚ) < D.a + D.b - 33 / 20 := by linarith
  have hF : (0 : ℚ) < D.a + D.b - D.c := by linarith
  have hc : (0 : ℚ) < D.c := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert enc_c hX x1 using 2; push_cast; norm_num
  · convert enc_c hX x2 using 2; push_cast; norm_num
  · convert enc_c hW w1 using 2; push_cast; norm_num
  · convert enc_c hW w2 using 2; push_cast; norm_num
  · convert enc_c h1 b1 using 2; push_cast; norm_num
  · convert enc_c h1 b0 using 2; push_cast; norm_num
  · convert enc_c hc c1 using 2; push_cast; norm_num
  · convert enc_c hc c0 using 2; push_cast; norm_num
  · convert enc_c hE e1 using 2 <;> push_cast <;> (try simp only [supportRadius]) <;> norm_num
  · convert enc_c hE e2 using 2 <;> push_cast <;> (try simp only [supportRadius]) <;> norm_num
  · convert enc_c hF f1 using 2 <;> push_cast <;> norm_num
  · convert enc_c hF f2 using 2 <;> push_cast <;> norm_num

theorem lineLower_le (hC : C.IsValid) (hD : D.IsValid) : (lineLower C D : ℝ) ≤ bandLine D.a D.b := by
  obtain ⟨hb, hbc, hcR, hc2, hbR, hab⟩ := facts hD
  obtain ⟨x1, -, w1, -, b1, -, c1, -, e1, -, f1, -⟩ := encs hD
  have hx0 : 0 ≤ D.xp1.lower := hD.2.2.2.2.2.2.1.1
  have hw0 : 0 ≤ D.wp1.lower := hD.2.2.2.2.2.2.2.2.1.1
  rw [bandLine_q hb hbR hab]
  have he : (-1 - (47 / 40 : ℝ)) = -((87 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  rw [he, q_form_split hb hbc hcR hab (by linarith) (BandLineData.continuousOn_bandPsi hb)]
  have hZ : (D.a : ℝ) - D.b = ((D.a + D.b : ℚ) : ℝ) - 2 * D.b := by push_cast; ring
  rw [hZ, show (D.a : ℝ) + D.b = ((D.a + D.b : ℚ) : ℝ) by push_cast; ring]
  exact splitLower_le (F := bandPsi) (by norm_num) hpj87 hb hbc hc2 hcR (by push_cast; linarith)
    (by push_cast; simp only [supportRadius]; ring) (by push_cast; linarith)
    (BandLineData.continuousOn_bandPsi hb) (fun q _ ↦ bandPsi_nonneg q) x1 hx0 w1 hw0 e1 f1
    (fun n ↦ profileMomentBetween_contains C hC hb hbc hcR b1 c1 n)
    (fun n ↦ profileMomentInterval_contains C.toPowers (C.toPowers_valid hC) hb hbR.le b1 n)
    (psiCoef_contains C hC) (psiCoef_lower_nonneg C hC)
    (fun q hq K ↦ psi_expansion (hc2.trans hq.1) hq.2 K) D.n₁ D.n₂ D.K

theorem slopeULower_le (hC : C.IsValid) (hD : D.IsValid) :
    (slopeULower C D : ℝ) ≤ bandSlopeU D.a D.b := by
  obtain ⟨hb, hbc, hcR, hc2, hbR, hab⟩ := facts hD
  obtain ⟨-, x2, -, w2, b1, -, c1, -, -, e2, -, f2⟩ := encs hD
  have hx0 : 0 ≤ D.xp2.lower := hD.2.2.2.2.2.2.2.1.1
  have hw0 : 0 ≤ D.wp2.lower := hD.2.2.2.2.2.2.2.2.2.1.1
  rw [bandSlopeU_q hb hbR hab]
  have he : (-2 - (47 / 40 : ℝ)) = -((127 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  have hfac : (∫ q in (D.b : ℝ)..Rs, bandPsi q * ((1 + 47 / 40) *
      (((D.a : ℝ) + D.b - q) ^ (-2 - (47 / 40 : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-2 - (47 / 40 : ℝ))))) =
      (1 + 47 / 40) * ∫ q in (D.b : ℝ)..Rs, bandPsi q *
        ((((D.a + D.b : ℚ) : ℝ) - q) ^ (-((127 / 40 : ℚ) : ℝ)) +
          (q + (((D.a + D.b : ℚ) : ℝ) - 2 * D.b)) ^ (-((127 / 40 : ℚ) : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul, he]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    push_cast
    ring_nf
  rw [hfac, q_form_split hb hbc hcR (by push_cast; linarith) (by push_cast; linarith)
    (BandLineData.continuousOn_bandPsi hb)]
  have key := splitLower_le (F := bandPsi) (p := 127 / 40) (by norm_num) hpj127 hb hbc hc2 hcR
    (X := D.a + D.b) (W := 33 / 20 + D.a - D.b) (by push_cast; linarith)
    (by push_cast; simp only [supportRadius]; ring) (by push_cast; linarith)
    (BandLineData.continuousOn_bandPsi hb) (fun q _ ↦ bandPsi_nonneg q) x2 hx0 w2 hw0 e2 f2
    (fun n ↦ profileMomentBetween_contains C hC hb hbc hcR b1 c1 n)
    (fun n ↦ profileMomentInterval_contains C.toPowers (C.toPowers_valid hC) hb hbR.le b1 n)
    (psiCoef_contains C hC) (psiCoef_lower_nonneg C hC)
    (fun q hq K ↦ psi_expansion (hc2.trans hq.1) hq.2 K) D.n₁ D.n₂ D.K
  unfold slopeULower
  rw [Rat.cast_mul]
  have h0 : ((1 + 47 / 40 : ℚ) : ℝ) = 1 + 47 / 40 := by push_cast; ring
  rw [h0]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

theorem slopeVLower_le (hC : C.IsValid) (hD : D.IsValid) :
    (slopeVLower C D : ℝ) ≤ bandSlopeV D.a D.b := by
  obtain ⟨hb, hbc, hcR, hc2, hbR, hab⟩ := facts hD
  obtain ⟨x1, -, w1, -, -, b0, -, c0, e1, -, f1, -⟩ := encs hD
  have hx0 : 0 ≤ D.xp1.lower := hD.2.2.2.2.2.2.1.1
  have hw0 : 0 ≤ D.wp1.lower := hD.2.2.2.2.2.2.2.2.1.1
  rw [bandSlopeV_q hb hbR hab]
  have he : (-1 - (47 / 40 : ℝ)) = -((87 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  have hfac : (∫ q in (D.b : ℝ)..Rs, q ^ (-1 - (47 / 40 : ℝ)) * ((47 / 40) *
      (((D.a : ℝ) + D.b - q) ^ (-1 - (47 / 40 : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-1 - (47 / 40 : ℝ))))) =
      (47 / 40) * ∫ q in (D.b : ℝ)..Rs, q ^ (-1 - (47 / 40 : ℝ)) *
        ((((D.a + D.b : ℚ) : ℝ) - q) ^ (-((87 / 40 : ℚ) : ℝ)) +
          (q + (((D.a + D.b : ℚ) : ℝ) - 2 * D.b)) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    rw [← he]
    push_cast
    ring_nf
  rw [hfac, q_form_split hb hbc hcR (by push_cast; linarith) (by push_cast; linarith)
    (BandLineData.continuousOn_slopePow hb)]
  have key := splitLower_le (F := fun q : ℝ ↦ q ^ (-1 - (47 / 40 : ℝ))) (p := 87 / 40) (by norm_num)
    hpj87 hb hbc hc2 hcR (X := D.a + D.b) (W := 33 / 20 + D.a - D.b) (by push_cast; linarith)
    (by push_cast; simp only [supportRadius]; ring) (by push_cast; linarith)
    (BandLineData.continuousOn_slopePow hb) (fun q hq ↦ Real.rpow_nonneg (hb.trans_le hq.1).le _) x1 hx0 w1 hw0
    e1 f1 (fun n ↦ slopeMomentBetween_contains hb hbc b0 c0 n)
    (fun n ↦ slopeMomentInterval_contains C.toPowers (C.toPowers_valid hC) hb hbR.le b0 n)
    (slopeCoef_contains C hC) (slopeCoef_lower_nonneg C hC)
    (fun q hq K ↦ slope_expansion (hc2.trans hq.1) hq.2 K) D.n₁ D.n₂ D.K
  unfold slopeVLower
  rw [Rat.cast_mul]
  have h0 : ((47 / 40 : ℚ) : ℝ) = 47 / 40 := by push_cast; ring
  rw [h0]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

end BandLineData2

end PartialBalayage.Maximal.Square
