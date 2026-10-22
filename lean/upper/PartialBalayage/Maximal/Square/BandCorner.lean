/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandMoments
public import PartialBalayage.Maximal.Square.PowerEnclosure
public import PartialBalayage.Maximal.Square.IntervalFiniteSum

/-!
# Rational lower bounds of the exterior line integrals at a corner

The moments are enclosed by rational intervals built from 40th-power enclosures of `R^(1-α)`,
`R^(-α)`, `b^(1-α)` and `b^(-α)`, and the truncated positive series are evaluated over the
rationals. The resulting numbers are lower bounds of `bandLine`, `bandSlopeU` and `bandSlopeV`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

/-- Binomial coefficients by descending factorials (linear-time evaluation). -/
def binomQ (n j : ℕ) : ℚ := (Nat.descFactorial n j / Nat.factorial j : ℕ)

theorem binomQ_eq (n j : ℕ) : (binomQ n j : ℝ) = (n.choose j : ℝ) := by
  unfold binomQ
  rw [← Nat.choose_eq_descFactorial_div_factorial]
  push_cast; rfl

/-- One-pass weighted sum `∑ cs[n] f (k + n)`. -/
def seriesFold : List ℚ → ℕ → (ℕ → ℚ) → ℚ
  | [], _, _ => 0
  | c :: cs, k, f => c * f k + seriesFold cs (k + 1) f

theorem seriesFold_eq (cs : List ℚ) (k : ℕ) (f : ℕ → ℚ) :
    seriesFold cs k f = ∑ n ∈ Finset.range cs.length, cs.getD n 0 * f (k + n) := by
  induction cs generalizing k with
  | nil => simp [seriesFold]
  | cons c cs ih =>
    rw [seriesFold, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [show k + 1 + n = k + (n + 1) by omega]

/-- The rounded series coefficients for `(1 - t)^(-p)`. -/
def bandCoefficients (p : ℚ) (N : ℕ) : List ℚ := roundedRisingList 96 p (fun _ b ↦ b) N

theorem seriesFold_bandCoefficients (p : ℚ) (N : ℕ) (f : ℕ → ℚ) :
    seriesFold (bandCoefficients p N) 0 f = ∑ n ∈ Finset.range N, roundedRising 96 p n * f n := by
  rw [seriesFold_eq]
  have hl : (bandCoefficients p N).length = N := by
    simp [bandCoefficients, roundedRisingList, length_roundedRisingListAux]
  rw [hl]
  apply Finset.sum_congr rfl
  intro n hn
  rw [zero_add, bandCoefficients, getD_roundedRisingList _ _ _ (Finset.mem_range.mp hn)]

/-- Shared enclosure data of the radius powers. -/
structure BandRadiusPowers where
  pow1 : RationalInterval
  pow0 : RationalInterval

namespace BandRadiusPowers

def IsValid (C : BandRadiusPowers) : Prop :=
  IsPowerEnclosureDeg 40 (33 / 20) (-7) C.pow1.lower C.pow1.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20) (-47) C.pow0.lower C.pow0.upper

instance (C : BandRadiusPowers) : Decidable C.IsValid := by
  unfold IsValid IsPowerEnclosureDeg; infer_instance

theorem pow1_contains {C : BandRadiusPowers} (hC : C.IsValid) :
    C.pow1.Contains (Rs ^ (1 - α)) := by
  have h := hC.1.rpow_bounds (by norm_num) (by norm_num)
  simp only [supportRadius]
  refine ⟨?_, ?_⟩ <;> [convert h.1 using 2; convert h.2 using 2] <;> push_cast <;> norm_num

theorem pow0_contains {C : BandRadiusPowers} (hC : C.IsValid) :
    C.pow0.Contains (Rs ^ (-α)) := by
  have h := hC.2.rpow_bounds (by norm_num) (by norm_num)
  simp only [supportRadius]
  refine ⟨?_, ?_⟩ <;> [convert h.1 using 2; convert h.2 using 2] <;> push_cast <;> norm_num

end BandRadiusPowers

/-- Interval of the profile moment `∫_b^R Ψ(q) q^n dq`. -/
def profileMomentInterval (C : BandRadiusPowers) (b : ℚ) (B1 : RationalInterval) (n : ℕ) :
    RationalInterval :=
  (((C.pow1.scale ((33 / 20) ^ n)).add (B1.scale (-(b ^ n)))).scale (1 / ((n : ℚ) + 1 - 47 / 40))).add
    (C.pow0.scale (-(((33 / 20) ^ (n + 1) - b ^ (n + 1)) / ((n : ℚ) + 1))))

/-- Interval of the slope moment `∫_b^R q^(-1-α) q^n dq`. -/
def slopeMomentInterval (C : BandRadiusPowers) (b : ℚ) (B0 : RationalInterval) (n : ℕ) :
    RationalInterval :=
  ((C.pow0.scale ((33 / 20) ^ n)).add (B0.scale (-(b ^ n)))).scale (1 / ((n : ℚ) - 47 / 40))

/-- Interval of a reflected moment `∫_b^R F(q) (R - q)^n dq` from intervals of the power moments. -/
def reflectedMomentInterval (M : ℕ → RationalInterval) (n : ℕ) : RationalInterval :=
  RationalInterval.sum (Finset.range (n + 1))
    (fun j ↦ (M j).scale (binomQ n j * (33 / 20) ^ (n - j) * (-1) ^ j))

theorem rpow_add_nat_mul {x : ℝ} (hx : 0 < x) (n : ℕ) (r : ℝ) :
    x ^ ((n : ℝ) + r) = x ^ n * x ^ r := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

theorem profileMomentInterval_contains (C : BandRadiusPowers) (hC : C.IsValid) {b : ℚ}
    (hb : 0 < (b : ℝ)) (hbR : (b : ℝ) ≤ Rs) {B1 : RationalInterval}
    (hB1 : B1.Contains ((b : ℝ) ^ (1 - α))) (n : ℕ) :
    (profileMomentInterval C b B1 n).Contains (∫ q in (b : ℝ)..Rs, bandPsi q * q ^ n) := by
  rw [integral_bandPsi_mul_pow hb hbR]
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  have h1 := (C.pow1_contains hC).scale ((33 / 20) ^ n)
  have h2 := hB1.scale (-(b ^ n))
  have h3 := (h1.add h2).scale (1 / ((n : ℚ) + 1 - 47 / 40))
  have h4 := (C.pow0_contains hC).scale (-(((33 / 20) ^ (n + 1) - b ^ (n + 1)) / ((n : ℚ) + 1)))
  have h5 := h3.add h4
  unfold profileMomentInterval
  convert h5 using 1
  rw [show (n : ℝ) + 1 - α = (n : ℝ) + (1 - α) by ring, rpow_add_nat_mul hR, rpow_add_nat_mul hb]
  simp only [supportRadius]
  push_cast
  ring

theorem slopeMomentInterval_contains (C : BandRadiusPowers) (hC : C.IsValid) {b : ℚ}
    (hb : 0 < (b : ℝ)) (hbR : (b : ℝ) ≤ Rs) {B0 : RationalInterval}
    (hB0 : B0.Contains ((b : ℝ) ^ (-α))) (n : ℕ) :
    (slopeMomentInterval C b B0 n).Contains (∫ q in (b : ℝ)..Rs, q ^ (-1 - α) * q ^ n) := by
  rw [integral_slope_mul_pow hb hbR]
  have hR : (0 : ℝ) < Rs := supportRadius_pos
  have h1 := (C.pow0_contains hC).scale ((33 / 20) ^ n)
  have h2 := hB0.scale (-(b ^ n))
  have h3 := (h1.add h2).scale (1 / ((n : ℚ) - 47 / 40))
  unfold slopeMomentInterval
  convert h3 using 1
  rw [show (n : ℝ) - α = (n : ℝ) + (-α) by ring, rpow_add_nat_mul hR, rpow_add_nat_mul hb]
  simp only [supportRadius]
  push_cast
  ring

theorem reflectedMomentInterval_contains {F : ℝ → ℝ} {b : ℝ} (hbR : b ≤ Rs)
    (hF : ContinuousOn F (Icc b Rs)) {M : ℕ → RationalInterval}
    (hM : ∀ j, (M j).Contains (∫ q in b..Rs, F q * q ^ j)) (n : ℕ) :
    (reflectedMomentInterval M n).Contains (∫ q in b..Rs, F q * (Rs - q) ^ n) := by
  rw [integral_mul_sub_pow hbR hF n]
  unfold reflectedMomentInterval
  apply RationalInterval.Contains.sum
  intro j _
  have h := (hM j).scale (binomQ n j * (33 / 20) ^ (n - j) * (-1) ^ j)
  convert h using 1
  push_cast
  rw [binomQ_eq]
  simp only [supportRadius]

/-- Enclosure data for one exterior line integral at a corner `(a, b)`, `0 < b < R < a + b`. -/
structure BandLineData where
  a : ℚ
  b : ℚ
  n₁ : ℕ
  n₂ : ℕ
  xp1 : RationalInterval
  xp2 : RationalInterval
  wp1 : RationalInterval
  wp2 : RationalInterval
  b1 : RationalInterval
  b0 : RationalInterval

namespace BandLineData

/-- The exact checks of the enclosures. -/
def IsValid (D : BandLineData) : Prop :=
  0 < D.b ∧ D.b < 33 / 20 ∧ 33 / 20 < D.a + D.b ∧
    IsPowerEnclosureDeg 40 (D.a + D.b) (-87) D.xp1.lower D.xp1.upper ∧
    IsPowerEnclosureDeg 40 (D.a + D.b) (-127) D.xp2.lower D.xp2.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20 + D.a - D.b) (-87) D.wp1.lower D.wp1.upper ∧
    IsPowerEnclosureDeg 40 (33 / 20 + D.a - D.b) (-127) D.wp2.lower D.wp2.upper ∧
    IsPowerEnclosureDeg 40 D.b (-7) D.b1.lower D.b1.upper ∧
    IsPowerEnclosureDeg 40 D.b (-47) D.b0.lower D.b0.upper

instance (D : BandLineData) : Decidable D.IsValid := by
  unfold IsValid IsPowerEnclosureDeg; infer_instance

/-- Generic truncated two-part series with interval moments. -/
def seriesLower (p : ℚ) (X W : ℚ) (xp wp : RationalInterval) (M : ℕ → RationalInterval)
    (n₁ n₂ : ℕ) : ℚ :=
  seriesFold (bandCoefficients p n₁) 0 (fun n ↦ (1 / X) ^ n * (xp.nonnegMul (M n)).lower) +
    seriesFold (bandCoefficients p n₂) 0
      (fun n ↦ (1 / W) ^ n * (wp.nonnegMul (reflectedMomentInterval M n)).lower)

/-- Lower bound of the line integral. -/
def lineLower (C : BandRadiusPowers) (D : BandLineData) : ℚ :=
  seriesLower (87 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) D.xp1 D.wp1
    (profileMomentInterval C D.b D.b1) D.n₁ D.n₂

/-- Lower bound of the first slope integral. -/
def slopeULower (C : BandRadiusPowers) (D : BandLineData) : ℚ :=
  (1 + 47 / 40) * seriesLower (127 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) D.xp2 D.wp2
    (profileMomentInterval C D.b D.b1) D.n₁ D.n₂

/-- Lower bound of the second slope integral. -/
def slopeVLower (C : BandRadiusPowers) (D : BandLineData) : ℚ :=
  (47 / 40) * seriesLower (87 / 40) (D.a + D.b) (33 / 20 + D.a - D.b) D.xp1 D.wp1
    (slopeMomentInterval C D.b D.b0) D.n₁ D.n₂

end BandLineData

/-- The termwise lower bound of the generic series. -/
theorem seriesLower_le {p : ℚ} (hp : 0 ≤ p) {X W : ℚ} (hX : 0 < (X : ℝ)) (hW : 0 < (W : ℝ))
    {xp wp : RationalInterval} (hxp : xp.Contains ((X : ℝ) ^ (-(p : ℝ))))
    (hwp : wp.Contains ((W : ℝ) ^ (-(p : ℝ)))) (hxp0 : 0 ≤ xp.lower) (hwp0 : 0 ≤ wp.lower)
    {M : ℕ → RationalInterval} {m mR : ℕ → ℝ} (hM : ∀ n, (M n).Contains (m n))
    (hMR : ∀ n, (reflectedMomentInterval M n).Contains (mR n)) (n₁ n₂ : ℕ) :
    (BandLineData.seriesLower p X W xp wp M n₁ n₂ : ℝ) ≤
      (∑ n ∈ Finset.range n₁, (roundedRising 96 p n : ℝ) * (X : ℝ) ^ (-(p : ℝ) - n) * m n) +
        ∑ n ∈ Finset.range n₂, (roundedRising 96 p n : ℝ) * (W : ℝ) ^ (-(p : ℝ) - n) * mR n := by
  unfold BandLineData.seriesLower
  rw [seriesFold_bandCoefficients, seriesFold_bandCoefficients]
  push_cast
  have hterm : ∀ {Y : ℚ} (hY : 0 < (Y : ℝ)) {yp I : RationalInterval} {x : ℝ}
      (hyp : yp.Contains ((Y : ℝ) ^ (-(p : ℝ)))) (hyp0 : 0 ≤ yp.lower) (hI : I.Contains x) (n : ℕ),
      (roundedRising 96 p n : ℝ) * ((1 / (Y : ℝ)) ^ n * ((yp.nonnegMul I).lower : ℝ)) ≤
        (roundedRising 96 p n : ℝ) * (Y : ℝ) ^ (-(p : ℝ) - n) * x := by
    intro Y hY yp I x hyp hyp0 hI n
    have hc : (0 : ℝ) ≤ roundedRising 96 p n := by exact_mod_cast roundedRising_nonneg 96 hp n
    have hprod := (hyp.nonnegMul hI hyp0).1
    have hpow : (Y : ℝ) ^ (-(p : ℝ) - n) = (Y : ℝ) ^ (-(p : ℝ)) * (1 / (Y : ℝ)) ^ n := by
      rw [Real.rpow_sub hY, Real.rpow_natCast, one_div_pow, div_eq_mul_one_div]
    rw [hpow, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc
    have h1 : (0 : ℝ) ≤ (1 / (Y : ℝ)) ^ n := by positivity
    calc
      _ ≤ (1 / (Y : ℝ)) ^ n * ((Y : ℝ) ^ (-(p : ℝ)) * x) := mul_le_mul_of_nonneg_left hprod h1
      _ = _ := by ring
  apply add_le_add
  · apply Finset.sum_le_sum
    intro n _
    exact hterm hX hxp hxp0 (hM n) n
  · apply Finset.sum_le_sum
    intro n _
    exact hterm hW hwp hwp0 (hMR n) n

namespace BandLineData

variable {C : BandRadiusPowers} {D : BandLineData}

theorem continuousOn_bandPsi {b : ℝ} (hb : 0 < b) : ContinuousOn bandPsi (Icc b Rs) := by
  have h : ContinuousOn (fun q : ℝ ↦ q ^ (-(47 / 40 : ℝ)) - Rs ^ (-(47 / 40 : ℝ))) (Icc b Rs) :=
    (continuousOn_id.rpow_const fun q hq ↦ Or.inl (hb.trans_le hq.1).ne').sub continuousOn_const
  exact h.sup continuousOn_const

private theorem enc_contains {d : ℕ} (hd : d ≠ 0) {q : ℚ} (hq : 0 < q) {n : ℤ} {I : RationalInterval}
    (h : IsPowerEnclosureDeg d q n I.lower I.upper) : I.Contains ((q : ℝ) ^ ((n : ℝ) / d)) :=
  h.rpow_bounds hd hq.le

private theorem enc_lower_nonneg {d : ℕ} {q : ℚ} {n : ℤ} {I : RationalInterval}
    (h : IsPowerEnclosureDeg d q n I.lower I.upper) : 0 ≤ I.lower := h.1

theorem lineLower_le (hC : C.IsValid) (hD : D.IsValid) : (lineLower C D : ℝ) ≤ bandLine D.a D.b := by
  obtain ⟨hb, hbR, hab, hx1, hx2, hw1, hw2, hb1, hb0⟩ := hD
  have hb' : (0 : ℝ) < D.b := by exact_mod_cast hb
  have hbR' : (D.b : ℝ) < Rs := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hbR
    simp only [supportRadius]; push_cast at h; exact h
  have hab' : Rs < (D.a : ℝ) + D.b := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hab
    simp only [supportRadius]; push_cast at h; exact h
  have hX : (0 : ℚ) < D.a + D.b := by linarith
  have hW : (0 : ℚ) < 33 / 20 + D.a - D.b := by linarith
  rw [bandLine_q hb' hbR' hab']
  have he : (-1 - (47 / 40 : ℝ)) = -((87 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  rw [he]
  have hs := q_series_le (F := bandPsi) (v := D.b) (X := D.a + D.b) (Z := D.a - D.b)
    (p := 87 / 40) 96 D.n₁ D.n₂ (by norm_num) hb' hbR' hab' (by linarith [hab', hbR'])
    (continuousOn_bandPsi hb') (fun q _ ↦ bandPsi_nonneg q)
  have hxc : D.xp1.Contains (((D.a + D.b : ℚ) : ℝ) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hX hx1
    convert h using 2; push_cast; norm_num
  have hwc : D.wp1.Contains (((33 / 20 + D.a - D.b : ℚ) : ℝ) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hW hw1
    convert h using 2; push_cast; norm_num
  have hb1c : D.b1.Contains ((D.b : ℝ) ^ (1 - α)) := by
    have h := enc_contains (by norm_num) hb hb1
    convert h using 2; push_cast; norm_num
  have hl := seriesLower_le (p := 87 / 40) (by norm_num) (by exact_mod_cast hX) (by exact_mod_cast hW)
    hxc hwc (enc_lower_nonneg hx1) (enc_lower_nonneg hw1)
    (fun n ↦ profileMomentInterval_contains C hC hb' hbR'.le hb1c n)
    (fun n ↦ reflectedMomentInterval_contains hbR'.le (continuousOn_bandPsi hb')
      (fun j ↦ profileMomentInterval_contains C hC hb' hbR'.le hb1c j) n) D.n₁ D.n₂
  refine hl.trans (le_trans (le_of_eq ?_) hs)
  push_cast
  simp only [supportRadius]
  ring_nf

private theorem corner_facts (hD : D.IsValid) :
    (0 : ℝ) < D.b ∧ (D.b : ℝ) < Rs ∧ Rs < (D.a : ℝ) + D.b ∧ (0 : ℚ) < D.a + D.b ∧
      (0 : ℚ) < 33 / 20 + D.a - D.b := by
  obtain ⟨hb, hbR, hab, -⟩ := hD
  refine ⟨by exact_mod_cast hb, ?_, ?_, by linarith, by linarith⟩
  · have h := (Rat.cast_lt (K := ℝ)).mpr hbR
    simp only [supportRadius]; push_cast at h; exact h
  · have h := (Rat.cast_lt (K := ℝ)).mpr hab
    simp only [supportRadius]; push_cast at h; exact h

theorem slopeULower_le (hC : C.IsValid) (hD : D.IsValid) :
    (slopeULower C D : ℝ) ≤ bandSlopeU D.a D.b := by
  obtain ⟨hb', hbR', hab', hX, hW⟩ := corner_facts hD
  obtain ⟨hb, -, -, -, hx2, -, hw2, hb1, -⟩ := hD
  rw [bandSlopeU_q hb' hbR' hab']
  have he : (-2 - (47 / 40 : ℝ)) = -((127 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  have hfac : (∫ q in (D.b : ℝ)..Rs, bandPsi q * ((1 + 47 / 40) *
      (((D.a : ℝ) + D.b - q) ^ (-2 - (47 / 40 : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-2 - (47 / 40 : ℝ))))) =
      (1 + 47 / 40) * ∫ q in (D.b : ℝ)..Rs, bandPsi q *
        (((D.a : ℝ) + D.b - q) ^ (-((127 / 40 : ℚ) : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-((127 / 40 : ℚ) : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul, he]
    apply intervalIntegral.integral_congr
    intro q _
    simp only
    ring
  rw [hfac]
  have hs := q_series_le (F := bandPsi) (v := D.b) (X := D.a + D.b) (Z := D.a - D.b)
    (p := 127 / 40) 96 D.n₁ D.n₂ (by norm_num) hb' hbR' hab' (by linarith [hab', hbR'])
    (continuousOn_bandPsi hb') (fun q _ ↦ bandPsi_nonneg q)
  have hxc : D.xp2.Contains (((D.a + D.b : ℚ) : ℝ) ^ (-((127 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hX hx2
    convert h using 2; push_cast; norm_num
  have hwc : D.wp2.Contains (((33 / 20 + D.a - D.b : ℚ) : ℝ) ^ (-((127 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hW hw2
    convert h using 2; push_cast; norm_num
  have hb1c : D.b1.Contains ((D.b : ℝ) ^ (1 - α)) := by
    have h := enc_contains (by norm_num) hb hb1
    convert h using 2; push_cast; norm_num
  have hl := seriesLower_le (p := 127 / 40) (by norm_num) (by exact_mod_cast hX) (by exact_mod_cast hW)
    hxc hwc (enc_lower_nonneg hx2) (enc_lower_nonneg hw2)
    (fun n ↦ profileMomentInterval_contains C hC hb' hbR'.le hb1c n)
    (fun n ↦ reflectedMomentInterval_contains hbR'.le (continuousOn_bandPsi hb')
      (fun j ↦ profileMomentInterval_contains C hC hb' hbR'.le hb1c j) n) D.n₁ D.n₂
  have key := hl.trans (le_trans (le_of_eq (by push_cast; simp only [supportRadius]; ring_nf)) hs)
  unfold slopeULower
  rw [Rat.cast_mul]
  have h0 : ((1 + 47 / 40 : ℚ) : ℝ) = 1 + 47 / 40 := by push_cast; ring
  rw [h0]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

theorem continuousOn_slopePow {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun q : ℝ ↦ q ^ (-1 - α)) (Icc b Rs) :=
  continuousOn_id.rpow_const fun q hq ↦ Or.inl (hb.trans_le hq.1).ne'

theorem slopeVLower_le (hC : C.IsValid) (hD : D.IsValid) :
    (slopeVLower C D : ℝ) ≤ bandSlopeV D.a D.b := by
  obtain ⟨hb', hbR', hab', hX, hW⟩ := corner_facts hD
  obtain ⟨hb, -, -, hx1, -, hw1, -, -, hb0⟩ := hD
  rw [bandSlopeV_q hb' hbR' hab']
  have he : (-1 - (47 / 40 : ℝ)) = -((87 / 40 : ℚ) : ℝ) := by push_cast; norm_num
  have hfac : (∫ q in (D.b : ℝ)..Rs, q ^ (-1 - (47 / 40 : ℝ)) * ((47 / 40) *
      (((D.a : ℝ) + D.b - q) ^ (-1 - (47 / 40 : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-1 - (47 / 40 : ℝ))))) =
      (47 / 40) * ∫ q in (D.b : ℝ)..Rs, q ^ (-1 - (47 / 40 : ℝ)) *
        (((D.a : ℝ) + D.b - q) ^ (-((87 / 40 : ℚ) : ℝ)) + (q + ((D.a : ℝ) - D.b)) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro _q _
    simp only
    rw [← he]
    ring
  rw [hfac]
  have hs := q_series_le (F := fun q : ℝ ↦ q ^ (-1 - (47 / 40 : ℝ))) (v := D.b) (X := D.a + D.b)
    (Z := D.a - D.b) (p := 87 / 40) 96 D.n₁ D.n₂ (by norm_num) hb' hbR' hab'
    (by linarith [hab', hbR']) (continuousOn_slopePow hb')
    (fun q hq ↦ Real.rpow_nonneg (hb'.trans_le hq.1).le _)
  have hxc : D.xp1.Contains (((D.a + D.b : ℚ) : ℝ) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hX hx1
    convert h using 2; push_cast; norm_num
  have hwc : D.wp1.Contains (((33 / 20 + D.a - D.b : ℚ) : ℝ) ^ (-((87 / 40 : ℚ) : ℝ))) := by
    have h := enc_contains (by norm_num) hW hw1
    convert h using 2; push_cast; norm_num
  have hb0c : D.b0.Contains ((D.b : ℝ) ^ (-α)) := by
    have h := enc_contains (by norm_num) hb hb0
    convert h using 2; push_cast; norm_num
  have hl := seriesLower_le (p := 87 / 40) (by norm_num) (by exact_mod_cast hX) (by exact_mod_cast hW)
    hxc hwc (enc_lower_nonneg hx1) (enc_lower_nonneg hw1)
    (fun n ↦ slopeMomentInterval_contains C hC hb' hbR'.le hb0c n)
    (fun n ↦ reflectedMomentInterval_contains hbR'.le (continuousOn_slopePow hb')
      (fun j ↦ slopeMomentInterval_contains C hC hb' hbR'.le hb0c j) n) D.n₁ D.n₂
  have key := hl.trans (le_trans (le_of_eq (by push_cast; simp only [supportRadius]; ring_nf)) hs)
  unfold slopeVLower
  rw [Rat.cast_mul]
  have h0 : ((47 / 40 : ℚ) : ℝ) = 47 / 40 := by push_cast; ring
  rw [h0]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

end BandLineData

end PartialBalayage.Maximal.Square
