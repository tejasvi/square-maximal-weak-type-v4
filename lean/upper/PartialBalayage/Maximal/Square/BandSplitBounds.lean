/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.BandSplit

/-!
# Rational split bounds of the exterior line integrals

The three parts of the split (far series on `[b, c]`, exact near expansion on `[c, R]`,
reflected series on `[b, R]`) are evaluated over the rationals from interval moments and
40th-power enclosures, and bounded below termwise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace PartialBalayage.Maximal.Square

local notation "Rs" => supportRadius
local notation "α" => (47 / 40 : ℝ)

/-- Interval of `∫_c^R (R - q)^k (X - q)^(-p) dq` from enclosures `E ∋ ε^(1-p)`, `F ∋ (X - c)^(1-p)`,
`ε = X - R`, `Xc = X - c`. -/
def nearIntegralInterval (p ε Xc : ℚ) (E F : RationalInterval) (k : ℕ) : RationalInterval :=
  RationalInterval.sum (Finset.range (k + 1)) (fun j ↦
    ((F.scale (Xc ^ j)).add (E.scale (-(ε ^ j)))).scale (binomQ k j * (-ε) ^ (k - j) / ((j : ℚ) + 1 - p)))

theorem nearIntegralInterval_contains {p : ℚ} (hp : ∀ j : ℕ, (j : ℝ) - (p : ℝ) ≠ -1) {c X : ℚ}
    (hcR : (c : ℝ) ≤ Rs) (hX : Rs < (X : ℝ)) {E F : RationalInterval}
    (hE : E.Contains (((X : ℝ) - Rs) ^ (1 - (p : ℝ))))
    (hF : F.Contains (((X : ℝ) - c) ^ (1 - (p : ℝ)))) (k : ℕ) :
    (nearIntegralInterval p (X - 33 / 20) (X - c) E F k).Contains
      (∫ q in (c : ℝ)..Rs, (Rs - q) ^ k * ((X : ℝ) - q) ^ (-(p : ℝ))) := by
  rw [integral_near k hcR hX hp]
  unfold nearIntegralInterval
  apply RationalInterval.Contains.sum
  intro j _
  have hε : (0 : ℝ) < (X : ℝ) - Rs := by linarith
  have hXc : (0 : ℝ) < (X : ℝ) - c := by linarith
  have h := ((hF.scale ((X - c) ^ j)).add (hE.scale (-((X - 33 / 20) ^ j)))).scale
    (binomQ k j * (-(X - 33 / 20)) ^ (k - j) / ((j : ℚ) + 1 - p))
  convert h using 1
  rw [show ((j : ℝ) + 1 - (p : ℝ)) = (j : ℝ) + (1 - (p : ℝ)) by ring, Real.rpow_add hXc,
    Real.rpow_add hε, Real.rpow_natCast, Real.rpow_natCast]
  push_cast
  rw [binomQ_eq]
  simp only [supportRadius]
  ring

/-- The generic split lower bound. -/
def splitLower (p : ℚ) (X W ε Xc : ℚ) (xp wp E F : RationalInterval) (Mf Mb A : ℕ → RationalInterval)
    (n₁ n₂ K : ℕ) : ℚ :=
  seriesFold (bandCoefficients p n₁) 0 (fun n ↦ (1 / X) ^ n * (xp.nonnegMul (Mf n)).lower) +
    (∑ k ∈ Finset.range K, ((A k).nonnegMul (nearIntegralInterval p ε Xc E F k)).lower) +
    seriesFold (bandCoefficients p n₂) 0
      (fun n ↦ (1 / W) ^ n * (wp.nonnegMul (reflectedMomentInterval Mb n)).lower)

private theorem term_le {p : ℚ} (hp : 0 ≤ p) {Y : ℚ} (hY : 0 < (Y : ℝ)) {yp I : RationalInterval}
    {x : ℝ} (hyp : yp.Contains ((Y : ℝ) ^ (-(p : ℝ)))) (hyp0 : 0 ≤ yp.lower) (hI : I.Contains x)
    (n : ℕ) :
    (roundedRising 96 p n : ℝ) * ((1 / (Y : ℝ)) ^ n * ((yp.nonnegMul I).lower : ℝ)) ≤
      (roundedRising 96 p n : ℝ) * (Y : ℝ) ^ (-(p : ℝ) - n) * x := by
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

/-- The split lower bound is below the three integrals. -/
theorem splitLower_le {F : ℝ → ℝ} {p : ℚ} (hp : 0 ≤ p) (hpj : ∀ j : ℕ, (j : ℝ) - (p : ℝ) ≠ -1)
    {b c X W : ℚ} (hb : 0 < (b : ℝ)) (hbc : (b : ℝ) ≤ c) (hc : Rs / 2 ≤ (c : ℝ)) (hcR : (c : ℝ) ≤ Rs)
    (hX : Rs < (X : ℝ)) (hW : (W : ℝ) = Rs + ((X : ℝ) - 2 * b)) (hbW : 0 < (b : ℝ) + ((X : ℝ) - 2 * b))
    (hFc : ContinuousOn F (Icc (b : ℝ) Rs)) (hF₀ : ∀ q ∈ Icc (b : ℝ) Rs, 0 ≤ F q)
    {xp wp E Fi : RationalInterval} (hxp : xp.Contains ((X : ℝ) ^ (-(p : ℝ)))) (hxp0 : 0 ≤ xp.lower)
    (hwp : wp.Contains ((W : ℝ) ^ (-(p : ℝ)))) (hwp0 : 0 ≤ wp.lower)
    (hE : E.Contains (((X : ℝ) - Rs) ^ (1 - (p : ℝ))))
    (hFi : Fi.Contains (((X : ℝ) - c) ^ (1 - (p : ℝ))))
    {Mf Mb A : ℕ → RationalInterval} (hMf : ∀ n, (Mf n).Contains (∫ q in (b : ℝ)..c, F q * q ^ n))
    (hMb : ∀ n, (Mb n).Contains (∫ q in (b : ℝ)..Rs, F q * q ^ n))
    {a : ℕ → ℝ} (hA : ∀ k, (A k).Contains (a k)) (hA0 : ∀ k, 0 ≤ (A k).lower)
    (hexp : ∀ q ∈ Icc (c : ℝ) Rs, ∀ K : ℕ, (∑ k ∈ Finset.range K, a k * (Rs - q) ^ k) ≤ F q)
    (n₁ n₂ K : ℕ) :
    (splitLower p X W (X - 33 / 20) (X - c) xp wp E Fi Mf Mb A n₁ n₂ K : ℝ) ≤
      (∫ q in (b : ℝ)..c, F q * ((X : ℝ) - q) ^ (-(p : ℝ))) +
        (∫ q in (c : ℝ)..Rs, F q * ((X : ℝ) - q) ^ (-(p : ℝ))) +
          ∫ q in (b : ℝ)..Rs, F q * (q + ((X : ℝ) - 2 * b)) ^ (-(p : ℝ)) := by
  unfold splitLower
  rw [seriesFold_bandCoefficients, seriesFold_bandCoefficients]
  push_cast
  have hX0 : (0 : ℝ) < X := by linarith [supportRadius_pos]
  have hW0 : (0 : ℝ) < W := by rw [hW]; linarith [supportRadius_pos]
  have hbR : (b : ℝ) ≤ Rs := hbc.trans hcR
  have h₁ := q_series_le_X (F := F) (v := b) (c := c) (X := X) (p := p) 96 n₁ hp hb hbc
    (by linarith) (hFc.mono (Icc_subset_Icc le_rfl hcR)) (fun q hq ↦ hF₀ q ⟨hq.1, hq.2.trans hcR⟩)
  have h₃ := q_series_le_W (F := F) (v := b) (Z := (X : ℝ) - 2 * b) (p := p) 96 n₂ hp hb hbR hbW
    hFc hF₀
  rw [← hW] at h₃
  have h₂ := near_series_le (F := F) (c := c) (X := X) (r := p) K a hc hcR hX
    (hFc.mono (Icc_subset_Icc hbc le_rfl)) (fun q hq ↦ hexp q hq K)
  have hMw : ∀ n, (reflectedMomentInterval Mb n).Contains (∫ q in (b : ℝ)..Rs, F q * (Rs - q) ^ n) :=
    fun n ↦ reflectedMomentInterval_contains hbR hFc hMb n
  have hI : ∀ k, (nearIntegralInterval p (X - 33 / 20) (X - c) E Fi k).Contains
      (∫ q in (c : ℝ)..Rs, (Rs - q) ^ k * ((X : ℝ) - q) ^ (-(p : ℝ))) :=
    fun k ↦ nearIntegralInterval_contains hpj hcR hX hE hFi k
  apply add_le_add (add_le_add _ _) _
  · refine le_trans (Finset.sum_le_sum fun n _ ↦ term_le hp hX0 hxp hxp0 (hMf n) n) h₁
  · refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) h₂
    exact ((hA k).nonnegMul (hI k) (hA0 k)).1
  · refine le_trans (Finset.sum_le_sum fun n _ ↦ term_le hp hW0 hwp hwp0 (hMw n) n) h₃

end PartialBalayage.Maximal.Square
