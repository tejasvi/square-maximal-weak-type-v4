/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.BetaIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Genuine positive real beta integrals

Positive real beta integrals agree with mathlib's complex beta integral and
therefore with the actual real Gamma quotient. This uses ordinary convergent
integrals and no continuation of the beta integral to negative parameters.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

/-- The actual real beta integrand. -/
def realBetaIntegrand (u v t : ℝ) : ℝ := t ^ (u - 1) * (1 - t) ^ (v - 1)

/-- The actual positive-parameter real beta integral. -/
def realBetaIntegral (u v : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, realBetaIntegrand u v t

theorem ofReal_realBetaIntegrand {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) (u v : ℝ) :
    (realBetaIntegrand u v t : ℂ) =
      (t : ℂ) ^ ((u : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v : ℂ) - 1) := by
  simp only [realBetaIntegrand, Complex.ofReal_mul,
    Complex.ofReal_cpow ht, Complex.ofReal_cpow (sub_nonneg.mpr ht₁)]
  push_cast
  rfl

theorem ofReal_realBetaIntegral (u v : ℝ) :
    (realBetaIntegral u v : ℂ) = Complex.betaIntegral (u : ℂ) (v : ℂ) := by
  rw [realBetaIntegral, ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  exact ofReal_realBetaIntegrand ht.1.le ht.2.le u v

/-- Positive real parameters give the actual convergent beta integral. -/
theorem intervalIntegrable_realBetaIntegrand {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (realBetaIntegrand u v) volume 0 1 := by
  have hi := Complex.betaIntegral_convergent (by simpa using hu : 0 < (u : ℂ).re)
    (by simpa using hv : 0 < (v : ℂ).re)
  have hir : IntervalIntegrable (fun t : ℝ ↦
      ((t : ℂ) ^ ((u : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v : ℂ) - 1)).re) volume 0 1 :=
    ⟨hi.1.re, hi.2.re⟩
  apply hir.congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have ht₀ : 0 ≤ t := ht.1.le
  have ht₁ : t ≤ 1 := ht.2.le
  have he := congrArg Complex.re (ofReal_realBetaIntegrand ht₀ ht₁ u v)
  simpa only [Complex.ofReal_re] using he.symm

/-- The genuine positive real beta integral equals its actual Gamma quotient. -/
theorem realBetaIntegral_eq_Gamma_mul_div {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    realBetaIntegral u v = Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [ofReal_realBetaIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div (u : ℂ) (v : ℂ)
      (by simpa using hu) (by simpa using hv)]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.Gamma_ofReal]

theorem realBetaIntegral_symm (u v : ℝ) : realBetaIntegral v u = realBetaIntegral u v := by
  apply Complex.ofReal_injective
  rw [ofReal_realBetaIntegral, ofReal_realBetaIntegral, Complex.betaIntegral_symm]

theorem squareBetaIntegral_eq_realBetaIntegral :
    squareBetaIntegral = realBetaIntegral (6 / 5) (6 / 5) := by
  simp only [squareBetaIntegral, realBetaIntegral, squareBetaIntegrand, realBetaIntegrand,
    show (6 / 5 : ℝ) - 1 = 1 / 5 by ring]

end PartialBalayage.Maximal.Square
