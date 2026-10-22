/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Tactic

/-!
# Fourier elliptic regularity for represented weak Laplace equations

A genuine `L²` function whose distributional Laplacian is represented by an `L²` function
belongs to the Fourier Sobolev space of order two. Its distributional second derivatives are
therefore represented by genuine `L²` functions. This is the global elliptic step used after
interior cutoff localization; it does not assert zero-boundary membership of gradients.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal Laplacian LineDeriv

namespace PartialBalayage.Linear

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [CompleteSpace F]

section Normed

variable [NormedSpace ℂ F]

omit [CompleteSpace F] in
/-- Addition of genuine temperate symbols gives addition of their Fourier multipliers. -/
theorem fourierMultiplierCLM_add_apply {a b : E → ℂ}
    (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (a + b) u =
      fourierMultiplierCLM F a u + fourierMultiplierCLM F b u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add ha hb,
    add_apply, FourierTransform.fourierInv_add]

omit [CompleteSpace F] in
/-- The order-two Bessel potential is the actual elliptic differential operator,
with the coefficient dictated by mathlib's Fourier normalization. -/
theorem besselPotential_two_eq_laplacian (u : 𝓢'(E, F)) :
    besselPotential E F 2 u = u -
      (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • (Δ u) := by
  have hsymbol : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2))) =
      (fun _ : E ↦ (1 : ℂ)) + (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  rw [besselPotential, hsymbol, fourierMultiplierCLM_add_apply (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_const, smul_apply, ContinuousLinearMap.id_apply, one_smul,
    laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul, smul_smul]
  have hcoefficient : Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
      Complex.ofReal (-(2 * Real.pi) ^ 2) = -1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    field_simp; norm_num
  rw [hcoefficient, neg_one_smul, sub_neg_eq_add]

/-- `u` and its represented Laplacian in `L²` give genuine order-two Sobolev regularity. -/
theorem memSobolev_two_of_laplacian_memSobolev_zero {u : 𝓢'(E, F)}
    (hu : MemSobolev 0 2 u) (hΔ : MemSobolev 0 2 (Δ u)) :
    MemSobolev 2 2 u := by
  have h := hu.sub (hΔ.smul (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)))
  rw [← besselPotential_two_eq_laplacian] at h
  simpa only [memSobolev_besselPotential_iff, add_zero] using h

/-- The distributional Laplacian equation here involves the actual `L²` embedding. -/
theorem memSobolev_two_of_L2_laplacian (u g : Lp F 2 (volume : Measure E))
    (hΔ : Δ (u : 𝓢'(E, F)) = (g : 𝓢'(E, F))) :
    MemSobolev 2 2 (u : 𝓢'(E, F)) := by
  apply memSobolev_two_of_laplacian_memSobolev_zero
  · exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  · exact memSobolev_zero_iff.mpr ⟨g, hΔ⟩

/-- An ordinary integral weak Laplace equation implies the actual represented
 distributional equation, rather than requiring it as an extra regularity hypothesis. -/
theorem laplacian_L2_eq_of_weak_integrals (u g : Lp F 2 (volume : Measure E))
    (hweak : ∀ φ : 𝓢(E, ℂ),
      (∫ x, (Δ φ) x • (u x : F)) = ∫ x, φ x • (g x : F)) :
    Δ (u : 𝓢'(E, F)) = (g : 𝓢'(E, F)) := by
  ext φ
  simpa only [laplacian_apply_apply, Lp.toTemperedDistribution_apply] using hweak φ

end Normed

section Hilbert

variable [InnerProductSpace ℂ F]

/-- Actual weak integral solutions with `L²` forcing have represented second
 distributional derivatives in every pair of directions. -/
theorem exists_L2_second_derivative_of_weak_laplacian
    (u g : Lp F 2 (volume : Measure E))
    (hweak : ∀ φ : 𝓢(E, ℂ),
      (∫ x, (Δ φ) x • (u x : F)) = ∫ x, φ x • (g x : F)) (v w : E) :
    ∃ H : Lp F 2 (volume : Measure E),
      ∂_{w} (∂_{v} (u : 𝓢'(E, F))) = (H : 𝓢'(E, F)) := by
  have hu := memSobolev_two_of_L2_laplacian u g
    (laplacian_L2_eq_of_weak_integrals u g hweak)
  have hv : MemSobolev 1 2 (∂_{v} (u : 𝓢'(E, F))) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using (hu.lineDerivOp (m := v))
  have hw : MemSobolev 0 2 (∂_{w} (∂_{v} (u : 𝓢'(E, F)))) := by
    simpa only [sub_self] using (hv.lineDerivOp (m := w))
  exact memSobolev_zero_iff.mp hw

end Hilbert

end PartialBalayage.Linear
