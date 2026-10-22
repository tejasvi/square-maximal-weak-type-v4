/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.DiamondAverageCap
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Simultaneous bounds for actual averages over every diamond radius

The genuine unnormalized region integrals are monotone in radius. Rational
radius estimates therefore extend to all positive radii using only continuity
of the explicit planar area. A countable intersection makes the actual
almost-everywhere contact bounds simultaneous.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- A monotone mass function inherits its actual quadratic upper bound from rational radii. -/
theorem le_quadratic_of_positive_rational_bounds (m : ℝ → ℝ) (hm : Monotone m) (C : ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) → m q ≤ 2 * (q : ℝ) ^ 2 * C)
    {r : ℝ} (hr : 0 < r) : m r ≤ 2 * r ^ 2 * C := by
  by_contra h
  have hlt : 2 * r ^ 2 * C < m r := lt_of_not_ge h
  have hc : ContinuousAt (fun s : ℝ ↦ 2 * s ^ 2 * C) r := by fun_prop
  have hn : ∀ᶠ s in 𝓝 r, 2 * s ^ 2 * C < m r := hc.eventually (Iio_mem_nhds hlt)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hn
  obtain ⟨q, hrq, hqδ⟩ := exists_rat_btwn (show r < r + δ by linarith)
  have hdist : dist (q : ℝ) r < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hrq)]
    linarith
  exact not_lt_of_ge ((hm hrq.le).trans (hb q (hr.trans hrq))) (hnear hdist)

/-- Genuine nonnegative diamond region integrals are monotone in radius. -/
theorem monotone_integral_closedEuclideanDiamond (f : E → ℝ) (hf : Integrable f)
    (hf₀ : ∀ᵐ y, 0 ≤ f y) (x : E) :
    Monotone (fun r ↦ ∫ y in closedEuclideanDiamond x r, f y) := by
  intro r s hrs
  apply setIntegral_mono_set hf.integrableOn (ae_restrict_of_ae hf₀)
  exact Eventually.of_forall (fun y hy ↦ hy.trans hrs)

/-- Bounds for the actual positive rational diamond averages control every positive radius. -/
theorem diamondAverage_le_of_positive_rational_bounds (f : E → ℝ) (hf : Integrable f)
    (hf₀ : ∀ᵐ y, 0 ≤ f y) (x : E) (C : ℝ)
    (hb : ∀ q : ℚ, 0 < (q : ℝ) →
      (2 * (q : ℝ) ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x q, f y) ≤ C)
    {r : ℝ} (hr : 0 < r) :
    (2 * r ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x r, f y) ≤ C := by
  have hm := le_quadratic_of_positive_rational_bounds
    (fun s ↦ ∫ y in closedEuclideanDiamond x s, f y)
    (monotone_integral_closedEuclideanDiamond f hf hf₀ x) C (fun q hq ↦ by
      calc
        _ = (2 * (q : ℝ) ^ 2) *
          ((2 * (q : ℝ) ^ 2)⁻¹ * ∫ y in closedEuclideanDiamond x q, f y) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hb q hq) (by positivity)) hr
  calc
    _ ≤ (2 * r ^ 2)⁻¹ * (2 * r ^ 2 * C) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C := by field_simp

/-- Countably many genuine contact estimates bound all true diamond averages simultaneously. -/
theorem ae_all_diamondAverages_le_half_kernel_mass [KernelMajorizationFacts] (f ν : E → ℝ)
    (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (hν₂ : MemLp ν 2 volume)
    (hf₀ : ∀ᵐ y, 0 ≤ f y) (κ : ℝ) (hcap : ∀ᵐ y, ν y ≤ κ) (P : E → Prop)
    (hcontact : ∀ r : ℝ, 0 < r → ∀ᵐ x, P x → 0 ≤
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y)) :
    ∀ᵐ x, P x → ∀ r : ℝ, 0 < r →
      (2 * r ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x r, f y) ≤
        κ * ((∫ y, euclideanKernel y) / 2) := by
  have hall : ∀ᵐ x, ∀ q : ℚ, 0 < (q : ℝ) → P x →
      (2 * (q : ℝ) ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x q, f y) ≤
        κ * ((∫ y, euclideanKernel y) / 2) := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · exact (ae_diamondAverage_le_half_kernel_mass f ν hf₂ hν₂ hf₀ κ hcap P hq
        (hcontact q hq)).mono (fun x hx _ ↦ hx)
    · exact Eventually.of_forall (fun x hx ↦ False.elim (hq hx))
  filter_upwards [hall] with x hx
  intro hp r hr
  exact diamondAverage_le_of_positive_rational_bounds f hf₁ hf₀ x _
    (fun q hq ↦ hx q hq hp) hr

end PartialBalayage.Maximal.Square
