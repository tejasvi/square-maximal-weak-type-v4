/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.AENonnegOfSmoothTests
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual positive-part tests on a Sobolev zero set

The normalized tests converge at every nonnegative value of the state. Their
pairings converge by domination with the product of two actual `L²` functions.
No pointwise regularity of the state or finite mass of a jump measure is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace PartialBalayage.Maximal.Square

/-- The positive-part test divided by its positive parameter `1/(k+1)`. -/
def normalizedContactTest {X : Type*} (u φ : X → ℝ) (k : ℕ) (x : X) : ℝ :=
  max (φ x - ((k : ℝ) + 1) * u x) 0

theorem normalizedContactTest_nonneg {X : Type*} (u φ : X → ℝ) (k : ℕ) (x : X) :
    0 ≤ normalizedContactTest u φ k x := le_max_right _ _

theorem normalizedContactTest_le {X : Type*} {u φ : X → ℝ} {x : X}
    (hu : 0 ≤ u x) (hφ : 0 ≤ φ x) (k : ℕ) :
    normalizedContactTest u φ k x ≤ φ x := by
  unfold normalizedContactTest
  apply max_le _ hφ
  have : 0 ≤ ((k : ℝ) + 1) * u x := mul_nonneg (by positivity) hu
  linarith

/-- The genuine normalized tests converge to the test restricted to the state zero set. -/
theorem tendsto_normalizedContactTest {X : Type*} (u φ : X → ℝ) (x : X)
    (hu : 0 ≤ u x) (hφ : 0 ≤ φ x) :
    Tendsto (fun k ↦ normalizedContactTest u φ k x) atTop
      (𝓝 ({y | u y = 0}.indicator φ x)) := by
  by_cases hx : u x = 0
  · simp only [normalizedContactTest, hx, mul_zero, sub_zero, max_eq_left hφ,
      indicator_of_mem (show x ∈ {y | u y = 0} from hx)]
    exact tendsto_const_nhds
  · have hux : 0 < u x := lt_of_le_of_ne hu (Ne.symm hx)
    have ht : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) * u x) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).atTop_mul_const hux
    have he : ∀ᶠ k : ℕ in atTop, normalizedContactTest u φ k x = 0 := by
      filter_upwards [ht.eventually (eventually_ge_atTop (φ x))] with k hk
      exact max_eq_right (by linarith)
    rw [indicator_of_notMem (show x ∉ {y | u y = 0} from hx)]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

/-- Pairings of the actual positive-part tests converge against every `L²` function. -/
theorem tendsto_integral_normalizedContactTest {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u g : Lp ℝ 2 μ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (φ : X → ℝ) (hφ : MemLp φ 2 μ) (hφ0 : ∀ᵐ x ∂μ, 0 ≤ φ x) :
    Tendsto (fun k ↦ ∫ x, g x * normalizedContactTest u φ k x ∂μ) atTop
      (𝓝 (∫ x, g x * {y | u y = 0}.indicator φ x ∂μ)) := by
  have hi : Integrable (fun x ↦ g x * φ x) μ := (Lp.memLp g).integrable_mul hφ
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖g x * φ x‖)
  · intro k
    unfold normalizedContactTest
    exact (Lp.aestronglyMeasurable g).mul
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable
        (hφ.aestronglyMeasurable.sub ((Lp.aestronglyMeasurable u).const_mul _)))
  · exact hi.norm
  · intro k
    filter_upwards [hu, hφ0] with x hux hφx
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedContactTest_nonneg _ _ _ _),
      Real.norm_of_nonneg hφx]
    exact mul_le_mul_of_nonneg_left (normalizedContactTest_le hux hφx k) (norm_nonneg _)
  · filter_upwards [hu, hφ0] with x hux hφx
    exact (tendsto_normalizedContactTest u φ x hux hφx).const_mul (g x)

/-- An error tending to zero in the genuine truncation tests gives positivity on the zero set. -/
theorem integral_contact_nonneg_of_normalized_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u g : Lp ℝ 2 μ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (φ : X → ℝ) (hφ : MemLp φ 2 μ) (hφ0 : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (C : ℝ) (htest : ∀ k : ℕ,
      -(C / ((k : ℝ) + 1)) ≤ ∫ x, g x * normalizedContactTest u φ k x ∂μ) :
    0 ≤ ∫ x, g x * {y | u y = 0}.indicator φ x ∂μ := by
  have hzero : Tendsto (fun k : ℕ ↦ -(C / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, neg_zero, mul_zero, one_mul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).neg
  exact le_of_tendsto_of_tendsto hzero
    (tendsto_integral_normalizedContactTest μ u g hu φ hφ hφ0)
    (Eventually.of_forall htest)

/-- Genuine positive-part test estimates imply almost-everywhere generator positivity at contact.

The hypothesis concerns actual integrals of normalized tests. A symmetric jump-form
identity and its mixed-sign inequality supply this estimate without pointwise state regularity.
-/
theorem ae_nonneg_on_contact_of_normalized_tests {d : ℕ}
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : ∀ᵐ x ∂volume, 0 ≤ u x)
    (htest : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 φ →
      HasCompactSupport φ → (∀ x, 0 ≤ φ x) → ∃ C : ℝ, ∀ k : ℕ,
        -(C / ((k : ℝ) + 1)) ≤ ∫ x, g x * normalizedContactTest u φ k x) :
    ∀ᵐ x ∂volume, u x = 0 → 0 ≤ g x := by
  let Z := {x | u x = 0}
  have hZ : MeasurableSet Z :=
    measurableSet_eq_fun (Lp.stronglyMeasurable u).measurable measurable_const
  let gm := (Lp.memLp g).indicator hZ
  let gZ := gm.toLp (Z.indicator (g : _ → ℝ))
  have hp : ∀ᵐ x ∂volume, 0 ≤ gZ x := by
    apply PartialBalayage.Linear.ae_nonneg_of_integral_compactC2_nonneg
    intro φ hφ hs hφ0
    obtain ⟨C, hC⟩ := htest φ hφ hs hφ0
    have hpos := integral_contact_nonneg_of_normalized_tests volume u g hu φ
      (hφ.continuous.memLp_of_hasCompactSupport hs) (Eventually.of_forall hφ0) C hC
    have he : (∫ x, φ x * gZ x) = ∫ x, g x * Z.indicator φ x := by
      apply integral_congr_ae
      filter_upwards [gm.coeFn_toLp] with x hx
      rw [hx]
      by_cases hzx : x ∈ Z
      · simp only [indicator_of_mem hzx]
        ring
      · simp only [indicator_of_notMem hzx, mul_zero]
    rwa [he]
  filter_upwards [hp, gm.coeFn_toLp] with x hx hgx hux
  rw [hgx, indicator_of_mem (show x ∈ Z from hux)] at hx
  exact hx

end PartialBalayage.Maximal.Square
