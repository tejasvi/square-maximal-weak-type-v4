/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.NormCap
public import CenteredMaximal.Analysis.WeakCompact
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The capped variational inequality on a finite measure space

On a finite measure space, the genuine pointwise norm cap in `L²(X; E)` is bounded,
closed, and convex. Weak compactness therefore gives a minimizer of every continuous
positive semidefinite quadratic energy on this set. The minimizer solves the associated
variational inequality. Positivity includes symmetry; no strict positivity or coercivity
of the operator is required.

This is an existence ingredient for a vector-valued dual obstacle construction. It does
not supply the locality or mass estimates of the partial balayage principles.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Bornology
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

section Bound

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The pointwise cap gives the sharp elementary `L²` norm bound. -/
theorem norm_le_of_mem_normCap {κ : ℝ} (hκ : 0 ≤ κ) {u : Lp E 2 μ}
    (hu : u ∈ normCap μ κ) : ‖u‖ ≤ κ * Real.sqrt (μ univ).toReal := by
  have h := Lp.norm_le_of_ae_bound hκ hu
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hp] at h
  simpa [Real.sqrt_eq_rpow, measureUnivNNReal, ENNReal.toReal,
    one_div, mul_comm] using h

theorem isBounded_normCap {κ : ℝ} (hκ : 0 ≤ κ) :
    IsBounded (normCap (E := E) μ κ) :=
  isBounded_iff_forall_norm_le.mpr
    ⟨κ * Real.sqrt (μ univ).toReal, fun _ hu ↦ norm_le_of_mem_normCap μ hκ hu⟩

end Bound

section Quadratic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic energy whose first variation is `A u - g`. -/
def positiveQuadraticEnergy (A : H →L[ℝ] H) (g : H) (u : H) : ℝ :=
  (1 / 2) * ⟪A u, u⟫ - ⟪g, u⟫

theorem continuous_positiveQuadraticEnergy (A : H →L[ℝ] H) (g : H) :
    Continuous (positiveQuadraticEnergy A g) := by
  unfold positiveQuadraticEnergy
  fun_prop

theorem positiveQuadraticEnergy_convex_combination (A : H →L[ℝ] H) (g : H)
    (hA : A.IsPositive) (u v : H) (a b : ℝ) (hab : a + b = 1) :
    a * positiveQuadraticEnergy A g u + b * positiveQuadraticEnergy A g v -
      positiveQuadraticEnergy A g (a • u + b • v) =
      a * b / 2 * ⟪A (u - v), u - v⟫ := by
  have hcross : ⟪A v, u⟫ = ⟪A u, v⟫ :=
    (hA.inner_left_eq_inner_right v u).trans (real_inner_comm (A u) v)
  have hb : b = 1 - a := by linarith
  simp only [positiveQuadraticEnergy, map_add, map_smul, map_sub, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right, hcross, hb]
  ring

theorem convexOn_positiveQuadraticEnergy (A : H →L[ℝ] H) (g : H)
    (hA : A.IsPositive) : ConvexOn ℝ univ (positiveQuadraticEnergy A g) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hid := positiveQuadraticEnergy_convex_combination A g hA u v a b hab
  have hnonneg := mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2))
    (hA.inner_nonneg_left (u - v))
  simp only [smul_eq_mul]
  linarith

/-- Expansion of the energy along an arbitrary direction. -/
theorem positiveQuadraticEnergy_add_smul (A : H →L[ℝ] H) (g : H)
    (hA : A.IsPositive) (u d : H) (t : ℝ) :
    positiveQuadraticEnergy A g (u + t • d) - positiveQuadraticEnergy A g u =
      -t * ⟪g - A u, d⟫ + t ^ 2 / 2 * ⟪A d, d⟫ := by
  have hcross : ⟪A d, u⟫ = ⟪A u, d⟫ :=
    (hA.inner_left_eq_inner_right d u).trans (real_inner_comm (A u) d)
  simp only [positiveQuadraticEnergy, map_add, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_sub_left, hcross]
  ring

/-- A quadratic nonnegative on the unit interval cannot have a negative right derivative. -/
theorem nonpos_of_quadratic_nonneg {c q : ℝ} (hq : 0 ≤ q)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ -t * c + t ^ 2 / 2 * q) : c ≤ 0 := by
  by_contra hc
  have hc : 0 < c := lt_of_not_ge hc
  let t := c / (q + c)
  have hden : 0 < q + c := add_pos_of_nonneg_of_pos hq hc
  have ht : 0 < t := div_pos hc hden
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hmul : t * (q + c) = c := div_mul_cancel₀ c hden.ne'
  have htq : t * q ≤ c := by nlinarith [mul_nonneg ht.le hc.le]
  have h := h t ⟨ht.le, ht1⟩
  have hq' := mul_le_mul_of_nonneg_left htq ht.le
  nlinarith [mul_pos ht hc]

/-- Every minimizer of the positive quadratic energy on a convex set solves the VI. -/
theorem variational_of_isMinOn_positiveQuadraticEnergy (A : H →L[ℝ] H) (g : H)
    (hA : A.IsPositive) {K : Set H} (hK : Convex ℝ K) {u : H} (hu : u ∈ K)
    (hmin : IsMinOn (positiveQuadraticEnergy A g) K u) :
    ∀ v ∈ K, ⟪g - A u, v - u⟫ ≤ 0 := by
  intro v hv
  apply nonpos_of_quadratic_nonneg (hA.inner_nonneg_left (v - u))
  intro t ht
  have hmem : u + t • (v - u) ∈ K := by
    have hseg := hK hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert hseg using 1
    module
  have h := sub_nonneg.mpr (isMinOn_iff.mp hmin _ hmem)
  rwa [positiveQuadraticEnergy_add_smul A g hA] at h

variable [CompleteSpace H]

/-- A bounded closed convex admissible set admits a VI for every positive operator. -/
theorem exists_variational_of_positive (A : H →L[ℝ] H) (g : H) (hA : A.IsPositive)
    {K : Set H} (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (hbounded : IsBounded K) : ∃ u ∈ K, ∀ v ∈ K, ⟪g - A u, v - u⟫ ≤ 0 := by
  have hcompact := hconv.isCompact_toWeakSpace_image hclosed hbounded
  have hlsc := ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (convexOn_positiveQuadraticEnergy A g hA)
    (continuous_positiveQuadraticEnergy A g).lowerSemicontinuous
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_isCompact_toWeakSpace_image
    hne hcompact (hlsc.lowerSemicontinuousOn _)
  exact ⟨u, hu, variational_of_isMinOn_positiveQuadraticEnergy A g hA hconv hu hmin⟩

end Quadratic

section NormCap

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure X) [IsFiniteMeasure μ]

/-- The actual pointwise norm cap is weakly compact when the underlying measure is finite. -/
theorem isCompact_toWeakSpace_image_normCap {κ : ℝ} (hκ : 0 ≤ κ) :
    IsCompact (toWeakSpace ℝ (Lp E 2 μ) '' normCap μ κ) :=
  Convex.isCompact_toWeakSpace_image (H := Lp E 2 μ)
    (convex_normCap μ κ) (isClosed_normCap μ hκ) (isBounded_normCap μ hκ)

/-- The capped dual variational problem has a solution for every bounded positive operator. -/
theorem exists_normCap_variational (A : Lp E 2 μ →L[ℝ] Lp E 2 μ) (g : Lp E 2 μ)
    (hA : A.IsPositive) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ ν ∈ normCap μ κ, ∀ η ∈ normCap μ κ, ⟪g - A ν, η - ν⟫ ≤ 0 :=
  exists_variational_of_positive A g hA (normCap_nonempty μ hκ)
    (isClosed_normCap μ hκ) (convex_normCap μ κ) (isBounded_normCap μ hκ)

end NormCap

end PartialBalayage.Linear
