/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapVariational

/-!
# Pointwise complementarity for the genuine norm-cap variational inequality

The support competitor in the direction of `w` belongs to the pointwise norm cap.
Testing the variational inequality against it shows that the nonnegative support
deficit has integral zero. Thus the cap is saturated and the capped vector aligns
with `w` almost everywhere on the active set `{w ≠ 0}`.

These consequences use the actual vector-valued `L²` admissible set. They do not
assert any differential equation, locality, or mass estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support vector of the norm ball in the direction `v`, with value zero at `v = 0`. -/
def capSupportVector (κ : ℝ) (v : E) : E := (κ / ‖v‖) • v

theorem norm_capSupportVector {κ : ℝ} (hκ : 0 ≤ κ) {v : E} (hv : v ≠ 0) :
    ‖capSupportVector κ v‖ = κ := by
  rw [capSupportVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hκ (norm_nonneg v))]
  exact div_mul_cancel₀ κ (norm_ne_zero_iff.mpr hv)

theorem norm_capSupportVector_le {κ : ℝ} (hκ : 0 ≤ κ) (v : E) :
    ‖capSupportVector κ v‖ ≤ κ := by
  by_cases hv : v = 0
  · simpa [capSupportVector, hv] using hκ
  · exact (norm_capSupportVector hκ hv).le

theorem inner_capSupportVector (κ : ℝ) (v : E) :
    ⟪v, capSupportVector κ v⟫ = κ * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, capSupportVector]
  · rw [capSupportVector, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
    field_simp [norm_ne_zero_iff.mpr hv]

/-- Equality in the support inequality forces vector alignment whenever the direction is nonzero. -/
theorem eq_capSupportVector_of_inner_eq {κ : ℝ} (hκ : 0 ≤ κ) {v u : E}
    (hv : v ≠ 0) (hu : ‖u‖ ≤ κ) (hinner : ⟪v, u⟫ = κ * ‖v‖) :
    u = capSupportVector κ v := by
  have hnorm := norm_capSupportVector hκ hv
  have hcross : ⟪u, capSupportVector κ v⟫ = κ ^ 2 := by
    rw [capSupportVector, real_inner_smul_right, real_inner_comm v u, hinner]
    field_simp [norm_ne_zero_iff.mpr hv]
  have hsq : ‖u‖ ^ 2 ≤ κ ^ 2 := (sq_le_sq₀ (norm_nonneg u) hκ).mpr hu
  have hsub := norm_sub_sq_real u (capSupportVector κ v)
  rw [hnorm, hcross] at hsub
  have hzero : ‖u - capSupportVector κ v‖ = 0 := by
    nlinarith [norm_nonneg (u - capSupportVector κ v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

section L2

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem capSupportVector_memLp {κ : ℝ} (hκ : 0 ≤ κ) (w : Lp E 2 μ) :
    MemLp (fun x ↦ capSupportVector κ (w x)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x ↦ capSupportVector κ (w x)) μ :=
    (aestronglyMeasurable_const.div₀ (Lp.aestronglyMeasurable w).norm).smul
      (Lp.aestronglyMeasurable w)
  exact MemLp.of_bound hmeas κ
    (Eventually.of_forall fun x ↦ norm_capSupportVector_le hκ (w x))

/-- The support competitor as an actual element of `L²`. -/
def capSupportL2 (κ : ℝ) (hκ : 0 ≤ κ) (w : Lp E 2 μ) : Lp E 2 μ :=
  (capSupportVector_memLp μ hκ w).toLp (fun x ↦ capSupportVector κ (w x))

theorem coeFn_capSupportL2 (κ : ℝ) (hκ : 0 ≤ κ) (w : Lp E 2 μ) :
    capSupportL2 μ κ hκ w =ᵐ[μ] fun x ↦ capSupportVector κ (w x) :=
  (capSupportVector_memLp μ hκ w).coeFn_toLp

theorem capSupportL2_mem_normCap (κ : ℝ) (hκ : 0 ≤ κ) (w : Lp E 2 μ) :
    capSupportL2 μ κ hκ w ∈ normCap μ κ := by
  filter_upwards [coeFn_capSupportL2 μ κ hκ w] with x hx
  rw [hx]
  exact norm_capSupportVector_le hκ (w x)

/-- The variational inequality makes the support pairing maximal pointwise almost everywhere. -/
theorem ae_inner_eq_cap_mul_norm_of_variational {κ : ℝ} (hκ : 0 ≤ κ)
    (ν w : Lp E 2 μ) (hν : ν ∈ normCap μ κ)
    (hvi : ∀ η ∈ normCap μ κ, ⟪w, η - ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, ⟪w x, ν x⟫ = κ * ‖w x‖ := by
  let η := capSupportL2 μ κ hκ w
  have hη : η ∈ normCap μ κ := capSupportL2_mem_normCap μ κ hκ w
  have heq : (fun x ↦ ⟪w x, (η - ν) x⟫) =ᵐ[μ]
      (fun x ↦ κ * ‖w x‖ - ⟪w x, ν x⟫) := by
    filter_upwards [Lp.coeFn_sub η ν, coeFn_capSupportL2 μ κ hκ w] with x hsub hsupport
    rw [hsub, Pi.sub_apply, inner_sub_right, hsupport, inner_capSupportVector]
  have hint := (L2.integrable_inner (𝕜 := ℝ) w (η - ν)).congr heq
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ κ * ‖w x‖ - ⟪w x, ν x⟫) := by
    filter_upwards [hν] with x hx
    have h := (real_inner_le_norm (w x) (ν x)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg (w x)))
    simpa only [Pi.zero_apply, mul_comm, sub_nonneg] using h
  have hle : (∫ x, κ * ‖w x‖ - ⟪w x, ν x⟫ ∂μ) ≤ 0 := by
    rw [← integral_congr_ae heq, ← L2.inner_def]
    exact hvi η hη
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp
    (le_antisymm hle (integral_nonneg_of_ae hnonneg))
  filter_upwards [hzero] with x hx
  exact (sub_eq_zero.mp hx).symm

/-- On the active set, the capped vector points in the direction of the multiplier `w`. -/
theorem ae_eq_capSupportVector_of_variational {κ : ℝ} (hκ : 0 ≤ κ)
    (ν w : Lp E 2 μ) (hν : ν ∈ normCap μ κ)
    (hvi : ∀ η ∈ normCap μ κ, ⟪w, η - ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, w x ≠ 0 → ν x = (κ / ‖w x‖) • w x := by
  filter_upwards [hν, ae_inner_eq_cap_mul_norm_of_variational μ hκ ν w hν hvi]
    with x hcap hinner
  intro hw
  exact eq_capSupportVector_of_inner_eq hκ hw hcap hinner

/-- The norm cap is saturated almost everywhere where `w` is nonzero. -/
theorem ae_norm_eq_cap_of_variational {κ : ℝ} (hκ : 0 ≤ κ)
    (ν w : Lp E 2 μ) (hν : ν ∈ normCap μ κ)
    (hvi : ∀ η ∈ normCap μ κ, ⟪w, η - ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, w x ≠ 0 → ‖ν x‖ = κ := by
  filter_upwards [ae_eq_capSupportVector_of_variational μ hκ ν w hν hvi] with x hx
  intro hw
  rw [hx hw]
  exact norm_capSupportVector hκ hw

end L2

end PartialBalayage.Linear
