/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.DirichletDual
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# The genuine positive scalar cap

The admissible density satisfies `0 ≤ ν ≤ κ` almost everywhere. Weak compactness of this
actual `L²` set constructs its dual variational solution. Pointwise interval support
competitors give saturation where the state is positive and a zero density where it is
negative. This differs from the signed norm-ball cap used for vector obstacles.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Bornology
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The actual positive scalar cap in `L²`. -/
def scalarIntervalCap (κ : ℝ) : Set (Lp ℝ 2 μ) := normCap μ κ ∩ Ici 0

theorem scalarIntervalCap_ae_bounds {κ : ℝ} {ν : Lp ℝ 2 μ}
    (hν : ν ∈ scalarIntervalCap μ κ) : ∀ᵐ x ∂μ, 0 ≤ ν x ∧ ν x ≤ κ := by
  filter_upwards [hν.1, (Lp.coeFn_nonneg ν).mpr hν.2] with x hb hx
  exact ⟨hx, (le_abs_self (ν x)).trans hb⟩

theorem scalarIntervalCap_nonempty {κ : ℝ} (hκ : 0 ≤ κ) :
    (scalarIntervalCap μ κ).Nonempty := by
  exact ⟨0, zero_mem_normCap μ hκ, by simp⟩

theorem isClosed_scalarIntervalCap {κ : ℝ} (hκ : 0 ≤ κ) :
    IsClosed (scalarIntervalCap μ κ) := (isClosed_normCap μ hκ).inter isClosed_Ici

theorem convex_scalarIntervalCap (κ : ℝ) : Convex ℝ (scalarIntervalCap μ κ) := by
  intro u hu v hv a b ha hb hab
  refine ⟨convex_normCap μ κ hu.1 hv.1 ha hb hab, ?_⟩
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(Lp.coeFn_nonneg u).mpr hu.2, (Lp.coeFn_nonneg v).mpr hv.2,
    Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u, Lp.coeFn_smul b v]
    with x hx hy hs hu hv
  simp only [hs, Pi.add_apply, hu, hv, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

variable [IsFiniteMeasure μ]

theorem isBounded_scalarIntervalCap {κ : ℝ} (hκ : 0 ≤ κ) :
    IsBounded (scalarIntervalCap μ κ) :=
  (isBounded_normCap (E := ℝ) μ hκ).subset inter_subset_left

/-- The actual scalar interval support point, with value zero in nonpositive directions. -/
def scalarIntervalSupport (κ r : ℝ) : ℝ := if 0 < r then κ else 0

theorem measurable_scalarIntervalSupport (κ : ℝ) : Measurable (scalarIntervalSupport κ) := by
  exact measurable_const.ite measurableSet_Ioi measurable_const

theorem scalarIntervalSupport_memLp {κ : ℝ} (hκ : 0 ≤ κ) (w : Lp ℝ 2 μ) :
    MemLp (fun x ↦ scalarIntervalSupport κ (w x)) 2 μ := by
  have hm : AEStronglyMeasurable (fun x ↦ scalarIntervalSupport κ (w x)) μ :=
    ((measurable_scalarIntervalSupport κ).comp_aemeasurable
      (Lp.aestronglyMeasurable w).aemeasurable).aestronglyMeasurable
  apply MemLp.of_bound hm κ
  filter_upwards with x
  unfold scalarIntervalSupport
  split_ifs <;> simp [Real.norm_of_nonneg hκ, hκ]

/-- The genuine `L²` support competitor for the pointwise positive interval cap. -/
def scalarIntervalSupportL2 (κ : ℝ) (hκ : 0 ≤ κ) (w : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (scalarIntervalSupport_memLp μ hκ w).toLp (fun x ↦ scalarIntervalSupport κ (w x))

theorem scalarIntervalSupportL2_ae (κ : ℝ) (hκ : 0 ≤ κ) (w : Lp ℝ 2 μ) :
    (scalarIntervalSupportL2 μ κ hκ w : X → ℝ) =ᵐ[μ]
      fun x ↦ scalarIntervalSupport κ (w x) :=
  (scalarIntervalSupport_memLp μ hκ w).coeFn_toLp

theorem scalarIntervalSupportL2_mem_cap {κ : ℝ} (hκ : 0 ≤ κ) (w : Lp ℝ 2 μ) :
    scalarIntervalSupportL2 μ κ hκ w ∈ scalarIntervalCap μ κ := by
  have he := scalarIntervalSupportL2_ae μ κ hκ w
  constructor
  · filter_upwards [he] with x hx
    rw [hx]
    unfold scalarIntervalSupport
    split_ifs <;> simp [Real.norm_of_nonneg hκ, hκ]
  · apply (Lp.coeFn_nonneg _).mp
    filter_upwards [he] with x hx
    rw [hx]
    unfold scalarIntervalSupport
    split_ifs <;> simp [hκ]

/-- The actual VI gives both signs of scalar pointwise complementarity. -/
theorem ae_scalarInterval_complementarity {κ : ℝ} (hκ : 0 ≤ κ) (ν w : Lp ℝ 2 μ)
    (hν : ν ∈ scalarIntervalCap μ κ)
    (hvi : ∀ η ∈ scalarIntervalCap μ κ, ⟪w, η - ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, (0 < w x → ν x = κ) ∧ (w x < 0 → ν x = 0) := by
  let η := scalarIntervalSupportL2 μ κ hκ w
  have hη := scalarIntervalSupportL2_mem_cap μ hκ w
  have he : (fun x ↦ ⟪w x, (η - ν) x⟫) =ᵐ[μ]
      (fun x ↦ w x * (scalarIntervalSupport κ (w x) - ν x)) := by
    filter_upwards [Lp.coeFn_sub η ν,
      scalarIntervalSupportL2_ae μ κ hκ w] with x hs he
    change η x = scalarIntervalSupport κ (w x) at he
    simp only [hs, Pi.sub_apply, he, Real.inner_apply]
  have hint := (L2.integrable_inner (𝕜 := ℝ) w (η - ν)).congr he
  have hn : 0 ≤ᵐ[μ] fun x ↦ w x * (scalarIntervalSupport κ (w x) - ν x) := by
    filter_upwards [scalarIntervalCap_ae_bounds μ hν] with x hx
    unfold scalarIntervalSupport
    split_ifs with hw
    · exact mul_nonneg hw.le (sub_nonneg.mpr hx.2)
    · exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hw) (by linarith [hx.1])
  have hle : (∫ x, w x * (scalarIntervalSupport κ (w x) - ν x) ∂μ) ≤ 0 := by
    rw [← integral_congr_ae he, ← L2.inner_def]
    exact hvi η hη
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hint).mp
    (le_antisymm hle (integral_nonneg_of_ae hn))
  filter_upwards [hz] with x hx
  constructor
  · intro hw
    rw [scalarIntervalSupport, ite_eq_left hw] at hx
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hw.ne')).symm
  · intro hw
    rw [scalarIntervalSupport, ite_eq_right (not_lt.mpr hw.le)] at hx
    have hs := (mul_eq_zero.mp hx).resolve_left hw.ne
    linarith

section Obstacle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual positive-cap dual problem supplies a state and pointwise capped density. -/
theorem exists_scalarInterval_dirichlet_dual_obstacle (A : H →L[ℝ] H) (hA : A.IsPositive)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫)
    (J : H →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : Lp ℝ 2 μ) (u : H), ν ∈ scalarIntervalCap μ κ ∧
      A u = J.adjoint (f - ν) ∧
      (∀ᵐ x ∂μ, (0 < J u x → ν x = κ) ∧ (J u x < 0 → ν x = 0)) := by
  let G := dirichletGreen A hc hcoercive J
  have hG : G.IsPositive := isPositive_dirichletGreen A hA hc hcoercive J
  obtain ⟨ν, hν, hvi⟩ := exists_variational_of_positive G (G f) hG
    (scalarIntervalCap_nonempty μ hκ) (isClosed_scalarIntervalCap μ hκ)
    (convex_scalarIntervalCap μ κ) (isBounded_scalarIntervalCap μ hκ)
  let u := coerciveOperatorInverse A hc hcoercive (J.adjoint (f - ν))
  have he : J u = G f - G ν := by
    simp only [u, G, dirichletGreen, ContinuousLinearMap.comp_apply, map_sub]
  refine ⟨ν, u, hν, apply_coerciveOperatorInverse A hc hcoercive _, ?_⟩
  apply ae_scalarInterval_complementarity μ hκ ν (J u) hν
  rw [he]
  exact hvi

end Obstacle

end PartialBalayage.Linear
