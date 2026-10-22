/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The pointwise norm cap in L²

The genuine admissible set consists of vector-valued `L²` functions whose pointwise norm is at
most a prescribed cap almost everywhere. For every nonnegative cap this set is nonempty, closed,
and convex over the real scalars. Closedness follows by applying the Lipschitz norm-excess map
`v ↦ max (‖v‖ - κ) 0` in `L²` and identifying the capped set with its zero preimage.

These are geometric ingredients for constructing the vector-valued obstacle decomposition.
No existence of a decomposition or operator weak type estimate is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

/-- The almost-everywhere pointwise norm constraint on `L²(X; E)`. -/
def normCap (μ : Measure X) (κ : ℝ) : Set (Lp E 2 μ) :=
  {u | ∀ᵐ x ∂μ, ‖u x‖ ≤ κ}

theorem zero_mem_normCap (μ : Measure X) {κ : ℝ} (hκ : 0 ≤ κ) :
    (0 : Lp E 2 μ) ∈ normCap μ κ := by
  filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
  simpa only [hx, Pi.zero_apply, norm_zero] using hκ

theorem normCap_nonempty (μ : Measure X) {κ : ℝ} (hκ : 0 ≤ κ) :
    (normCap (E := E) μ κ).Nonempty :=
  ⟨0, zero_mem_normCap μ hκ⟩

/-- The amount by which a vector exceeds the pointwise norm cap. -/
def normExcess (κ : ℝ) (v : E) : ℝ := max (‖v‖ - κ) 0

theorem lipschitzWith_normExcess (κ : ℝ) : LipschitzWith 1 (normExcess (E := E) κ) := by
  simpa only [normExcess, add_zero] using!
    (lipschitzWith_one_norm.sub (LipschitzWith.const κ)).max_const 0

theorem normExcess_zero {κ : ℝ} (hκ : 0 ≤ κ) : normExcess κ (0 : E) = 0 := by
  simp [normExcess, hκ]

theorem normExcess_eq_zero_iff (κ : ℝ) (v : E) : normExcess κ v = 0 ↔ ‖v‖ ≤ κ := by
  simp only [normExcess, max_eq_right_iff, sub_nonpos]

/-- The norm-excess map, acting on equivalence classes of `L²` functions. -/
def normExcessL2 (μ : Measure X) (κ : ℝ) (hκ : 0 ≤ κ) : Lp E 2 μ → Lp ℝ 2 μ :=
  (lipschitzWith_normExcess κ).compLp (normExcess_zero hκ)

theorem continuous_normExcessL2 (μ : Measure X) (κ : ℝ) (hκ : 0 ≤ κ) :
    Continuous (normExcessL2 (E := E) μ κ hκ) :=
  (lipschitzWith_normExcess κ).continuous_compLp (normExcess_zero hκ)

theorem normExcessL2_eq_zero_iff (μ : Measure X) (κ : ℝ) (hκ : 0 ≤ κ) (u : Lp E 2 μ) :
    normExcessL2 μ κ hκ u = 0 ↔ u ∈ normCap μ κ := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hae := (lipschitzWith_normExcess κ).coeFn_compLp (normExcess_zero hκ) u
  constructor
  · intro h
    filter_upwards [hae, h] with x hx hzero
    exact (normExcess_eq_zero_iff κ (u x)).mp (hx.symm.trans hzero)
  · intro h
    filter_upwards [hae, h] with x hx hcap
    exact hx.trans ((normExcess_eq_zero_iff κ (u x)).mpr hcap)

theorem isClosed_normCap (μ : Measure X) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsClosed (normCap (E := E) μ κ) := by
  have hset : normCap (E := E) μ κ = normExcessL2 μ κ hκ ⁻¹' {0} := by
    ext u
    exact (normExcessL2_eq_zero_iff μ κ hκ u).symm
  rw [hset]
  exact isClosed_singleton.preimage (continuous_normExcessL2 μ κ hκ)

variable [NormedSpace ℝ E]

theorem convex_normCap (μ : Measure X) (κ : ℝ) : Convex ℝ (normCap (E := E) μ κ) := by
  intro u hu v hv a b ha hb hab
  filter_upwards [hu, hv, Lp.coeFn_add (a • u) (b • v),
    Lp.coeFn_smul a u, Lp.coeFn_smul b v] with x hux hvx hadd hau hbv
  rw [hadd, Pi.add_apply, hau, hbv, Pi.smul_apply, Pi.smul_apply]
  calc
    ‖a • u x + b • v x‖ ≤ ‖a • u x‖ + ‖b • v x‖ := norm_add_le _ _
    _ = a * ‖u x‖ + b * ‖v x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * κ + b * κ := add_le_add (mul_le_mul_of_nonneg_left hux ha)
      (mul_le_mul_of_nonneg_left hvx hb)
    _ = κ := by rw [← add_mul, hab, one_mul]

end PartialBalayage.Linear
