/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceL1Norm
public import PartialBalayage.Linear.NormCap
public import PartialBalayage.Linear.CapEnergy
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak compactness of whole-space capped densities

A pointwise norm cap and a finite full-vector mass bound give a uniform `L²` bound.
Both constraints are weakly closed, so their intersection is weakly compact in the genuine
Hilbert `L²` space. This compactness requires no finiteness of the ambient measure and supplies
the density compactness needed in an exhaustion by bounded domains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Bornology Metric
open scoped ENNReal NNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure X} [SigmaFinite μ]

/-- Actual whole-space `L²` densities with pointwise norm cap and full-vector mass bound. -/
def normMassCap (μ : Measure X) (κ mass : ℝ≥0) : Set (Lp E 2 μ) :=
  {f | f ∈ normCap μ (κ : ℝ) ∧ ∫⁻ x, ‖f x‖ₑ ∂μ ≤ (mass : ℝ≥0∞)}

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SigmaFinite μ] in
/-- Cap and mass alone give a uniform bound for the actual Hilbert norm. -/
theorem norm_le_of_mem_normMassCap {κ mass : ℝ≥0} {f : Lp E 2 μ}
    (hf : f ∈ normMassCap μ κ mass) : ‖f‖ ≤ (κ : ℝ) * (mass : ℝ) + 1 := by
  have he := eLpNorm_two_sq_le_of_cap (Lp.aestronglyMeasurable f) hf.1
  have hm : ENNReal.ofReal (κ : ℝ) * (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      (κ : ℝ≥0∞) * (mass : ℝ≥0∞) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact mul_le_mul_right hf.2 _
  have hs : ‖f‖ₑ ^ (2 : ℕ) ≤ (κ : ℝ≥0∞) * (mass : ℝ≥0∞) := by
    simpa only [← Lp.enorm_def] using he.trans hm
  have hn : ‖f‖₊ ^ (2 : ℕ) ≤ κ * mass := by
    apply ENNReal.coe_le_coe.mp
    simpa only [enorm, ENNReal.coe_pow, ENNReal.coe_mul] using hs
  have hr : ‖f‖ ^ (2 : ℕ) ≤ (κ : ℝ) * (mass : ℝ) := by exact_mod_cast hn
  nlinarith [sq_nonneg (‖f‖ - 1), κ.coe_nonneg, mass.coe_nonneg]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SigmaFinite μ] in
theorem isBounded_normMassCap (κ mass : ℝ≥0) :
    IsBounded (normMassCap (E := E) μ κ mass) :=
  isBounded_iff_forall_norm_le.mpr ⟨(κ : ℝ) * (mass : ℝ) + 1,
    fun _ hf => norm_le_of_mem_normMassCap hf⟩

omit [CompleteSpace E] in
/-- The cap and mass constraints are closed for the weak Hilbert topology. -/
theorem isClosed_toWeakSpace_image_normMassCap (κ mass : ℝ≥0) :
    IsClosed (toWeakSpace ℝ (Lp E 2 μ) '' normMassCap μ κ mass) := by
  have hc := (convex_normCap (E := E) μ (κ : ℝ)).isClosed_toWeakSpace_image
    (isClosed_normCap μ κ.coe_nonneg)
  have hm := isClosed_lintegral_norm_sublevel_weak (E := E) (μ := μ) (mass : ℝ≥0∞)
  have he : toWeakSpace ℝ (Lp E 2 μ) '' normMassCap μ κ mass =
      (toWeakSpace ℝ (Lp E 2 μ) '' normCap μ (κ : ℝ)) ∩
        {f | ∫⁻ x, ‖((toWeakSpace ℝ (Lp E 2 μ)).symm f) x‖ₑ ∂μ ≤ (mass : ℝ≥0∞)} := by
    ext f
    simp only [(toWeakSpace ℝ (Lp E 2 μ)).image_eq_preimage_symm,
      mem_preimage, normMassCap, mem_ofPred_eq, mem_inter_iff]
  rw [he]
  exact hc.inter hm

/-- Actual capped densities with a finite full-vector mass bound are weakly compact. -/
theorem isCompact_toWeakSpace_image_normMassCap (κ mass : ℝ≥0) :
    IsCompact (toWeakSpace ℝ (Lp E 2 μ) '' normMassCap μ κ mass) := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : Lp E 2 μ)).mp
    (isBounded_normMassCap (E := E) (μ := μ) κ mass)
  exact (isCompact_toWeakSpace_image_closedBall (0 : Lp E 2 μ) r).of_isClosed_subset
    (isClosed_toWeakSpace_image_normMassCap κ mass) (image_mono hr)

end PartialBalayage.Linear
