/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.WeakCompact
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Weak lower semicontinuity of the vector norm integral

On finite measure spaces, actual `L²` functions embed continuously and linearly into `L¹`.
Their `L¹` norm is convex and continuous, hence weakly lower semicontinuous. The statements use
the full vector norm and require no scalar positivity cone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure X} [IsFiniteMeasure μ]

/-- The actual finite-measure `L²` to `L¹` inclusion. -/
def l2ToL1 (f : Lp E 2 μ) : Lp E 1 μ :=
  ((Lp.memLp f).integrable (by norm_num)).toL1 f

omit [NormedSpace ℝ E] in
theorem coeFn_l2ToL1 (f : Lp E 2 μ) : l2ToL1 f =ᵐ[μ] f :=
  Integrable.coeFn_toL1 _

omit [NormedSpace ℝ E] in
theorem norm_l2ToL1_le (f : Lp E 2 μ) :
    ‖l2ToL1 f‖ ≤ ((μ univ) ^ (1 / 2 : ℝ)).toReal * ‖f‖ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) (Lp.aestronglyMeasurable f)
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  have hfin : eLpNorm f 2 μ * (μ univ) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))
  have hr := ENNReal.toReal_mono hfin h
  rw [l2ToL1, Integrable.toL1, Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul, ← Lp.norm_def, mul_comm] using hr

/-- The finite-measure inclusion is a real linear map. -/
def l2ToL1Linear : Lp E 2 μ →ₗ[ℝ] Lp E 1 μ where
  toFun := l2ToL1
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_l2ToL1 (f + g), coeFn_l2ToL1 f, coeFn_l2ToL1 g,
      Lp.coeFn_add f g, Lp.coeFn_add (l2ToL1 f) (l2ToL1 g)] with x hsum hf hg hadd hadd'
    rw [hsum, hadd, hadd', Pi.add_apply, Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_l2ToL1 (c • f), coeFn_l2ToL1 f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (l2ToL1 f)] with x hcf hf hsmul hsmul'
    change (l2ToL1 (c • f)) x = (c • l2ToL1 f) x
    rw [hcf, hsmul, hsmul', Pi.smul_apply, Pi.smul_apply, hf]

/-- The finite-measure inclusion as a genuine bounded linear map. -/
def l2ToL1CLM : Lp E 2 μ →L[ℝ] Lp E 1 μ :=
  l2ToL1Linear.mkContinuous ((μ univ) ^ (1 / 2 : ℝ)).toReal norm_l2ToL1_le

/-- The full vector `L¹` norm on the actual finite-measure `L²` space. -/
def l1NormOnL2 (f : Lp E 2 μ) : ℝ := ‖l2ToL1CLM f‖

theorem ofReal_l1NormOnL2 (f : Lp E 2 μ) :
    ENNReal.ofReal (l1NormOnL2 f) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  change ENNReal.ofReal ‖l2ToL1 f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ
  rw [ofReal_norm]
  exact Integrable.enorm_toL1 _

theorem continuous_l1NormOnL2 : Continuous (l1NormOnL2 (E := E) (μ := μ)) :=
  l2ToL1CLM.continuous.norm

theorem convexOn_l1NormOnL2 : ConvexOn ℝ univ (l1NormOnL2 (E := E) (μ := μ)) := by
  have h := (convexOn_norm (E := Lp E 1 μ) convex_univ).comp_linearMap
    (l2ToL1CLM (E := E) (μ := μ)).toLinearMap
  convert! h using 1

/-- The full vector norm integral is weakly lower semicontinuous, without a positivity cone. -/
theorem lowerSemicontinuous_l1NormOnL2_weak :
    LowerSemicontinuous (l1NormOnL2 ∘ (toWeakSpace ℝ (Lp E 2 μ)).symm) :=
  convexOn_l1NormOnL2.lowerSemicontinuous_comp_toWeakSpace_symm
    continuous_l1NormOnL2.lowerSemicontinuous

end PartialBalayage.Linear
