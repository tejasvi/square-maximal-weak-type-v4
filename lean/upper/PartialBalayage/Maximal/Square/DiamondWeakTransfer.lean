/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: target 359123/100000 (our certificate) instead of 452/125. -/
module

public import PartialBalayage.Maximal.Square.EuclideanDiamondMaximal
public import PartialBalayage.Maximal.Square.EuclideanDiamondTransport
public import PartialBalayage.Maximal.Square.KernelMass

/-!
# Exact all-input transfer and the table's strict square target

Taking the actual input norm preserves the genuine maximal function.
Monotone norm truncations then extend nonnegative L¹ and L² estimates to
all integrable inputs. The actual diamond-to-square transformation and
strict original kernel mass give the table target from that coefficient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual nonnegative L¹ and L² estimate suffices for every true integrable input. -/
theorem euclideanDiamondMaximalFunction_weak_bound_of_nonneg_L1_L2 (C : ℝ≥0∞)
    (hb : ∀ f : E → ℝ, Integrable f → MemLp f 2 volume →
      (∀ᵐ y, 0 ≤ f y) → ∀ α : ℝ≥0∞,
        α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤ C * ∫⁻ y, ‖f y‖ₑ) :
    ∀ f : E → ℝ, Integrable f → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤ C * ∫⁻ y, ‖f y‖ₑ := by
  apply euclideanDiamondMaximalFunction_weak_bound_of_L1_L2 C
  intro f hf hf₂ α
  simpa only [euclideanDiamondMaximalFunction, enorm_norm] using
    hb (fun y ↦ ‖f y‖) hf.norm hf₂.norm
      (Eventually.of_forall fun y ↦ norm_nonneg (f y)) α

/-- A bound by the genuine half-kernel coefficient implies our strict square target. -/
theorem cubeWeakTypeConstant_lt_of_diamond_half_mass_bound
    (hC : IsDiamondWeakTypeBound (ENNReal.ofReal ((∫ y, euclideanKernel y) / 2))) :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (359123 / 100000 : ℝ) := by
  have hb := isCubeWeakTypeBound_of_diamond hC
  have hinf : cubeWeakTypeConstant 2 ≤ ENNReal.ofReal ((∫ y, euclideanKernel y) / 2) :=
    sInf_le hb
  exact hinf.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (by norm_num : (0 : ℝ) < 359123 / 100000)).mpr half_integral_euclideanKernel_lt)

/-- The actual all-input Euclidean estimate implies our strict square target. -/
theorem cubeWeakTypeConstant_lt_of_euclideanDiamond_half_mass_bound
    (hC : ∀ f : E → ℝ, Integrable f → ∀ α : ℝ≥0∞,
      α * volume {x | α < euclideanDiamondMaximalFunction f x} ≤
        ENNReal.ofReal ((∫ y, euclideanKernel y) / 2) * ∫⁻ y, ‖f y‖ₑ) :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (359123 / 100000 : ℝ) :=
  cubeWeakTypeConstant_lt_of_diamond_half_mass_bound
    (isDiamondWeakTypeBound_of_euclidean hC)

end PartialBalayage.Maximal.Square
