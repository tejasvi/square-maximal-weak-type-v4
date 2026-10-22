/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: target 359123/100000 (our certificate); the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.StableKernelContactCaps
public import PartialBalayage.Maximal.Square.DiamondContactLevelBound
public import PartialBalayage.Maximal.Square.DiamondWeakTransfer

/-!
# The genuine square estimate reduced to actual source positivity

The constructed stable obstacle, full singular-source contact comparison,
true all-radius averages, level bounds and all-input transfer give the
table's strict target. Only the actual geometric density positivity remains
to be discharged by the finite rectangle checks and their true coverage.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

/-- All genuine analytic steps give the strict square target from actual source positivity. -/
theorem cubeWeakTypeConstant_lt_of_square_source_nonneg [KernelMajorizationFacts]
    (hpositive : ∀ᵐ x : EuclideanSpace ℝ (Fin 2), 0 ≤ squareGeneratorDensity x) :
    cubeWeakTypeConstant 2 < ENNReal.ofReal (359123 / 100000 : ℝ) := by
  apply cubeWeakTypeConstant_lt_of_euclideanDiamond_half_mass_bound
  apply euclideanDiamondMaximalFunction_weak_bound_of_nonneg_L1_L2
  intro f hf₁ hf₂ hf₀ α
  exact euclideanDiamondMaximalFunction_levelSet_bound_of_contact_caps f hf₁ hf₂ hf₀
    (fun κ hκ ↦ exists_stable_kernel_contact_caps_of_square_source_nonneg
      hpositive f hf₁ hf₂ hf₀ κ hκ) α

end PartialBalayage.Maximal.Square
