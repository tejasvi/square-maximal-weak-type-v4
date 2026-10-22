/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SobolevZeroExtension
public import CenteredMaximal.Ball.BallWeakDistribution
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# True interior weak equations after zero extension

Isometric zero extension preserves scalar pairings and the Dirichlet bilinear form. An
actual finite-domain weak equation therefore holds for global compact test functions whose
support is inside that domain. This is the equation needed for an exhaustion limit; no
global equation for a finite-domain extension is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The genuine scalar coordinate extension as a linear isometry. -/
def zeroExtendUnivL2LI (hΩ : MeasurableSet Ω) :
    L2D Ω →ₗᵢ[ℝ] L2D (univ : Set (EuclideanSpace ℝ (Fin d))) where
  toLinearMap := (zeroExtendUnivL2CLM hΩ).toLinearMap
  norm_map' := norm_zeroExtendUnivL2CLM hΩ

/-- Actual restricted scalar pairings are preserved by zero extension. -/
theorem inner_zeroExtendUnivL2CLM (hΩ : MeasurableSet Ω) (f g : L2D Ω) :
    ⟪zeroExtendUnivL2CLM hΩ f, zeroExtendUnivL2CLM hΩ g⟫ = ⟪f, g⟫ :=
  (zeroExtendUnivL2LI hΩ).inner_map_map f g

/-- The actual first-gradient bilinear form is preserved by genuine H01 extension. -/
theorem laplaceBilin_zeroExtendH01_pairing (hΩ : MeasurableSet Ω) (U W : H01 Ω) :
    laplaceBilin univ (zeroExtendH01 hΩ U) (zeroExtendH01 hΩ W) =
      laplaceBilin Ω U W := by
  rw [laplaceBilin_apply, laplaceBilin_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪zeroExtendH1amb hΩ (U : H1amb Ω) i.succ,
    zeroExtendH1amb hΩ (W : H1amb Ω) i.succ⟫ = _
  rw [zeroExtendH1amb_apply, zeroExtendH1amb_apply, inner_zeroExtendUnivL2CLM]

/-- A genuine compact interior test extends to its whole-space H01 test. -/
theorem zeroExtendH01_test (hΩ : MeasurableSet Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Ω φ) :
    zeroExtendH01 hΩ hφ.toH01 = (hφ.mono (subset_univ Ω)).toH01 := by
  apply Subtype.ext
  exact zeroExtendH1amb_testGraph hΩ hφ

/-- The genuine finite weak equation holds after extension on every interior global test. -/
theorem zeroExtendH01_interior_weak_equation (hΩ : MeasurableSet Ω)
    (U : H01 Ω) (r : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = ⟪r, (W : H1amb Ω) 0⟫)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Ω φ) :
    laplaceBilin univ (zeroExtendH01 hΩ U) (hφ.mono (subset_univ Ω)).toH01 =
      ⟪zeroExtendUnivL2CLM hΩ r, (hφ.mono (subset_univ Ω)).testCls⟫ := by
  rw [← zeroExtendH01_test hΩ hφ, laplaceBilin_zeroExtendH01_pairing, heq]
  have hv : (hφ.mono (subset_univ Ω)).testCls =
      zeroExtendUnivL2CLM hΩ hφ.testCls := by
    have ht := congrArg (fun W : H1amb (univ : Set (EuclideanSpace ℝ (Fin d))) ↦ W 0)
      (zeroExtendH1amb_testGraph hΩ hφ)
    simpa only [zeroExtendH1amb_apply, IsTestFn.testGraph_zero] using ht.symm
  rw [hv, inner_zeroExtendUnivL2CLM, IsTestFn.toH01_value]

end PartialBalayage.Linear
