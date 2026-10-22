/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorDirichletEnergy
public import CenteredMaximal.Ball.BallWeakDistribution

/-!
# Extension of genuine compact-test equations to actual Dirichlet tests

The physical gradient pairing and the source value pairing extend to bounded linear
functionals on the ambient graph. Their difference has a closed kernel containing every
compact smooth test graph. It therefore contains the actual defining H01 closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The genuine physical gradient pairing extended to the whole ambient graph. -/
def ambientDirichletPairing (U : H01 Ω) : H1amb Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, innerSL ℝ ((U : H1amb Ω) i.succ) ∘L
    PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) i.succ

/-- Evaluation of the actual ambient pairing recovers the true Dirichlet bilinear form. -/
theorem ambientDirichletPairing_H01 (U W : H01 Ω) :
    ambientDirichletPairing U (W : H1amb Ω) = laplaceBilin Ω U W := by
  simp only [ambientDirichletPairing, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, laplaceBilin_apply]
  rfl

/-- A genuine compact-test weak equation extends to every actual H01 test. -/
theorem laplaceBilin_eq_inner_of_test_equation (U : H01 Ω) (g : L2D Ω)
    (htest : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn Ω φ),
      laplaceBilin Ω U hφ.toH01 = inner ℝ g hφ.testCls) :
    ∀ W : H01 Ω, laplaceBilin Ω U W = inner ℝ g ((W : H1amb Ω) 0) := by
  let L : H1amb Ω →L[ℝ] ℝ := ambientDirichletPairing U -
    innerSL ℝ g ∘L PiLp.proj 2 (fun _ : Fin (d + 1) ↦ L2D Ω) 0
  have hs : Submodule.span ℝ (testGraphSet Ω) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro Y ⟨φ, hφ, rfl⟩
    change ambientDirichletPairing U (hφ.toH01 : H1amb Ω) - inner ℝ g hφ.testCls = 0
    rw [ambientDirichletPairing_H01]
    exact sub_eq_zero.mpr (htest φ hφ)
  intro W
  have hw : (W : H1amb Ω) ∈ closure
      ((Submodule.span ℝ (testGraphSet Ω)) : Set (H1amb Ω)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact W.property
  have hz := (closure_minimal hs L.isClosed_ker) hw
  change ambientDirichletPairing U (W : H1amb Ω) - inner ℝ g ((W : H1amb Ω) 0) = 0 at hz
  rw [ambientDirichletPairing_H01] at hz
  exact sub_eq_zero.mp hz

end PartialBalayage.Linear
