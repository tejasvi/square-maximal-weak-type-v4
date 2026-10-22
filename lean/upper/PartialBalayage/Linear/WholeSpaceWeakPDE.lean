/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.WholeSpaceStateExhaustion
public import PartialBalayage.Linear.ExhaustionWeakEquation

/-!
# Actual capped whole-space density and compact-test PDE

The expanding open balls contain every compact test support eventually. The actual uniformly
bounded finite obstacle family therefore yields a genuine whole-space H01 state and capped
finite-mass density satisfying the true Laplace equation on every compact smooth test. Cap
alignment of the limit is a separate result and is not claimed by this PDE construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {n m : ℕ}

set_option maxHeartbeats 800000 in
/-- Every genuine integrable vector L² input has an actual capped finite-mass density and
global Dirichlet state satisfying the compact-test weak equation. -/
theorem exists_wholeSpace_vector_weak_PDE
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin m)) volume)
    (κ : ℝ≥0) (hκ : 0 < κ) :
    ∃ (ν : Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
      (U : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) m),
      ν ∈ normMassCap volume κ ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩ ∧
      ∀ j : Fin m, ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ∀ hφ : IsTestFn univ φ,
        laplaceBilin univ (U j) hφ.toH01 =
          ⟪univVectorCoordinateCLM j f - univVectorCoordinateCLM j ν, hφ.testCls⟫ := by
  let Ω : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k ↦ ball 0 (k + 1 : ℝ)
  have hΩ : ∀ k, IsOpen (Ω k) := fun _ ↦ isOpen_ball
  have hΩb : ∀ k, Bornology.IsBounded (Ω k) := fun _ ↦ isBounded_ball
  let mass : ℝ≥0 := ⟨∫ x, ‖f x‖, integral_nonneg (fun _ ↦ norm_nonneg _)⟩
  obtain ⟨ν, U, νlimit, Ulimit, l, hdata, _, _, hνlimit, hlne, hl, hνt, hUt⟩ :=
    exists_finiteObstacle_joint_weak_limit Ω hΩ hΩb f hf κ mass hκ le_rfl
  let : l.NeBot := hlne
  refine ⟨νlimit, Ulimit, hνlimit, ?_⟩
  apply vector_weak_test_equation_of_joint_limit Ω (fun k ↦ (hΩ k).measurableSet)
    ν U f νlimit Ulimit (fun k ↦ (hdata k).2.1) ?_ hl hνt hUt
  intro K hK
  exact eventually_compact_subset_expanding_balls hK

end PartialBalayage.Linear
