/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SobolevZeroExtension
public import PartialBalayage.Linear.VectorDirichletEnergy

/-!
# Genuine whole-space extension of vector Dirichlet states

The actual scalar isometric H01 extension is applied to the finite Hilbert product.
Both the full state norm and its physical Dirichlet energy are preserved. Thus the
domain-independent finite-state bounds also bound the actual whole-space states.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The actual componentwise isometric vector Dirichlet extension. -/
def zeroExtendVectorDirichletState (hΩ : MeasurableSet Ω) :
    VectorDirichletState Ω m →L[ℝ]
      VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin d))) m :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m ↦ H01 (univ : Set (EuclideanSpace ℝ (Fin d))))).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun j ↦ zeroExtendH01 hΩ ∘L
        PiLp.proj 2 (fun _ : Fin m ↦ H01 Ω) j)

theorem zeroExtendVectorDirichletState_apply (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) (j : Fin m) :
    zeroExtendVectorDirichletState hΩ U j = zeroExtendH01 hΩ (U j) := rfl

/-- Actual vector H01 extension is isometric in the full Sobolev norm. -/
theorem norm_zeroExtendVectorDirichletState (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) : ‖zeroExtendVectorDirichletState hΩ U‖ = ‖U‖ := by
  apply pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0) |>.mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [zeroExtendVectorDirichletState_apply, norm_zeroExtendH01]

/-- The genuine scalar first-gradient energy is preserved by zero extension. -/
theorem laplaceBilin_zeroExtendH01_self (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    laplaceBilin univ (zeroExtendH01 hΩ U) (zeroExtendH01 hΩ U) = laplaceBilin Ω U U := by
  rw [laplaceBilin_self, laplaceBilin_self]
  apply Finset.sum_congr rfl
  intro i _
  change ‖zeroExtendH1amb hΩ (U : H1amb Ω) i.succ‖ ^ 2 = _
  rw [zeroExtendH1amb_apply, norm_zeroExtendUnivL2CLM]

/-- The true vector gradient energy is independent of the extension domain. -/
theorem vectorDirichletEnergy_zeroExtend (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) :
    vectorDirichletEnergy (zeroExtendVectorDirichletState hΩ U) = vectorDirichletEnergy U := by
  unfold vectorDirichletEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [zeroExtendVectorDirichletState_apply, laplaceBilin_zeroExtendH01_self]

/-- The actual vector value norm is preserved along with its Dirichlet energy. -/
theorem norm_observation_zeroExtend (hΩ : MeasurableSet Ω)
    (U : VectorDirichletState Ω m) :
    ‖vectorDirichletObservation univ (zeroExtendVectorDirichletState hΩ U)‖ =
      ‖vectorDirichletObservation Ω U‖ := by
  apply pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0) |>.mp
  rw [norm_vectorDirichletObservation_sq, norm_vectorDirichletObservation_sq]
  apply Finset.sum_congr rfl
  intro j _
  change ‖zeroExtendH1amb hΩ (U j : H1amb Ω) 0‖ ^ 2 = _
  rw [zeroExtendH1amb_apply, norm_zeroExtendUnivL2CLM]

end PartialBalayage.Linear
