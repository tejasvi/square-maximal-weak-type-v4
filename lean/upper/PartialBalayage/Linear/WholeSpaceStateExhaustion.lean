/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.JointWeakCompactness
public import PartialBalayage.Linear.UniformFiniteStateBounds

/-!
# Actual finite obstacles with a joint whole-space weak limit

For an integrable genuine L² input and a positive cap, select the proved finite obstacle
on each bounded open domain. The actual Fourier coercivity theorem bounds their Sobolev
norms by one constant. Joint weak compactness therefore supplies an actual state and capped
finite-mass density along a nontrivial cofinal filter, without assuming a uniform state bound.
Passing the PDE and recovering complementarity are separate assertions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace NNReal ENNReal Topology

namespace PartialBalayage.Linear

variable {n m : ℕ}

set_option maxHeartbeats 800000 in
/-- The actual finite obstacle family has a joint weak limit, with no compactness
or state-bound assumption among the hypotheses. -/
theorem exists_finiteObstacle_joint_weak_limit
    (Ω : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hΩ : ∀ k, IsOpen (Ω k)) (hΩb : ∀ k, Bornology.IsBounded (Ω k))
    (f : Lp (EuclideanSpace ℝ (Fin m)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
    (hf : Integrable (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin m)) volume)
    (κ mass : ℝ≥0) (hκ : 0 < κ) (hmass : (∫ x, ‖f x‖) ≤ (mass : ℝ)) :
    ∃ (ν : ∀ k, VectorDirichletL2 (Ω k) m) (U : ∀ k, VectorDirichletState (Ω k) m)
      (νlimit : Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))))
      (Ulimit : VectorDirichletState (univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) m)
      (l : Filter ℕ),
      (∀ k, ν k ∈ normCap (volume.restrict (Ω k)) (κ : ℝ) ∧
        (∀ j : Fin m, ∀ W : H01 (Ω k), laplaceBilin (Ω k) (U k j) W =
          ⟪vectorDirichletCoordinate (Ω k) j (restrictL2CLM (Ω k) f) -
            vectorDirichletCoordinate (Ω k) j (ν k), W.val 0⟫) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ν k x = ((κ : ℝ) / ‖vectorDirichletObservation (Ω k) (U k) x‖) •
            vectorDirichletObservation (Ω k) (U k) x) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x ≠ 0 →
          ‖ν k x‖ = (κ : ℝ)) ∧
        (∀ᵐ x ∂(volume.restrict (Ω k)), vectorDirichletObservation (Ω k) (U k) x = 0 →
          ν k x = restrictL2CLM (Ω k) f x)) ∧
      (∀ k, zeroExtendL2 (hΩ k).measurableSet (ν k) ∈ normMassCap volume κ mass) ∧
      (∀ k, ‖zeroExtendL2 (hΩ k).measurableSet (ν k)‖ ^ (2 : ℕ) ≤
        (κ : ℝ) * ∫ x, ‖f x‖) ∧
      νlimit ∈ normMassCap volume κ mass ∧ l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _ (zeroExtendL2 (hΩ k).measurableSet (ν k))) l
        (𝓝 (toWeakSpace ℝ _ νlimit)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ _
        (zeroExtendVectorDirichletState (hΩ k).measurableSet (U k))) l
          (𝓝 (toWeakSpace ℝ _ Ulimit)) := by
  obtain ⟨ν, U, hdata, hcap, henergy, _⟩ :=
    exists_finiteObstacle_density_weak_cluster Ω hΩ hΩb f hf κ mass hmass
  have hn : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    simp
  have hκreal : 0 < (κ : ℝ) := by exact_mod_cast hκ
  obtain ⟨B, _, hB⟩ := exists_uniform_vectorDirichlet_state_bound (m := m)
    hn hκreal (norm_nonneg f)
  have hU : ∀ k, ‖U k‖ ≤ B := by
    intro k
    exact hB (Ω k) (hΩ k).measurableSet ((hΩb k).measure_lt_top (μ := volume)).ne
      (U k) (restrictL2CLM (Ω k) f) (ν k) (norm_restrictL2CLM_le (Ω k) f)
        (hdata k).2.1 (hdata k).2.2.1
  obtain ⟨νlimit, Ulimit, l, hνlimit, _, hlne, hl, hνt, hUt⟩ :=
    exists_joint_weak_filter_zeroExtended_finite Ω (fun k ↦ (hΩ k).measurableSet)
      ν U κ mass B hcap hU
  exact ⟨ν, U, νlimit, Ulimit, l, hdata, hcap, henergy, hνlimit, hlne, hl, hνt, hUt⟩

end PartialBalayage.Linear
