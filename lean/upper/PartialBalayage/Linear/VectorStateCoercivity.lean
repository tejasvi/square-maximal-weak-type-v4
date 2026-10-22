/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorDirichletEnergy
public import PartialBalayage.Linear.FourierCoercivity

/-!
# Vector Dirichlet coercivity from scalar Fourier interpolation

Finite Hilbert summation converts the genuine scalar frequency estimates into a bound for
the full vector value. The exact obstacle energy-mass balance then yields state bounds with
constants independent of the spatial domain. This module records the summation step; the
scalar analytical estimate is supplied separately from actual Fourier derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Genuine scalar value-energy bounds sum to the full vector value estimate. -/
theorem norm_observation_sq_le_of_coordinate_bounds (U : VectorDirichletState Ω m)
    {M V D : ℝ}
    (hcoord : ∀ j : Fin m, ‖(U j : H1amb Ω) 0‖ ^ 2 ≤
      V * M ^ 2 + D * laplaceBilin Ω (U j) (U j)) :
    ‖vectorDirichletObservation Ω U‖ ^ 2 ≤
      (m : ℝ) * V * M ^ 2 + D * vectorDirichletEnergy U := by
  rw [norm_vectorDirichletObservation_sq]
  calc
    _ ≤ ∑ j : Fin m, (V * M ^ 2 + D * laplaceBilin Ω (U j) (U j)) :=
      Finset.sum_le_sum (fun j _ ↦ hcoord j)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      unfold vectorDirichletEnergy
      ring

/-- A harmless finite-coordinate factor gives the vector norm form of interpolation. -/
theorem norm_observation_le_of_coordinate_bounds (U : VectorDirichletState Ω m)
    {M V D : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hcoord : ∀ j : Fin m, ‖(U j : H1amb Ω) 0‖ ^ 2 ≤
      V * M ^ 2 + D * laplaceBilin Ω (U j) (U j)) :
    ‖vectorDirichletObservation Ω U‖ ≤
      ((m : ℝ) + 1) * Real.sqrt V * M +
        Real.sqrt D * Real.sqrt (vectorDirichletEnergy U) := by
  have hs := norm_observation_sq_le_of_coordinate_bounds U hcoord
  have hE := vectorDirichletEnergy_nonneg U
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcount (mul_nonneg hV (sq_nonneg M))
  have ha : 0 ≤ ((m : ℝ) + 1) * Real.sqrt V * M := by positivity
  have hb : 0 ≤ Real.sqrt D * Real.sqrt (vectorDirichletEnergy U) := by positivity
  have ha2 : (((m : ℝ) + 1) * Real.sqrt V * M) ^ 2 =
      ((m : ℝ) + 1) ^ 2 * V * M ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hV]
  have hb2 : (Real.sqrt D * Real.sqrt (vectorDirichletEnergy U)) ^ 2 =
      D * vectorDirichletEnergy U := by
    rw [mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hE]
  nlinarith [mul_nonneg ha hb, norm_nonneg (vectorDirichletObservation Ω U)]

/-- The actual full Sobolev norm is controlled by value norm plus square-root energy. -/
theorem norm_vectorState_le_value_add_sqrt_energy (U : VectorDirichletState Ω m) :
    ‖U‖ ≤ ‖vectorDirichletObservation Ω U‖ + Real.sqrt (vectorDirichletEnergy U) := by
  have heq := norm_vectorDirichletState_sq U
  have hs := Real.sq_sqrt (vectorDirichletEnergy_nonneg U)
  have hp := mul_nonneg (norm_nonneg (vectorDirichletObservation Ω U))
    (Real.sqrt_nonneg (vectorDirichletEnergy U))
  nlinarith [norm_nonneg U, norm_nonneg (vectorDirichletObservation Ω U),
    Real.sqrt_nonneg (vectorDirichletEnergy U)]

end PartialBalayage.Linear
