/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.SobolevZeroSet

/-!
# Locality of iterated Sobolev gradients

When each first-gradient coordinate itself has a zero-boundary Sobolev graph, applying
first-gradient locality twice proves that every second-gradient coordinate vanishes on the
original value zero set. This is an actual graph statement, rather than an assumed locality
property. Establishing these second graphs for a constructed PDE state is a separate regularity
task; the present hypotheses should not be mistaken for arbitrary `H¹` regularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open CenteredMaximal.Ball.DirichletSobolev

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Actual Sobolev graphs representing each first weak derivative of the state. -/
def IsSecondGradientGraph (U : H01 Ω) (G : Fin d → H01 Ω) : Prop :=
  ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω),
    ((G i : H1amb Ω) 0 x : ℝ) = ((U : H1amb Ω) i.succ x : ℝ)

/-- The second weak derivatives represented by actual graphs vanish on the state zero set. -/
theorem ae_second_gradient_eq_zero_on_value_zero (hΩ : IsOpen Ω)
    (U : H01 Ω) (G : Fin d → H01 Ω) (hG : IsSecondGradientGraph U G) (i j : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 →
      ((G i : H1amb Ω) j.succ x : ℝ) = 0 := by
  filter_upwards [ae_gradient_eq_zero_on_value_zero hΩ U i,
    ae_gradient_eq_zero_on_value_zero hΩ (G i) j, hG i] with x hU hGi hvalue
  intro hx
  exact hGi (by rw [hvalue, hU hx])

/-- Simultaneous locality for every represented second weak derivative. -/
theorem ae_all_second_gradients_eq_zero_on_value_zero (hΩ : IsOpen Ω)
    (U : H01 Ω) (G : Fin d → H01 Ω) (hG : IsSecondGradientGraph U G) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 →
      ∀ i j : Fin d, ((G i : H1amb Ω) j.succ x : ℝ) = 0 := by
  have h := ae_all_iff.mpr (fun i : Fin d ↦ ae_all_iff.mpr (fun j : Fin d ↦
    ae_second_gradient_eq_zero_on_value_zero hΩ U G hG i j))
  filter_upwards [h] with x hx
  exact fun hzero i j ↦ hx i j hzero

/-- The actual sum of the represented second-gradient diagonal coordinates. -/
def secondGraphLaplacian (G : Fin d → H01 Ω) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, ((G i : H1amb Ω) i.succ x : ℝ)

/-- The represented weak Laplacian vanishes on the original value zero set. -/
theorem ae_secondGraphLaplacian_eq_zero_on_value_zero (hΩ : IsOpen Ω)
    (U : H01 Ω) (G : Fin d → H01 Ω) (hG : IsSecondGradientGraph U G) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 →
      secondGraphLaplacian G x = 0 := by
  filter_upwards [ae_all_second_gradients_eq_zero_on_value_zero hΩ U G hG] with x hx
  intro hzero
  exact Finset.sum_eq_zero (fun i _ ↦ hx hzero i i)

/-- A density in the actual represented Laplace equation equals the input on the inactive set. -/
theorem ae_density_eq_input_on_value_zero (hΩ : IsOpen Ω)
    (U : H01 Ω) (G : Fin d → H01 Ω) (hG : IsSecondGradientGraph U G)
    {f ν : EuclideanSpace ℝ (Fin d) → ℝ}
    (heq : ∀ᵐ x ∂(volume.restrict Ω), ν x = f x + secondGraphLaplacian G x) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 → ν x = f x := by
  filter_upwards [ae_secondGraphLaplacian_eq_zero_on_value_zero hΩ U G hG, heq]
    with x hzero hx
  intro hu
  simpa only [hzero hu, add_zero] using hx

end PartialBalayage.Linear
