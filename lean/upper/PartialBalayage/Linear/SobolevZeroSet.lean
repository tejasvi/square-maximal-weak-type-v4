/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletPositivePart

/-!
# Genuine locality of Dirichlet Sobolev gradients on level sets

The copied positive-part construction uses a smooth regularization whose derivative
at zero is zero. Thus the positive and negative parts both have zero gradient on
the zero set. Uniqueness of weak-gradient graphs identifies their difference with
the original Sobolev element, proving that its gradient vanishes on its zero set.
Applying this to a difference also proves equality of gradients on equality sets.

These statements use actual elements of the zero-boundary Sobolev graph space on
an open domain. No locality assumption, boundedness, or finite-measure hypothesis
is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Every weak-gradient coordinate vanishes almost everywhere on the value zero set. -/
theorem ae_gradient_eq_zero_on_value_zero (hΩ : IsOpen Ω) (U : H01 Ω) (i : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 →
      ((U : H1amb Ω) i.succ x : ℝ) = 0 := by
  obtain ⟨P, hP⟩ := exists_isPositivePartGraph U
  obtain ⟨N, hN⟩ := exists_isPositivePartGraph (-U)
  have hdecomp := H01_eq_positive_sub_negative hΩ U P N hP hN
  have hcoord : (U : H1amb Ω) i.succ =
      (P : H1amb Ω) i.succ - (N : H1amb Ω) i.succ := by
    simpa only [Submodule.coe_sub, PiLp.sub_apply] using
      congrArg (fun V : H01 Ω ↦ (V : H1amb Ω) i.succ) hdecomp
  have hcoordae : ((U : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[
      volume.restrict Ω] fun x ↦
      ((P : H1amb Ω) i.succ x : ℝ) - ((N : H1amb Ω) i.succ x : ℝ) := by
    rw [hcoord]
    exact Lp.coeFn_sub _ _
  filter_upwards [hP.2 i, hN.2 i, Lp.coeFn_neg ((U : H1amb Ω) 0), hcoordae]
    with x hp hn hneg hdiff
  intro hx
  simp only [Submodule.coe_neg, PiLp.neg_apply] at hn
  rw [hx] at hp
  simp only [lt_self_iff_false, ite_false] at hp
  rw [hneg, Pi.neg_apply, hx] at hn
  simp only [neg_zero, lt_self_iff_false, ite_false] at hn
  rw [hdiff, hp, hn, sub_self]

/-- Sobolev gradients agree almost everywhere on the set where the values agree. -/
theorem ae_gradient_eq_on_value_eq (hΩ : IsOpen Ω) (U V : H01 Ω) (i : Fin d) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = ((V : H1amb Ω) 0 x : ℝ) →
      ((U : H1amb Ω) i.succ x : ℝ) = ((V : H1amb Ω) i.succ x : ℝ) := by
  have hzero := ae_gradient_eq_zero_on_value_zero hΩ (U - V) i
  simp only [Submodule.coe_sub, PiLp.sub_apply] at hzero
  filter_upwards [hzero, Lp.coeFn_sub ((U : H1amb Ω) 0) ((V : H1amb Ω) 0),
    Lp.coeFn_sub ((U : H1amb Ω) i.succ) ((V : H1amb Ω) i.succ)]
    with x hx hvalue hgradient
  intro heq
  have hvaluezero : ((U : H1amb Ω) 0 - (V : H1amb Ω) 0) x = 0 := by
    rw [hvalue, Pi.sub_apply, heq, sub_self]
  have hgradientzero := hx hvaluezero
  rw [hgradient, Pi.sub_apply] at hgradientzero
  exact sub_eq_zero.mp hgradientzero

/-- The zero-set locality statement can be chosen simultaneously for every coordinate. -/
theorem ae_all_gradients_eq_zero_on_value_zero (hΩ : IsOpen Ω) (U : H01 Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ((U : H1amb Ω) 0 x : ℝ) = 0 →
      ∀ i : Fin d, ((U : H1amb Ω) i.succ x : ℝ) = 0 := by
  have h := ae_all_iff.mpr (fun i : Fin d ↦ ae_gradient_eq_zero_on_value_zero hΩ U i)
  filter_upwards [h] with x hx
  exact fun hzero i ↦ hx i hzero

end PartialBalayage.Linear
