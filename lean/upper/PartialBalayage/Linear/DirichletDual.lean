/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapComplementarity
public import CenteredMaximal.Ball.MonotoneSurjectivity

/-!
# The finite-domain vector-valued dual obstacle

A bounded positive coercive Dirichlet operator `A` has a genuine bounded inverse.
For a bounded observation map `J`, the Green operator `J A⁻¹ J†` is positive.
The norm-cap variational inequality produces a vector-valued capped source `ν`
and a state `u` satisfying `A u = J† (f - ν)`. The capped source aligns with
`J u` and saturates its pointwise cap where `J u` is nonzero.

Coercivity is imposed on the Dirichlet operator `A`, not on its Green operator.
This abstract finite-measure construction does not assert whole-space mass,
Kato, or locality estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace PartialBalayage.Linear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Coercivity gives injectivity of the actual Dirichlet operator. -/
theorem injective_of_coercive (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) : Function.Injective A := by
  intro u v huv
  have h := hcoercive (u - v)
  rw [map_sub, huv, sub_self, inner_zero_left] at h
  have hsq : ‖u - v‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp
    (by simpa only [mul_comm, zero_mul, mul_zero] using h)
  have hnorm : ‖u - v‖ = 0 := by
    nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Coercivity gives surjectivity by the contracting gradient-step construction. -/
theorem surjective_of_coercive (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) : Function.Surjective A := by
  intro f
  apply CenteredMaximal.Ball.exists_eq_of_stronglyMonotone_lipschitz A f hc
  · intro u v
    simpa only [← map_sub] using A.le_opNorm (u - v)
  · intro u v
    simpa only [← map_sub] using hcoercive (u - v)

/-- The bounded equivalence defined by a coercive Dirichlet operator. -/
def coerciveOperatorEquiv (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (injective_of_coercive A hc hcoercive))
    (LinearMap.range_eq_top.mpr (surjective_of_coercive A hc hcoercive))

@[simp]
theorem coerciveOperatorEquiv_apply (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (u : H) :
    coerciveOperatorEquiv A hc hcoercive u = A u := rfl

/-- The actual bounded inverse of a coercive Dirichlet operator. -/
def coerciveOperatorInverse (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) : H →L[ℝ] H :=
  (coerciveOperatorEquiv A hc hcoercive).symm.toContinuousLinearMap

@[simp]
theorem apply_coerciveOperatorInverse (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (f : H) :
    A (coerciveOperatorInverse A hc hcoercive f) = f := by
  exact (coerciveOperatorEquiv A hc hcoercive).apply_symm_apply f

@[simp]
theorem coerciveOperatorInverse_apply (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (u : H) :
    coerciveOperatorInverse A hc hcoercive (A u) = u :=
  (coerciveOperatorEquiv A hc hcoercive).symm_apply_apply u

/-- The inverse of a symmetric positive coercive operator is positive. -/
theorem isPositive_coerciveOperatorInverse (A : H →L[ℝ] H) (hA : A.IsPositive)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) :
    (coerciveOperatorInverse A hc hcoercive).IsPositive := by
  let B := coerciveOperatorInverse A hc hcoercive
  have hAB : ∀ f, A (B f) = f := apply_coerciveOperatorInverse A hc hcoercive
  refine (ContinuousLinearMap.isPositive_iff B).mpr ⟨?_, ?_⟩
  · intro f g
    calc
      ⟪B f, g⟫ = ⟪B f, A (B g)⟫ := by rw [hAB]
      _ = ⟪A (B f), B g⟫ := (hA.inner_left_eq_inner_right (B f) (B g)).symm
      _ = ⟪f, B g⟫ := by rw [hAB]
  · intro f
    have h := hA.inner_nonneg_left (B f)
    rw [hAB] at h
    rwa [real_inner_comm] at h

section Green

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The Green operator obtained from a coercive state operator and an observation map. -/
def dirichletGreen (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (J : H →L[ℝ] F) : F →L[ℝ] F :=
  J ∘L coerciveOperatorInverse A hc hcoercive ∘L J.adjoint

/-- Green positivity follows from inverse positivity and adjoint conjugation. -/
theorem isPositive_dirichletGreen (A : H →L[ℝ] H) (hA : A.IsPositive) {c : ℝ}
    (hc : 0 < c) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (J : H →L[ℝ] F) :
    (dirichletGreen A hc hcoercive J).IsPositive :=
  (isPositive_coerciveOperatorInverse A hA hc hcoercive).conj_adjoint J

/-- The Green quadratic form is exactly the state Dirichlet energy. -/
theorem inner_dirichletGreen_eq (A : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫) (J : H →L[ℝ] F) (f : F) :
    ⟪dirichletGreen A hc hcoercive J f, f⟫ =
      ⟪A (coerciveOperatorInverse A hc hcoercive (J.adjoint f)),
        coerciveOperatorInverse A hc hcoercive (J.adjoint f)⟫ := by
  rw [apply_coerciveOperatorInverse]
  simp only [dirichletGreen, ContinuousLinearMap.comp_apply]
  rw [← J.adjoint_inner_right, real_inner_comm]

end Green

section Obstacle

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure X) [IsFiniteMeasure μ]

/-- The signed/vector-valued dual obstacle on a finite measure space, with its actual equation
and pointwise alignment and saturation on the active set. -/
theorem exists_dirichlet_dual_obstacle (A : H →L[ℝ] H) (hA : A.IsPositive)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ ⟪A u, u⟫)
    (J : H →L[ℝ] Lp E 2 μ) (f : Lp E 2 μ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (ν : Lp E 2 μ) (u : H), ν ∈ normCap μ κ ∧
      u = coerciveOperatorInverse A hc hcoercive (J.adjoint (f - ν)) ∧
      A u = J.adjoint (f - ν) ∧
      (∀ᵐ x ∂μ, (J u) x ≠ 0 → ν x = (κ / ‖(J u) x‖) • (J u) x) ∧
      (∀ᵐ x ∂μ, (J u) x ≠ 0 → ‖ν x‖ = κ) := by
  let G := dirichletGreen A hc hcoercive J
  have hG : G.IsPositive := isPositive_dirichletGreen A hA hc hcoercive J
  obtain ⟨ν, hν, hvi⟩ := exists_normCap_variational μ G (G f) hG hκ
  let u := coerciveOperatorInverse A hc hcoercive (J.adjoint (f - ν))
  have hJu : J u = G f - G ν := by
    simp only [u, G, dirichletGreen, ContinuousLinearMap.comp_apply, map_sub]
  have hvi' : ∀ η ∈ normCap μ κ, ⟪J u, η - ν⟫ ≤ 0 := by
    rw [hJu]
    exact hvi
  exact ⟨ν, u, hν, rfl, apply_coerciveOperatorInverse A hc hcoercive _,
    ae_eq_capSupportVector_of_variational μ hκ ν (J u) hν hvi',
    ae_norm_eq_cap_of_variational μ hκ ν (J u) hν hvi'⟩

end Obstacle

end PartialBalayage.Linear
