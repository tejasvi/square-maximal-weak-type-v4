/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpNashReal
public import PartialBalayage.Maximal.Square.JumpBallObstacle
public import PartialBalayage.Linear.ZeroExtensionMass
public import PartialBalayage.Linear.FourierCoercivity

/-!
# Domain-independent bounds for the genuine positive jump obstacle

The actual zero-exterior state is the genuine zero extension of its ball value,
so its mass is finite and unchanged by extension. Its true weak equation and cap
complementarity give the exact energy-mass balance. The physical jump Nash estimate
then gives uniform energy, mass, and full graph-norm bounds across the exhaustion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open PartialBalayage.Linear
open scoped RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Ω" R:arg => closedBall (0 : E) R
local notation "H" α:arg R:arg => StableJumpDirichletSpace α (Ω R)
local notation "L²" R:arg => Lp ℝ 2 (volume.restrict (Ω R))

/-- The actual zero-exterior state value equals genuine zero extension of its restriction. -/
theorem stableJumpBall_globalValue_eq_zeroExtend (α R : ℝ) (U : H α R) :
    stableJumpDirichletGlobalValue α (Ω R) U =
      zeroExtendL2 measurableSet_closedBall (stableJumpDirichletValue α (Ω R) U) := by
  apply Lp.ext
  have hr : ∀ᵐ x, x ∈ Ω R → stableJumpDirichletValue α (Ω R) U x =
      stableJumpDirichletGlobalValue α (Ω R) U x :=
    (ae_restrict_iff' measurableSet_closedBall).mp (restrictL2CLM_ae (Ω R) _)
  have hz := (mem_stableJumpSupported_iff α measurableSet_closedBall U.val).mp U.property
  filter_upwards [hr, hz,
    zeroExtendL2_ae measurableSet_closedBall (stableJumpDirichletValue α (Ω R) U)]
    with x hR hzero he
  rw [he]
  by_cases hx : x ∈ Ω R
  · rw [indicator_of_mem hx, hR hx]
  · rw [indicator_of_notMem hx]
    exact hzero hx

/-- The actual finite-ball jump state has a genuine whole-space integrable value. -/
theorem integrable_stableJumpBall_globalValue (α R : ℝ) (U : H α R) :
    Integrable (stableJumpDirichletGlobalValue α (Ω R) U : E → ℝ) := by
  let : IsFiniteMeasure (volume.restrict (Ω R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  rw [stableJumpBall_globalValue_eq_zeroExtend]
  exact integrable_zeroExtendL2 measurableSet_closedBall _ ((Lp.memLp _).integrable one_le_two)

/-- The actual finite-ball value norm is preserved under its genuine zero extension. -/
theorem norm_stableJumpBall_globalValue (α R : ℝ) (U : H α R) :
    ‖stableJumpDirichletGlobalValue α (Ω R) U‖ =
      ‖stableJumpDirichletValue α (Ω R) U‖ := by
  rw [stableJumpBall_globalValue_eq_zeroExtend, norm_zeroExtendL2]

/-- The actual finite-ball value mass is preserved under its genuine zero extension. -/
theorem integral_norm_stableJumpBall_globalValue (α R : ℝ) (U : H α R) :
    (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) =
      ∫ x, ‖stableJumpDirichletValue α (Ω R) U x‖ ∂volume.restrict (Ω R) := by
  rw [stableJumpBall_globalValue_eq_zeroExtend, integral_norm_zeroExtendL2]

/-- Genuine weak testing and cap alignment give the exact jump energy-mass balance. -/
theorem stableJumpBall_energy_mass_balance (α R : ℝ) (U : H α R) (f ν : L² R)
    {κ : ℝ} (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫)
    (hu : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ stableJumpDirichletValue α (Ω R) U x)
    (hcomp : ∀ᵐ x ∂volume.restrict (Ω R),
      0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) :
    stableJumpForm α U.val U.val + κ *
      (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) =
        ⟪f, stableJumpDirichletValue α (Ω R) U⟫ := by
  have hpair : ⟪ν, stableJumpDirichletValue α (Ω R) U⟫ =
      κ * (∫ x, ‖stableJumpDirichletValue α (Ω R) U x‖ ∂volume.restrict (Ω R)) := by
    rw [L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hu, hcomp] with x hx hc
    rw [Real.inner_apply, Real.norm_eq_abs, abs_of_nonneg hx]
    rcases hx.eq_or_lt with hz | hp
    · rw [← hz, mul_zero, mul_zero]
    · rw [hc hp]
  rw [integral_norm_stableJumpBall_globalValue]
  have h := hpde U
  rw [inner_sub_left, hpair] at h
  linarith

/-- The genuine state equation supplies the functional sublevel bound used in coercivity. -/
theorem stableJumpBall_functional_sublevel (α R : ℝ) (U : H α R) (f ν : L² R)
    {κ : ℝ} (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫)
    (hu : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ stableJumpDirichletValue α (Ω R) U x)
    (hcomp : ∀ᵐ x ∂volume.restrict (Ω R),
      0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) :
    stableJumpForm α U.val U.val / 2 + κ *
      (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) ≤
        ‖f‖ * ‖stableJumpDirichletGlobalValue α (Ω R) U‖ := by
  have hE : 0 ≤ stableJumpForm α U.val U.val := by rw [stableJumpForm_self]; positivity
  have he := stableJumpBall_energy_mass_balance α R U f ν hpde hu hcomp
  have h := real_inner_le_norm f (stableJumpDirichletValue α (Ω R) U)
  rw [← norm_stableJumpBall_globalValue] at h
  linarith

/-- The actual full singular jump graph norm is controlled by its actual value and energy. -/
theorem norm_stableJumpEnergySpace_le (α : ℝ) (U : StableJumpEnergySpace α) :
    ‖U‖ ≤ ‖stableJumpValue α U‖ + Real.sqrt (stableJumpForm α U U) := by
  have h := stableJumpEnergy_norm_sq α U
  have hE : 0 ≤ stableJumpForm α U U := by rw [stableJumpForm_self]; positivity
  have hs := Real.sq_sqrt hE
  rw [← stableJumpForm_self] at h
  nlinarith [norm_nonneg U, norm_nonneg (stableJumpValue α U),
    Real.sqrt_nonneg (stableJumpForm α U U),
    mul_nonneg (norm_nonneg (stableJumpValue α U)) (Real.sqrt_nonneg (stableJumpForm α U U))]

/-- True jump interpolation gives quantitative bounds independent of the obstacle ball. -/
theorem stableJumpBall_uniform_energy_mass_bounds {α R r κ F : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hr : 0 < r) (hκ : 0 < κ) (hF : 0 ≤ F)
    (U : H α R) (f ν : L² R) (hf : ‖f‖ ≤ F)
    (hsmall : F * Real.sqrt (2 / r ^ 2) ≤ κ / 2)
    (hpde : ∀ W : H α R, stableJumpForm α U.val W.val =
      ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫)
    (hu : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ stableJumpDirichletValue α (Ω R) U x)
    (hcomp : ∀ᵐ x ∂volume.restrict (Ω R),
      0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) :
    stableJumpForm α U.val U.val ≤
      4 * F ^ 2 * (2 / (jumpAveragingWeight α r * r)) ∧
    (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) ≤
      2 * F ^ 2 * (2 / (jumpAveragingWeight α r * r)) / κ := by
  have hw := jumpAveragingWeight_pos hα0 hα2 hr
  apply obstacle_sublevel_bounds_of_interpolation
    (integral_nonneg (fun _ ↦ norm_nonneg _))
    (by positivity : 0 ≤ 2 / (jumpAveragingWeight α r * r))
    (by rw [stableJumpForm_self]; positivity) hκ hF hsmall
    (stableJump_norm_le_mass_energy hα0 hα2 hr U.val
      (integrable_stableJumpBall_globalValue α R U))
  exact (stableJumpBall_functional_sublevel α R U f ν hpde hu hcomp).trans
    (mul_le_mul_of_nonneg_right hf (norm_nonneg _))

/-- There is a single finite bound for the actual state norm and mass on every obstacle ball. -/
theorem exists_uniform_stableJumpBall_state_bound {α κ F : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hκ : 0 < κ) (hF : 0 ≤ F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, ∀ (U : H α R) (f ν : L² R), ‖f‖ ≤ F →
      (∀ W : H α R, stableJumpForm α U.val W.val =
        ⟪f - ν, stableJumpDirichletValue α (Ω R) W⟫) →
      (∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ stableJumpDirichletValue α (Ω R) U x) →
      (∀ᵐ x ∂volume.restrict (Ω R),
        0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) →
      ‖U‖ ≤ B ∧ (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) ≤ B := by
  let r := 8 * (F + 1) / κ
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : κ * r = 8 * (F + 1) := by dsimp [r]; field_simp
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hA : Real.sqrt (2 / r ^ 2) = Real.sqrt 2 / r := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hsmall : F * Real.sqrt (2 / r ^ 2) ≤ κ / 2 := by
    rw [hA, ← mul_div_assoc]
    apply (div_le_iff₀ hr).mpr
    have hm := mul_le_mul_of_nonneg_left hs2 hF
    nlinarith
  let A := Real.sqrt (2 / r ^ 2)
  let D := 2 / (jumpAveragingWeight α r * r)
  let Em := 4 * F ^ 2 * D
  let Mm := 2 * F ^ 2 * D / κ
  have hw := jumpAveragingWeight_pos hα0 hα2 hr
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hEm : 0 ≤ Em := by dsimp [Em]; positivity
  have hMm : 0 ≤ Mm := by dsimp [Mm]; positivity
  let S := A * Mm + (Real.sqrt D + 1) * Real.sqrt Em
  have hS : 0 ≤ S := by dsimp [S, A]; positivity
  refine ⟨S + Mm, add_nonneg hS hMm, ?_⟩
  intro R U f ν hf hpde hu hcomp
  obtain ⟨hE, hM⟩ := stableJumpBall_uniform_energy_mass_bounds hα0 hα2 hr hκ hF
    U f ν hf hsmall hpde hu hcomp
  change stableJumpForm α U.val U.val ≤ Em at hE
  change (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) ≤ Mm at hM
  have hsqrt := Real.sqrt_le_sqrt hE
  have hi := stableJump_norm_le_mass_energy hα0 hα2 hr U.val
    (integrable_stableJumpBall_globalValue α R U)
  change ‖stableJumpDirichletGlobalValue α (Ω R) U‖ ≤ A *
    (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) +
      Real.sqrt D * Real.sqrt (stableJumpForm α U.val U.val) at hi
  have hm := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg (2 / r ^ 2))
  have he := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg D)
  have hn := norm_stableJumpEnergySpace_le α U.val
  change ‖U‖ ≤ ‖stableJumpDirichletGlobalValue α (Ω R) U‖ +
    Real.sqrt (stableJumpForm α U.val U.val) at hn
  constructor
  · dsimp [S]
    change A * _ ≤ A * Mm at hm
    have hval := hi.trans (add_le_add hm he)
    calc
      ‖U‖ ≤ ‖stableJumpDirichletGlobalValue α (Ω R) U‖ +
          Real.sqrt (stableJumpForm α U.val U.val) := hn
      _ ≤ (A * Mm + Real.sqrt D * Real.sqrt Em) + Real.sqrt Em :=
        add_le_add hval hsqrt
      _ ≤ _ := by nlinarith
  · exact hM.trans (le_add_of_nonneg_left hS)

set_option maxHeartbeats 600000 in
/-- Actual positive inputs produce a uniformly bounded family of genuine stable ball obstacles. -/
theorem exists_uniform_positive_stableJumpBall_obstacles {α κ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hκ : 0 < κ)
    (f : Lp ℝ 2 (volume : Measure E)) (hf : ∀ᵐ x, 0 ≤ f x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 < R → ∃ (ν : L² R) (U : H α R),
      (∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ ν x ∧ ν x ≤ κ) ∧
      (∀ᵐ x, 0 ≤ stableJumpDirichletGlobalValue α (Ω R) U x) ∧
      (∀ W : H α R, stableJumpForm α U.val W.val =
        ⟪restrictL2CLM (Ω R) f - ν, stableJumpDirichletValue α (Ω R) W⟫) ∧
      (∀ᵐ x ∂volume.restrict (Ω R),
        0 < stableJumpDirichletValue α (Ω R) U x → ν x = κ) ∧
      ‖U‖ ≤ B ∧ (∫ x : E, ‖stableJumpDirichletGlobalValue α (Ω R) U x‖) ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_stableJumpBall_state_bound hα0 hα2 hκ (norm_nonneg f)
  refine ⟨B, hB, ?_⟩
  intro R hR
  have hfr : ∀ᵐ x ∂volume.restrict (Ω R), 0 ≤ restrictL2CLM (Ω R) f x := by
    filter_upwards [ae_restrict_of_ae hf, restrictL2CLM_ae (Ω R) f] with x hx he
    rw [he]
    exact hx
  obtain ⟨ν, U, hν, hu, hpde, hcomp⟩ := exists_positive_stableJumpBall_obstacle
    hα0 hα2 hR (restrictL2CLM (Ω R) f) hfr hκ.le
  have hus : ∀ᵐ x ∂volume.restrict (Ω R),
      0 ≤ stableJumpDirichletValue α (Ω R) U x := by
    filter_upwards [ae_restrict_of_ae hu,
      restrictL2CLM_ae (Ω R) (stableJumpDirichletGlobalValue α (Ω R) U)] with x hx he
    change stableJumpDirichletValue α (Ω R) U x = _ at he
    rw [he]
    exact hx
  exact ⟨ν, U, hν, hu, hpde, hcomp,
    hb R U (restrictL2CLM (Ω R) f) ν (norm_restrictL2CLM_le _ _) hpde hus hcomp⟩

end PartialBalayage.Maximal.Square
