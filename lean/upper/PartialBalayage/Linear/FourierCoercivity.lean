/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierEnergySplit
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Coercivity from the genuine isotropic Fourier energy

Low-frequency splitting gives an interpolation bound with an arbitrarily small coefficient
on the full vector `L¹` mass. Young's inequality then bounds both energy and mass on the
nonpositive obstacle-functional sublevel. The constants depend only on the input norm,
the cap, the dimension, and the energy order, and are independent of an exhaustion domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Metric Set
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*}
variable [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The real low/high estimate has its true finite-energy value. -/
theorem norm_sq_le_fourier_energy_split (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    (hE : fourierEnergy α f ≠ ⊤) :
    ‖f‖ ^ 2 ≤ (∫ x, ‖f x‖) ^ 2 * (volume (closedBall (0 : X) R)).toReal +
      R ^ (-α) * (fourierEnergy α f).toReal := by
  have hvol : volume (closedBall (0 : X) R) ≠ ⊤ :=
    (isCompact_closedBall (0 : X) R).measure_lt_top.ne
  have hM : 0 ≤ (∫ x, ‖f x‖) ^ 2 := sq_nonneg _
  have hD : 0 ≤ R ^ (-α) := Real.rpow_nonneg hR.le _
  have hfin : ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume (closedBall (0 : X) R) +
      ENNReal.ofReal (R ^ (-α)) * fourierEnergy α f ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE⟩
  have he := ENNReal.toReal_mono hfin (enorm_sq_le_fourier_energy_split f hf hα hR)
  simpa only [← ofReal_norm, ENNReal.toReal_pow, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hM, ENNReal.toReal_ofReal hD] using he

/-- The norm form of the actual low/high estimate. -/
theorem norm_le_fourier_energy_split (f : Lp E 2 (volume : Measure X))
    (hf : Integrable (f : X → E)) {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    (hE : fourierEnergy α f ≠ ⊤) :
    ‖f‖ ≤ Real.sqrt ((volume (closedBall (0 : X) R)).toReal) * (∫ x, ‖f x‖) +
      Real.sqrt (R ^ (-α)) * Real.sqrt (fourierEnergy α f).toReal := by
  have hM : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hs := norm_sq_le_fourier_energy_split f hf hα hR hE
  have hv := Real.sq_sqrt (volume (closedBall (0 : X) R)).toReal_nonneg
  have hd := Real.sq_sqrt (Real.rpow_nonneg hR.le (-α))
  have he := Real.sq_sqrt (fourierEnergy α f).toReal_nonneg
  have hp := mul_nonneg (Real.sqrt_nonneg (volume (closedBall (0 : X) R)).toReal) hM
  have hq := mul_nonneg (Real.sqrt_nonneg (R ^ (-α)))
    (Real.sqrt_nonneg (fourierEnergy α f).toReal)
  nlinarith [mul_nonneg hp hq, norm_nonneg f]

/-- Young's inequality gives quantitative domain-independent energy and mass bounds. -/
theorem obstacle_sublevel_bounds_of_interpolation {N M A D energy κ F : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hE : 0 ≤ energy)
    (hκ : 0 < κ) (hF : 0 ≤ F) (hsmall : F * A ≤ κ / 2)
    (hinterp : N ≤ A * M + Real.sqrt D * Real.sqrt energy)
    (hsub : energy / 2 + κ * M ≤ F * N) :
    energy ≤ 4 * F ^ 2 * D ∧ M ≤ 2 * F ^ 2 * D / κ := by
  have hsqE := Real.sq_sqrt hE
  have hsqD := Real.sq_sqrt hD
  have hpair := mul_le_mul_of_nonneg_left hinterp hF
  have hmass := mul_le_mul_of_nonneg_right hsmall hM
  have hy := sq_nonneg (Real.sqrt energy / 2 - F * Real.sqrt D)
  have hbound : energy / 4 + κ * M / 2 ≤ F ^ 2 * D := by
    nlinarith
  constructor
  · nlinarith [mul_nonneg hκ.le hM]
  · apply (le_div_iff₀ hκ).mpr
    nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- A positive frequency radius makes the mass coefficient arbitrarily small in every
positive dimension. This radius depends on the data and cap, never on a spatial domain. -/
theorem exists_small_fourier_radius (hn : 0 < Module.finrank ℝ X)
    {κ F : ℝ} (hκ : 0 < κ) (hF : 0 ≤ F) :
    ∃ R : ℝ, 0 < R ∧
      F * Real.sqrt ((volume (closedBall (0 : X) R)).toReal) ≤ κ / 2 := by
  let C := (volume (closedBall (0 : X) 1)).toReal
  let q := κ / (2 * (F + 1))
  let R := min 1 (q ^ 2 / (C + 1))
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hq : 0 < q := div_pos hκ (by positivity)
  have hR : 0 < R := lt_min zero_lt_one (div_pos (sq_pos_of_pos hq) (by positivity))
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRq : R * (C + 1) ≤ q ^ 2 := by
    exact (le_div_iff₀ (by positivity : 0 < C + 1)).mp (min_le_right _ _)
  have hpow : R ^ Module.finrank ℝ X ≤ R := by
    have hp : R ^ (Module.finrank ℝ X - 1) ≤ 1 := pow_le_one₀ hR.le hR1
    have hnEq : Module.finrank ℝ X = (Module.finrank ℝ X - 1) + 1 := by omega
    rw [hnEq, pow_succ]
    nlinarith
  have hv : (volume (closedBall (0 : X) R)).toReal ≤ q ^ 2 := by
    rw [Measure.addHaar_closedBall' volume (0 : X) hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
    change R ^ Module.finrank ℝ X * C ≤ q ^ 2
    nlinarith [mul_le_mul_of_nonneg_right hpow hC]
  have hs : Real.sqrt ((volume (closedBall (0 : X) R)).toReal) ≤ q :=
    Real.sqrt_le_iff.mpr ⟨hq.le, hv⟩
  have hqEq : 2 * (F + 1) * q = κ := by
    dsimp [q]
    field_simp
  refine ⟨R, hR, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hs hF]

end PartialBalayage.Linear
