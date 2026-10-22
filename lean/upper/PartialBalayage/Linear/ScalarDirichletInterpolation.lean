/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierDirichletEnergy
public import PartialBalayage.Linear.SobolevCoordinateMass

/-!
# Actual scalar Dirichlet interpolation

The genuine zero extension preserves scalar value mass, value norm, and physical gradient
energy. Low/high frequency splitting therefore gives a finite interpolation bound on every
actual Dirichlet state with integrable value, without an assumed interpolation inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure X)

/-- The exact finite Fourier energy of the genuine complex zero-extended Dirichlet value. -/
theorem fourierEnergy_two_zeroExtendH01_eq_div (hΩ : MeasurableSet Ω) (U : H01 Ω) :
    fourierEnergy 2 (complexGlobalGraphCoordinateCLM 0
      (zeroExtendH01 hΩ U : H1amb (univ : Set X))) =
        ENNReal.ofReal (laplaceBilin Ω U U) / ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
  apply (ENNReal.eq_div_iff ?_ ENNReal.ofReal_ne_top).mpr
  · exact fourierEnergy_two_zeroExtendH01 hΩ U
  · exact ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (by positivity))

/-- Genuine scalar interpolation by value mass and physical gradient energy at every radius. -/
theorem scalarDirichlet_interpolation (hΩ : MeasurableSet Ω) (U : H01 Ω)
    (hU : Integrable ((U : H1amb Ω) 0 : X → ℝ) (volume.restrict Ω))
    {R : ℝ} (hR : 0 < R) :
    ‖(U : H1amb Ω) 0‖ ^ 2 ≤
      (∫ x, ‖(U : H1amb Ω) 0 x‖ ∂(volume.restrict Ω)) ^ 2 *
        (volume (closedBall (0 : X) R)).toReal +
          (R ^ (-2 : ℝ) / (2 * Real.pi) ^ 2) * laplaceBilin Ω U U := by
  let f : L² := complexGlobalGraphCoordinateCLM 0
    (zeroExtendH01 hΩ U : H1amb (univ : Set X))
  have hf : Integrable (f : X → ℂ) :=
    integrable_complexGlobalGraphCoordinate_zeroExtend hΩ U hU
  have hm : (∫ x, ‖f x‖) = ∫ x, ‖(U : H1amb Ω) 0 x‖ ∂(volume.restrict Ω) :=
    integral_norm_complexGlobalGraphCoordinate_zeroExtend hΩ U
  have hn : ‖f‖ = ‖(U : H1amb Ω) 0‖ := by
    rw [norm_complexGlobalGraphCoordinateCLM]
    change ‖zeroExtendUnivL2CLM hΩ ((U : H1amb Ω) 0)‖ = _
    exact norm_zeroExtendUnivL2CLM hΩ _
  have hE : fourierEnergy 2 f = ENNReal.ofReal (laplaceBilin Ω U U) /
      ENNReal.ofReal ((2 * Real.pi) ^ 2) := fourierEnergy_two_zeroExtendH01_eq_div hΩ U
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (by positivity))
  have hB : 0 ≤ laplaceBilin Ω U U := by
    rw [laplaceBilin_self]
    exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hlo : ENNReal.ofReal ((∫ x, ‖f x‖) ^ 2) * volume (closedBall (0 : X) R) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (isCompact_closedBall (0 : X) R).measure_ne_top
  have hhi : ENNReal.ofReal (R ^ (-2 : ℝ)) *
      (ENNReal.ofReal (laplaceBilin Ω U U) / ENNReal.ofReal ((2 * Real.pi) ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hc)
  have hs := enorm_sq_le_fourier_energy_split f hf (by norm_num : (0 : ℝ) ≤ 2) hR
  rw [hE] at hs
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hlo, hhi⟩) hs
  rw [ENNReal.toReal_add hlo hhi] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg f),
    ENNReal.toReal_ofReal (sq_nonneg (∫ x, ‖f x‖)),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le _), ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal (sq_nonneg (2 * Real.pi))] at hr
  simpa only [hn, hm, div_mul_eq_mul_div, mul_div_assoc] using hr

end PartialBalayage.Linear
