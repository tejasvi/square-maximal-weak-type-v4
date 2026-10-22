/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpRectangleEnergy
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The physical-space stable jump Nash estimate

Two-coordinate rectangular averaging separates the actual state square norm from
an actual correlation term. Translation invariance bounds this term by the square
of the true `L¹` mass, while the preceding module controls the translation squares
by the full singular jump energy. No Fourier energy identity is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual volume-preserving coordinate-pair identification. -/
def coordinatePairEquiv : (ℝ × ℝ) ≃ᵐ E :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem measurePreserving_coordinatePairEquiv :
    MeasurePreserving coordinatePairEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

theorem coordinatePairEquiv_apply (t s : ℝ) :
    coordinatePairEquiv (t, s) = t • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      s • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  ext i
  fin_cases i <;> simp [coordinatePairEquiv, MeasurableEquiv.finTwoArrow,
    MeasurableEquiv.piFinTwo, EuclideanSpace.basisFun_apply]

/-- The actual total absolute correlation over all two-coordinate translations. -/
theorem lintegral_absolute_translation_correlation (u : Lp ℝ 2 (volume : Measure E)) :
    (∫⁻ p : ℝ × ℝ, ∫⁻ x : E, ‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ) =
      (∫⁻ x : E, ‖u x‖ₑ) ^ (2 : ℕ) := by
  have hu : Measurable (u : E → ℝ) := (Lp.stronglyMeasurable u).measurable
  have hm : Measurable (fun q : (ℝ × ℝ) × E ↦
      ‖u q.2‖ₑ * ‖u (q.2 + coordinatePairEquiv q.1)‖ₑ) := by fun_prop
  have hi (x : E) : (∫⁻ p : ℝ × ℝ, ‖u (x + coordinatePairEquiv p)‖ₑ) =
      ∫⁻ y : E, ‖u y‖ₑ := by
    rw [measurePreserving_coordinatePairEquiv.lintegral_comp_emb
      coordinatePairEquiv.measurableEmbedding (fun y ↦ ‖u (x + y)‖ₑ)]
    exact (measurePreserving_add_left volume x).lintegral_comp_emb
      (Homeomorph.addLeft x).isClosedEmbedding.measurableEmbedding (fun y ↦ ‖u y‖ₑ)
  calc
    _ = ∫⁻ x : E, ∫⁻ p : ℝ × ℝ, ‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x : E, ‖u x‖ₑ * (∫⁻ y : E, ‖u y‖ₑ) := by
      congr 1
      funext x
      rw [lintegral_const_mul' _ _ enorm_ne_top, hi]
    _ = _ := by
      rw [lintegral_mul_const _ hu.enorm]
      exact (pow_two _).symm

private theorem enorm_square_le_difference_and_correlation (a b : ℝ) :
    ‖a‖ₑ ^ (2 : ℕ) ≤ ‖b - a‖ₑ ^ (2 : ℕ) + 2 * ‖a‖ₑ * ‖b‖ₑ := by
  have he (r : ℝ) : ‖r‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (r ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg r), Real.norm_eq_abs, sq_abs]
  have hab : a * b ≤ |a| * |b| := by simpa only [abs_mul] using le_abs_self (a * b)
  have h : a ^ 2 ≤ (b - a) ^ 2 + 2 * |a| * |b| := by nlinarith [sq_nonneg b]
  rw [he, he, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [h2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (sq_nonneg _) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- Actual absolute correlation on the averaging rectangle. -/
def rectangleAbsoluteCorrelation (u : E → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in jumpAveragingBand R, ∫⁻ t in jumpAveragingBand R, ∫⁻ x : E,
    ‖u x‖ₑ * ‖u (x + coordinatePairEquiv (t, s))‖ₑ

/-- Restricting actual translations bounds the rectangle correlation by the true mass square. -/
theorem rectangleAbsoluteCorrelation_le (u : Lp ℝ 2 (volume : Measure E)) (R : ℝ) :
    rectangleAbsoluteCorrelation (u : E → ℝ) R ≤ (∫⁻ x : E, ‖u x‖ₑ) ^ (2 : ℕ) := by
  have hu : Measurable (u : E → ℝ) := (Lp.stronglyMeasurable u).measurable
  have hm : Measurable (fun q : (ℝ × ℝ) × E ↦
      ‖u q.2‖ₑ * ‖u (q.2 + coordinatePairEquiv q.1)‖ₑ) := by fun_prop
  have hC : Measurable (fun p : ℝ × ℝ ↦
      ∫⁻ x : E, ‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ) :=
    hm.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ s : ℝ, ∫⁻ t : ℝ, ∫⁻ x : E,
        ‖u x‖ₑ * ‖u (x + coordinatePairEquiv (t, s))‖ₑ :=
      (lintegral_mono fun s ↦ setLIntegral_le_lintegral _ _).trans
        (setLIntegral_le_lintegral _ _)
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ x : E,
        ‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ :=
      (lintegral_prod_symm' _ hC).symm
    _ = _ := lintegral_absolute_translation_correlation u

/-- The true square norm is controlled by rectangle translations and true input mass. -/
theorem square_norm_le_rectangleTranslationSquare_add_mass
    (u : Lp ℝ 2 (volume : Measure E)) (R : ℝ) :
    ENNReal.ofReal R ^ (2 : ℕ) * ‖u‖ₑ ^ (2 : ℕ) ≤
      rectangleTranslationSquare (u : E → ℝ) R +
        2 * (∫⁻ x : E, ‖u x‖ₑ) ^ (2 : ℕ) := by
  let μ := volume.restrict (jumpAveragingBand R)
  let T (p : ℝ × ℝ) := translationSquare (u : E → ℝ) (coordinatePairEquiv p)
  let C (p : ℝ × ℝ) := ∫⁻ x : E, ‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ
  have hu : Measurable (u : E → ℝ) := (Lp.stronglyMeasurable u).measurable
  have hvol : μ univ = ENNReal.ofReal R := by
    rw [Measure.restrict_apply_univ, jumpAveragingBand, Real.volume_Icc]
    congr 1
    ring
  have hnorm : ‖u‖ₑ ^ (2 : ℕ) = ∫⁻ x : E, ‖u x‖ₑ ^ (2 : ℕ) := by
    rw [Lp.enorm_def]
    simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
      (Lp.aestronglyMeasurable u)
  have hTm : Measurable T := by
    have hTd : Measurable (fun q : (ℝ × ℝ) × E ↦
        ‖u (q.2 + coordinatePairEquiv q.1) - u q.2‖ₑ ^ (2 : ℕ)) := by fun_prop
    exact hTd.lintegral_prod_right'
  have hi (p : ℝ × ℝ) : ‖u‖ₑ ^ (2 : ℕ) ≤ T p + 2 * C p := by
    rw [hnorm]
    calc
      _ ≤ ∫⁻ x : E, ‖u (x + coordinatePairEquiv p) - u x‖ₑ ^ (2 : ℕ) +
          2 * (‖u x‖ₑ * ‖u (x + coordinatePairEquiv p)‖ₑ) := by
        apply lintegral_mono
        intro x
        simpa only [mul_assoc] using enorm_square_le_difference_and_correlation
          (u x) (u (x + coordinatePairEquiv p))
      _ = _ := by
        have hd : Measurable (fun x : E ↦
            ‖u (x + coordinatePairEquiv p) - u x‖ₑ ^ (2 : ℕ)) := by fun_prop
        rw [lintegral_add_left hd, lintegral_const_mul'
          _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
        rfl
  have hinner (s : ℝ) : (∫⁻ t, T (t, s) + 2 * C (t, s) ∂μ) =
      (∫⁻ t, T (t, s) ∂μ) + 2 * (∫⁻ t, C (t, s) ∂μ) := by
    have hms : Measurable (fun t : ℝ ↦ T (t, s)) :=
      hTm.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_add_left hms,
      lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  have hrect : ENNReal.ofReal R ^ (2 : ℕ) * ‖u‖ₑ ^ (2 : ℕ) ≤
      rectangleTranslationSquare (u : E → ℝ) R +
        2 * rectangleAbsoluteCorrelation (u : E → ℝ) R := by
    calc
      _ = ∫⁻ s, ∫⁻ t, ‖u‖ₑ ^ (2 : ℕ) ∂μ ∂μ := by
        simp only [lintegral_const, hvol]
        ring
      _ ≤ ∫⁻ s, ∫⁻ t, T (t, s) + 2 * C (t, s) ∂μ ∂μ :=
        lintegral_mono fun s ↦ lintegral_mono fun t ↦ hi (t, s)
      _ = _ := by
        simp_rw [hinner]
        rw [lintegral_add_left (hTm.lintegral_prod_left' (μ := μ)),
          lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
        simp only [T, coordinatePairEquiv_apply, rectangleTranslationSquare,
          rectangleAbsoluteCorrelation, C, μ]
  exact hrect.trans (add_le_add le_rfl
    (mul_le_mul_right (rectangleAbsoluteCorrelation_le u R) 2))

/-- The genuine physical-space averaging Nash inequality for the full stable jump graph. -/
theorem stableJump_nash_averaging {α R : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hR : 0 < R) (U : StableJumpEnergySpace α) :
    ENNReal.ofReal (jumpAveragingWeight α R) * ENNReal.ofReal R ^ (2 : ℕ) *
        ‖stableJumpValue α U‖ₑ ^ (2 : ℕ) ≤
      2 * ENNReal.ofReal R * (‖stableJumpData α U 0‖ₑ ^ (2 : ℕ) +
        ‖stableJumpData α U 1‖ₑ ^ (2 : ℕ)) +
      2 * ENNReal.ofReal (jumpAveragingWeight α R) *
        (∫⁻ x : E, ‖stableJumpValue α U x‖ₑ) ^ (2 : ℕ) := by
  let w := ENNReal.ofReal (jumpAveragingWeight α R)
  calc
    _ ≤ w * (rectangleTranslationSquare (stableJumpValue α U : E → ℝ) R +
        2 * (∫⁻ x : E, ‖stableJumpValue α U x‖ₑ) ^ (2 : ℕ)) := by
      rw [mul_assoc]
      exact mul_le_mul_right (square_norm_le_rectangleTranslationSquare_add_mass
        (stableJumpValue α U) R) w
    _ = w * rectangleTranslationSquare (stableJumpValue α U : E → ℝ) R +
        2 * w * (∫⁻ x : E, ‖stableJumpValue α U x‖ₑ) ^ (2 : ℕ) := by ring
    _ ≤ _ := add_le_add
      (jumpAveragingWeight_mul_rectangleTranslationSquare_le hα0 hα2 hR U) le_rfl

end PartialBalayage.Maximal.Square
