/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.JumpTranslationControl
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Actual two-coordinate translation control

The squared difference of a combined translation is bounded by twice the squares
of its two coordinate differences. Translation invariance of Lebesgue measure
then gives a genuine rectangular averaging bound from the two singular energies.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine integrated square of an actual physical translation difference. -/
def translationSquare (u : E → ℝ) (a : E) : ℝ≥0∞ :=
  ∫⁻ x, ‖u (x + a) - u x‖ₑ ^ (2 : ℕ)

private theorem enorm_sub_square_le (a b c : ℝ) :
    ‖a - c‖ₑ ^ (2 : ℕ) ≤ 2 * ‖a - b‖ₑ ^ (2 : ℕ) + 2 * ‖b - c‖ₑ ^ (2 : ℕ) := by
  have he (r : ℝ) : ‖r‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (r ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg r), Real.norm_eq_abs, sq_abs]
  have h : (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
    nlinarith [sq_nonneg (a - 2 * b + c)]
  rw [he, he, he]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [h2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

private theorem aemeasurable_translation_difference_square {u : E → ℝ}
    (hu : AEStronglyMeasurable u volume) (a : E) :
    AEMeasurable (fun x ↦ ‖u (x + a) - u x‖ₑ ^ (2 : ℕ)) volume :=
  ((hu.comp_measurePreserving (measurePreserving_add_right volume a)).sub hu).enorm.pow_const 2

/-- The actual two-step translation square is controlled by its true individual squares. -/
theorem translationSquare_add_le {u : E → ℝ} (hu : AEStronglyMeasurable u volume)
    (a b : E) :
    translationSquare u (a + b) ≤ 2 * translationSquare u a + 2 * translationSquare u b := by
  have hm := (aemeasurable_translation_difference_square hu a).comp_quasiMeasurePreserving
    (measurePreserving_add_right volume b).quasiMeasurePreserving
  have hshift : (∫⁻ x : E, ‖u ((x + b) + a) - u (x + b)‖ₑ ^ (2 : ℕ)) =
      translationSquare u a :=
    (measurePreserving_add_right volume b).lintegral_comp_emb
      (Homeomorph.addRight b).isClosedEmbedding.measurableEmbedding
      (fun x ↦ ‖u (x + a) - u x‖ₑ ^ (2 : ℕ))
  have hm2 : AEMeasurable (fun x : E ↦
      2 * ‖u ((x + b) + a) - u (x + b)‖ₑ ^ (2 : ℕ)) volume :=
    aemeasurable_const.mul hm
  calc
    _ ≤ ∫⁻ x : E, 2 * ‖u ((x + b) + a) - u (x + b)‖ₑ ^ (2 : ℕ) +
        2 * ‖u (x + b) - u x‖ₑ ^ (2 : ℕ) := by
      apply lintegral_mono
      intro x
      simpa only [add_assoc, add_comm a b] using
        enorm_sub_square_le (u ((x + b) + a)) (u (x + b)) (u x)
    _ = _ := by
      rw [lintegral_add_left' hm2,
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞), hshift]
      rfl

/-- The actual coordinate translation square is measurable for every averaging measure. -/
theorem aemeasurable_coordinate_translationSquare {u : E → ℝ}
    (hu : AEStronglyMeasurable u volume) (μ : Measure ℝ) [SigmaFinite μ] (i : Fin 2) :
    AEMeasurable (fun t ↦ translationSquare u (t • EuclideanSpace.basisFun (Fin 2) ℝ i)) μ := by
  have hj : QuasiMeasurePreserving (coordinateJumpPoint i) ((volume : Measure E).prod μ)
      volume := by
    apply QuasiMeasurePreserving.prod_of_left (by unfold coordinateJumpPoint; fun_prop)
    filter_upwards with t
    exact (measurePreserving_add_right volume
      (t • EuclideanSpace.basisFun (Fin 2) ℝ i)).quasiMeasurePreserving
  have hm := (hu.comp_quasiMeasurePreserving hj).sub
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fst
      (μ := (volume : Measure E)) (ν := μ)))
  exact (hm.enorm.pow_const 2).lintegral_prod_left'

/-- The actual two-coordinate rectangular translation-square average. -/
def rectangleTranslationSquare (u : E → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in jumpAveragingBand R, ∫⁻ t in jumpAveragingBand R,
    translationSquare u (t • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      s • EuclideanSpace.basisFun (Fin 2) ℝ 1)

/-- True rectangular averaging is controlled by the two actual coordinate averages. -/
theorem rectangleTranslationSquare_le {u : E → ℝ} (hu : AEStronglyMeasurable u volume)
    (R : ℝ) :
    rectangleTranslationSquare u R ≤ 2 * ENNReal.ofReal R *
      ((∫⁻ t in jumpAveragingBand R,
        translationSquare u (t • EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      (∫⁻ s in jumpAveragingBand R,
        translationSquare u (s • EuclideanSpace.basisFun (Fin 2) ℝ 1))) := by
  let μ := volume.restrict (jumpAveragingBand R)
  let T (i : Fin 2) (t : ℝ) :=
    translationSquare u (t • EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hvol : μ univ = ENNReal.ofReal R := by
    rw [Measure.restrict_apply_univ, jumpAveragingBand, Real.volume_Icc]
    congr 1
    ring
  have hm : AEMeasurable (fun t ↦ 2 * T 0 t) μ :=
    aemeasurable_const.mul (aemeasurable_coordinate_translationSquare hu μ 0)
  have hi (s : ℝ) : (∫⁻ t, 2 * T 0 t + 2 * T 1 s ∂μ) =
      2 * (∫⁻ t, T 0 t ∂μ) + 2 * T 1 s * ENNReal.ofReal R := by
    rw [lintegral_add_left' hm, lintegral_const_mul'
      _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞), lintegral_const, hvol]
  calc
    _ ≤ ∫⁻ s, ∫⁻ t, 2 * T 0 t + 2 * T 1 s ∂μ ∂μ :=
      lintegral_mono fun s ↦ lintegral_mono fun t ↦ translationSquare_add_le hu _ _
    _ = ∫⁻ s, 2 * (∫⁻ t, T 0 t ∂μ) + 2 * T 1 s * ENNReal.ofReal R ∂μ := by
      simp_rw [hi]
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const, hvol,
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      change _ = 2 * ENNReal.ofReal R * ((∫⁻ t, T 0 t ∂μ) + ∫⁻ s, T 1 s ∂μ)
      ring

/-- Actual rectangular translation squares are controlled by the full singular jump energy. -/
theorem jumpAveragingWeight_mul_rectangleTranslationSquare_le {α R : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R) (U : StableJumpEnergySpace α) :
    ENNReal.ofReal (jumpAveragingWeight α R) *
      rectangleTranslationSquare (stableJumpValue α U : E → ℝ) R ≤
        2 * ENNReal.ofReal R * (‖stableJumpData α U 0‖ₑ ^ (2 : ℕ) +
          ‖stableJumpData α U 1‖ₑ ^ (2 : ℕ)) := by
  let w := ENNReal.ofReal (jumpAveragingWeight α R)
  let I (i : Fin 2) := ∫⁻ t in jumpAveragingBand R,
    translationSquare (stableJumpValue α U : E → ℝ)
      (t • EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hi (i : Fin 2) : w * I i ≤ ‖stableJumpData α U i‖ₑ ^ (2 : ℕ) :=
    jumpAveragingWeight_mul_translation_lintegral_le_symm hα0 hα2 hR U i
  calc
    _ ≤ w * (2 * ENNReal.ofReal R * (I 0 + I 1)) :=
      mul_le_mul_right (rectangleTranslationSquare_le (Lp.aestronglyMeasurable _) R) w
    _ = 2 * ENNReal.ofReal R * (w * I 0 + w * I 1) := by ring
    _ ≤ _ := mul_le_mul_right (add_le_add (hi 0) (hi 1)) _

end PartialBalayage.Maximal.Square
