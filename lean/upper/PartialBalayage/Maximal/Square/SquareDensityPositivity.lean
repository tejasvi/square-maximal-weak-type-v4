/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: interior bound 264/5 and grid spacing 1/32; the exterior is split into points where the kernel vanishes (outside the box or on zero cells) and the ordered non-zero cells, whose positivity is a second explicit premise. -/
module

public import PartialBalayage.Maximal.Square.GeneratorInteriorTransport
public import PartialBalayage.Maximal.Square.KernelGeneratorAlmostEverywhere
public import PartialBalayage.Maximal.Square.BandCoverage

/-!
# Geometric positivity transport to the genuine source density

Actual coordinate swapping preserves the named interior expression. Positivity on the
ordered interior domain, on the ordered non-zero cells outside the diamond, and the vanishing
of the kernel on the remaining exterior points give source positivity on the entire plane
outside the already proved null axes and diamond boundary. The geometry premises are explicit.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The literal interior expression inherits swapping from the genuine original generator. -/
theorem generatorInteriorDensity_swap {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : u + v < 264 / 5) : generatorInteriorDensity u v = generatorInteriorDensity v u := by
  have he₁ := kernelGeneratorAt_scaled_eq_generatorInteriorDensity hu hv hr
  have he₂ := kernelGeneratorAt_scaled_eq_generatorInteriorDensity hv hu
    (by simpa only [add_comm] using hr)
  rw [kernelGeneratorAt_swap] at he₁
  exact mul_left_cancel₀ (stableNormalization_pos (by norm_num) (by norm_num)).ne'
    (he₁.symm.trans he₂)

/-- An actual ordered-interior proof covers the full positive-coordinate interior. -/
theorem generatorInteriorDensity_pos_of_ordered_interior
    (hinterior : ∀ {u v : ℝ}, 0 < v → v ≤ u → u + v < 264 / 5 →
      0 < generatorInteriorDensity u v) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 264 / 5) :
    0 < generatorInteriorDensity u v := by
  by_cases hvu : v ≤ u
  · exact hinterior hv hvu hr
  · rw [generatorInteriorDensity_swap hu hv hr]
    exact hinterior hu (le_of_lt (lt_of_not_ge hvu)) (by simpa only [add_comm] using hr)

/-- The kernel at an ordered exterior point vanishes on zero cells and outside the box. -/
theorem kernel_scaled_eq_zero {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (hr : 264 / 5 < a + b)
    (hcell : 72 ≤ a ∨ ZeroCell ⌊a⌋ ⌊b⌋) : kernel (a / 32) (b / 32) = 0 := by
  rcases hcell with h | hz
  · apply kernel_eq_zero_of_box
    left
    rw [abs_of_pos (by linarith)]
    linarith
  · have ha0 : 0 ≤ a := by linarith
    have hfa := Int.floor_le a
    have hfb := Int.floor_le b
    have hla := Int.lt_floor_add_one a
    have hlb := Int.lt_floor_add_one b
    have h := kernel_eq_zero_of_zeroCell hz (t := a - ⌊a⌋) (s := b - ⌊b⌋) (by linarith) (by linarith)
      (by linarith) (by linarith) ?_ ?_
    · simpa using h
    · simp only [add_sub_cancel, diamondRadius, supportRadius]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · simp only [add_sub_cancel]
      intro hc
      linarith [hc.2]

/-- The source density is nonnegative almost everywhere, given ordered interior positivity and
ordered exterior positivity on the non-zero cells of the box. -/
theorem ae_squareGeneratorDensity_nonneg_of_ordered [KernelMajorizationFacts]
    (hinterior : ∀ {u v : ℝ}, 0 < v → v ≤ u → u + v < 264 / 5 →
      0 < generatorInteriorDensity u v)
    (hband : ∀ {u v : ℝ}, 0 < v → v ≤ u → u < 72 → 264 / 5 < u + v → ¬ ZeroCell ⌊u⌋ ⌊v⌋ →
      0 < bandDensity u v) :
    ∀ᵐ x : E, 0 ≤ squareGeneratorDensity x := by
  filter_upwards [ae_euclidean_coordinate_ne_zero 0, ae_euclidean_coordinate_ne_zero 1,
    ae_diamondRadius_ne supportRadius] with x hx₀ hx₁ hne
  by_cases hr : diamondRadius (x 0) (x 1) < supportRadius
  · rw [squareGeneratorDensity_eq_generatorInteriorDensity hx₀ hx₁ hr]
    have hrscaled : 32 * |x 0| + 32 * |x 1| < 264 / 5 := by
      norm_num only [supportRadius, diamondRadius] at hr
      linarith
    apply mul_nonneg (stableNormalization_pos (by norm_num) (by norm_num)).le
    exact (generatorInteriorDensity_pos_of_ordered_interior hinterior
      (mul_pos (by norm_num) (abs_pos.mpr hx₀))
      (mul_pos (by norm_num) (abs_pos.mpr hx₁)) hrscaled).le
  · have hgt : supportRadius < diamondRadius (x 0) (x 1) := lt_of_le_of_ne (le_of_not_gt hr) hne.symm
    have hu : 0 < |x 0| := abs_pos.mpr hx₀
    have hv : 0 < |x 1| := abs_pos.mpr hx₁
    have hsum : 264 / 5 < 32 * |x 0| + 32 * |x 1| := by
      norm_num only [supportRadius, diamondRadius] at hgt
      linarith
    rw [squareGeneratorDensity_eq_kernelGeneratorAt_abs hx₀ hx₁ hne]
    -- order the coordinates
    obtain ⟨a, b, hab, hba, hb, hkg, hkx⟩ : ∃ a b : ℝ, a + b = 32 * |x 0| + 32 * |x 1| ∧ b ≤ a ∧ 0 < b ∧
        kernelGeneratorAt (47 / 40) |x 0| |x 1| = kernelGeneratorAt (47 / 40) (a / 32) (b / 32) ∧
        kernel (x 0) (x 1) = kernel (a / 32) (b / 32) := by
      rcases le_total |x 1| |x 0| with h | h
      · refine ⟨32 * |x 0|, 32 * |x 1|, rfl, by linarith, by positivity, ?_, ?_⟩
        · congr 1 <;> ring
        · rw [← kernel_abs]; congr 1 <;> ring
      · refine ⟨32 * |x 1|, 32 * |x 0|, by ring, by linarith, by positivity, ?_, ?_⟩
        · rw [← kernelGeneratorAt_swap]; congr 1 <;> ring
        · rw [← kernel_abs, ← kernel_swap]; congr 1 <;> ring
    by_cases hz : 72 ≤ a ∨ ZeroCell ⌊a⌋ ⌊b⌋
    · rw [← squareGeneratorDensity_eq_kernelGeneratorAt_abs hx₀ hx₁ hne]
      apply squareGeneratorDensity_nonneg_of_kernel_zero hx₀ hx₁ hne
      change kernel (x 0) (x 1) = 0
      rw [hkx]
      exact kernel_scaled_eq_zero hb hba (by linarith) hz
    · push_neg at hz
      rw [hkg, kernelGeneratorAt_scaled_eq_band (by linarith) hb (by linarith)]
      exact mul_nonneg (stableNormalization_pos (by norm_num) (by norm_num)).le
        (hband hb hba hz.1 (by linarith) hz.2).le

end PartialBalayage.Maximal.Square
