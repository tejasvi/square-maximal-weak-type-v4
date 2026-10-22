/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.SplineTaylorSum

/-!
# Genuine cubic bounds on closed rational intervals

Exact affine substitution and the cubic Bernstein change of basis reconstruct
the actual polynomial. The basis is a nonnegative partition of unity, so the
maximum absolute rational coefficient bounds the whole closed interval.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The exact cubic coefficients after a rational affine substitution. -/
def cubicAffineCoefficients (c : Fin 4 → ℚ) (l w : ℚ) : Fin 4 → ℚ :=
  ![c 0 + c 1 * l + c 2 * l ^ (2 : ℕ) + c 3 * l ^ (3 : ℕ),
    w * (c 1 + 2 * c 2 * l + 3 * c 3 * l ^ (2 : ℕ)),
    w ^ (2 : ℕ) * (c 2 + 3 * c 3 * l), w ^ (3 : ℕ) * c 3]

/-- The exact cubic Bernstein coefficient vector of an ordinary cubic. -/
def cubicBernsteinCoefficients (c : Fin 4 → ℚ) : Fin 4 → ℚ :=
  ![c 0, c 0 + c 1 / 3, c 0 + 2 * c 1 / 3 + c 2 / 3,
    c 0 + c 1 + c 2 + c 3]

/-- The genuine four cubic Bernstein basis functions. -/
def cubicBernsteinBasis (x : ℝ) : Fin 4 → ℝ :=
  ![(1 - x) ^ (3 : ℕ), 3 * x * (1 - x) ^ (2 : ℕ),
    3 * x ^ (2 : ℕ) * (1 - x), x ^ (3 : ℕ)]

/-- Exact affine coefficients reconstruct the actual real cubic. -/
theorem centeredCubic_affine (c : Fin 4 → ℚ) (l w : ℚ) (x : ℝ) :
    centeredCubic (fun i ↦ (c i : ℝ)) ((l : ℝ) + (w : ℝ) * x) =
      centeredCubic (fun i ↦ (cubicAffineCoefficients c l w i : ℝ)) x := by
  norm_num [centeredCubic, cubicAffineCoefficients, Fin.sum_univ_succ]
  ring

/-- The actual cubic equals its exact rational Bernstein reconstruction. -/
theorem centeredCubic_eq_bernstein (c : Fin 4 → ℚ) (x : ℝ) :
    centeredCubic (fun i ↦ (c i : ℝ)) x =
      ∑ i : Fin 4, (cubicBernsteinCoefficients c i : ℝ) * cubicBernsteinBasis x i := by
  norm_num [centeredCubic, cubicBernsteinCoefficients, cubicBernsteinBasis,
    Fin.sum_univ_succ]
  ring

theorem cubicBernsteinBasis_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (i : Fin 4) :
    0 ≤ cubicBernsteinBasis x i := by
  have h : 0 ≤ 1 - x := by linarith
  fin_cases i <;> norm_num [cubicBernsteinBasis] <;> positivity

theorem cubicBernsteinBasis_sum (x : ℝ) : ∑ i : Fin 4, cubicBernsteinBasis x i = 1 := by
  norm_num [cubicBernsteinBasis, Fin.sum_univ_succ]
  ring

/-- Exact rational absolute Bernstein bounds imply a true bound on the closed unit interval. -/
theorem abs_centeredCubic_le_bernstein {c : Fin 4 → ℚ} {M : ℚ} {x : ℝ}
    (hM : ∀ i, |cubicBernsteinCoefficients c i| ≤ M) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    |centeredCubic (fun i ↦ (c i : ℝ)) x| ≤ (M : ℝ) := by
  rw [centeredCubic_eq_bernstein]
  calc
    _ ≤ ∑ i : Fin 4,
        |(cubicBernsteinCoefficients c i : ℝ) * cubicBernsteinBasis x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, (M : ℝ) * cubicBernsteinBasis x i := by
      apply Finset.sum_le_sum
      intro i hi
      have hB := cubicBernsteinBasis_nonneg hx₀ hx₁ i
      rw [abs_mul, abs_of_nonneg hB]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM i) hB
    _ = (M : ℝ) := by rw [← Finset.mul_sum, cubicBernsteinBasis_sum, mul_one]

/-- The actual polynomial is bounded everywhere on the stated closed rational interval. -/
theorem abs_centeredCubic_le_on_interval {c : Fin 4 → ℚ} {l w M : ℚ} {s : ℝ}
    (hw : 0 < w) (hM : ∀ i, |cubicBernsteinCoefficients (cubicAffineCoefficients c l w) i| ≤ M)
    (hs₀ : (l : ℝ) ≤ s) (hs₁ : s ≤ ((l + w : ℚ) : ℝ)) :
    |centeredCubic (fun i ↦ (c i : ℝ)) s| ≤ (M : ℝ) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hx₀ : 0 ≤ (s - (l : ℝ)) / (w : ℝ) := div_nonneg (sub_nonneg.mpr hs₀) hw'.le
  have hx₁ : (s - (l : ℝ)) / (w : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hw').mpr
    push_cast at hs₁
    linarith
  have hb := abs_centeredCubic_le_bernstein hM hx₀ hx₁
  rw [← centeredCubic_affine] at hb
  have he : (l : ℝ) + (w : ℝ) * ((s - (l : ℝ)) / (w : ℝ)) = s := by field_simp; ring
  simpa only [he] using hb

end PartialBalayage.Maximal.Square
