/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.DiamondCoordinateIntegral
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual angular derivatives of the paired diamond generator

The crossed-axis kinks are retained. Local Lipschitz bounds justify differentiation of the
true paired integral, whose two actual crossed-axis contributions cancel by translation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PartialBalayage.Linear
open scoped NNReal

namespace PartialBalayage.Maximal.Square

/-- The actual backward coordinate profile along a fixed diamond radius. -/
def diamondAngularBackward (α r t a : ℝ) : ℝ := (|a - t| + r - a) ^ (-α)

/-- The true angular integrand of the paired coordinate generator. -/
def diamondAngularIntegrand (α r a t : ℝ) : ℝ := t ^ (-1 - α) *
  (2 * (r + t) ^ (-α) + diamondAngularBackward α r t a +
    diamondAngularBackward α r t (r - a) - 4 * r ^ (-α))

theorem diamondAngularBackward_eq_of_le {α r t a : ℝ} (ht : t ≤ a) :
    diamondAngularBackward α r t a = (r - t) ^ (-α) := by
  rw [diamondAngularBackward, abs_of_nonneg (sub_nonneg.mpr ht)]
  congr 1
  ring

theorem diamondAngularBackward_eq_of_lt {α r t a : ℝ} (ht : a < t) :
    diamondAngularBackward α r t a = (t + r - 2 * a) ^ (-α) := by
  rw [diamondAngularBackward, abs_of_neg (sub_neg.mpr ht)]
  congr 1
  ring

/-- The true backward profile has its ordinary derivative away from the crossing point. -/
theorem hasDerivAt_diamondAngularBackward {α r t a : ℝ}
    (ha : a < r) (hne : a ≠ t) :
    HasDerivAt (diamondAngularBackward α r t)
      (if a < t then 2 * α * (t + r - 2 * a) ^ (-1 - α) else 0) a := by
  have hp : |a - t| + r - a ≠ 0 := ne_of_gt (by linarith [abs_nonneg (a - t)])
  by_cases ht : a < t
  · have hd := ((hasDerivAt_abs_neg (sub_neg.mpr ht)).comp a
      ((hasDerivAt_id a).sub_const t)).add_const r
    have h := (hd.sub (hasDerivAt_id a)).rpow_const (p := -α) (Or.inl hp)
    rw [ite_eq_left ht]
    convert h using 1
    · rfl
    · dsimp only [Pi.sub_apply, Function.comp_apply, id_eq]
      rw [abs_of_neg (sub_neg.mpr ht)]
      have he : -(a - t) + r - a = t + r - 2 * a := by ring
      rw [he, show -α - 1 = -1 - α by ring]
      ring
  · have ht' : 0 < a - t := sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt ht) hne.symm)
    have hd := ((hasDerivAt_abs_pos ht').comp a
      ((hasDerivAt_id a).sub_const t)).add_const r
    have h := (hd.sub (hasDerivAt_id a)).rpow_const (p := -α) (Or.inl hp)
    rw [ite_eq_right ht]
    convert h using 1
    · rfl
    · simp

/-- The actual backward angular profile has a uniform local Lipschitz bound. -/
theorem lipschitzOnWith_diamondAngularBackward {α r δ : ℝ}
    (hα : 0 ≤ α) (hδ : 0 < δ) (t : ℝ) :
    LipschitzOnWith (2 * negativePowerLipConst (-α) δ (by linarith) hδ)
      (diamondAngularBackward α r t) (Icc δ (r - δ)) := by
  let L := negativePowerLipConst (-α) δ (by linarith) hδ
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' : δ ≤ |x - t| + r - x := by linarith [abs_nonneg (x - t), hx.2]
  have hy' : δ ≤ |y - t| + r - y := by linarith [abs_nonneg (y - t), hy.2]
  have h := (lipschitzOnWith_rpow_nonpos_Ici (neg_nonpos.mpr hα) hδ).dist_le_mul
    (|x - t| + r - x) hx' (|y - t| + r - y) hy'
  have hb : dist (|x - t| + r - x) (|y - t| + r - y) ≤ 2 * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    have he : |x - t| + r - x - (|y - t| + r - y) =
        (|x - t| - |y - t|) - (x - y) := by ring
    rw [he]
    have hxy := abs_abs_sub_abs_le_abs_sub (x - t) (y - t)
    simp only [sub_sub_sub_cancel_right] at hxy
    exact (abs_sub _ _).trans (by linarith)
  change dist ((|x - t| + r - x) ^ (-α)) ((|y - t| + r - y) ^ (-α)) ≤ _
  exact h.trans (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc, mul_comm, L] using
    mul_le_mul_of_nonneg_left hb L.coe_nonneg)

/-- The actual angular derivative, supported precisely on the crossed-axis tails. -/
def diamondAngularDerivative (α r a t : ℝ) : ℝ := 2 * α * t ^ (-1 - α) *
  ((if a < t then (t - a + (r - a)) ^ (-1 - α) else 0) -
    (if r - a < t then (t - (r - a) + a) ^ (-1 - α) else 0))

/-- At every noncrossing positive jump, the true paired integrand has its actual derivative. -/
theorem hasDerivAt_diamondAngularIntegrand {α r a t : ℝ}
    (ha0 : 0 < a) (har : a < r) (hta : a ≠ t) (htv : r - a ≠ t) :
    HasDerivAt (fun b ↦ diamondAngularIntegrand α r b t)
      (diamondAngularDerivative α r a t) a := by
  have hu := hasDerivAt_diamondAngularBackward (α := α) har hta
  have hv := (hasDerivAt_diamondAngularBackward (α := α)
    (by linarith : r - a < r) htv).comp a ((hasDerivAt_id a).const_sub r)
  have h := ((hu.const_add (2 * (r + t) ^ (-α))).add hv).sub_const
    (4 * r ^ (-α)) |>.const_mul (t ^ (-1 - α))
  convert h using 1
  · rfl
  · dsimp only [diamondAngularDerivative, Pi.add_apply, Pi.sub_apply, Function.comp_apply,
      id_eq]
    have he₁ : t + r - 2 * a = t - a + (r - a) := by ring
    have he₂ : t + r - 2 * (r - a) = t - (r - a) + a := by ring
    rw [he₁, he₂]
    split_ifs <;> ring

/-- Below the local distance to either axis, the actual angular integrand is constant. -/
theorem diamondAngularIntegrand_eq_of_le {α r δ a t : ℝ}
    (ha : a ∈ Icc δ (r - δ)) (ht : t ≤ δ) :
    diamondAngularIntegrand α r a t =
      t ^ (-1 - α) * (2 * (r + t) ^ (-α) + 2 * (r - t) ^ (-α) - 4 * r ^ (-α)) := by
  rw [diamondAngularIntegrand, diamondAngularBackward_eq_of_le (ht.trans ha.1),
    diamondAngularBackward_eq_of_le (by linarith [ha.2] : t ≤ r - a)]
  ring

/-- The genuine angular integrand has an integrable local Lipschitz majorant. -/
theorem lipschitzOnWith_diamondAngularIntegrand {α r δ t : ℝ}
    (hα : 0 ≤ α) (hδ : 0 < δ) (ht : 0 < t) :
    LipschitzOnWith (Real.nnabs (if δ < t then
      4 * (negativePowerLipConst (-α) δ (by linarith) hδ : ℝ) * t ^ (-1 - α) else 0))
      (fun a ↦ diamondAngularIntegrand α r a t) (Icc δ (r - δ)) := by
  let L := negativePowerLipConst (-α) δ (by linarith) hδ
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hdt : δ < t
  · have hl := lipschitzOnWith_diamondAngularBackward (r := r) hα hδ t
    have hu := hl.dist_le_mul x hx y hy
    have hv := hl.dist_le_mul (r - x) (by constructor <;> linarith [hx.1, hx.2])
      (r - y) (by constructor <;> linarith [hy.1, hy.2])
    have he : diamondAngularIntegrand α r x t - diamondAngularIntegrand α r y t =
        t ^ (-1 - α) * ((diamondAngularBackward α r t x -
          diamondAngularBackward α r t y) + (diamondAngularBackward α r t (r - x) -
            diamondAngularBackward α r t (r - y))) := by unfold diamondAngularIntegrand; ring
    rw [dist_eq_norm, he, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] at hu hv
    rw [show r - x - (r - y) = -(x - y) by ring, norm_neg] at hv
    have hs := (norm_add_le _ _).trans (add_le_add hu hv)
    rw [Real.coe_nnabs, ite_eq_left hdt,
      abs_of_nonneg (by positivity : 0 ≤ 4 * (L : ℝ) * t ^ (-1 - α))]
    exact (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg ht.le _)).trans_eq (by
      simp only [L, dist_eq_norm]
      ring)
  · rw [diamondAngularIntegrand_eq_of_le hx (le_of_not_gt hdt),
      diamondAngularIntegrand_eq_of_le hy (le_of_not_gt hdt), dist_self]
    positivity

end PartialBalayage.Maximal.Square
