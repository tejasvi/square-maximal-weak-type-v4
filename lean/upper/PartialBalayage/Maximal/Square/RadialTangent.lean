/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40 instead of 6/5 (tangent with exponents -47/40 and -87/40). -/
module

public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.PowerEnclosure
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Genuine radial tangent bounds for the square certificate

The radial lower polynomial is justified by actual convexity on the positive half-line.
Downward rational height and slope bounds remain valid because the tangent is taken at
the maximum radius of the triangle. The origin is excluded explicitly from the tangent.
-/

@[expose] public section

noncomputable section

open Set

namespace PartialBalayage.Maximal.Square

/-- A nonpositive real power is genuinely convex on the positive half-line. -/
theorem convexOn_rpow_of_nonpos (p : ℝ) (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x ^ p) := by
  have hd (x : ℝ) (hx : 0 < x) :=
    Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')
  have hm : MonotoneOn (deriv (fun x : ℝ ↦ x ^ p)) (interior (Ioi 0)) := by
    intro x hx y hy hxy
    have hx' : 0 < x := interior_subset hx
    have hy' : 0 < y := interior_subset hy
    rw [(hd x hx').deriv, (hd y hy').deriv]
    apply mul_le_mul_of_nonpos_left
    · exact Real.rpow_le_rpow_of_nonpos hx' hxy (by linarith)
    · exact hp
  exact hm.convexOn_of_deriv (convex_Ioi 0)
    (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (ne_of_gt hx)))
    (fun x hx ↦ (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)

/-- The source's order-47/40 tangent is an actual real inequality. -/
theorem rpow_six_fifths_tangent {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hrq : r ≤ q) :
    q ^ (-(47 / 40 : ℝ)) + (47 / 40 : ℝ) * q ^ (-(87 / 40 : ℝ)) * (q - r) ≤
      r ^ (-(47 / 40 : ℝ)) := by
  rcases eq_or_lt_of_le hrq with h | h
  · subst q
    simp
  have hd : HasDerivAt (fun x : ℝ ↦ x ^ (-(47 / 40 : ℝ)))
      (-(47 / 40 : ℝ) * q ^ (-(87 / 40 : ℝ))) q := by
    convert Real.hasDerivAt_rpow_const (p := -(47 / 40 : ℝ)) (Or.inl hq.ne') using 1
    norm_num
  have hconv := convexOn_rpow_of_nonpos (-(47 / 40 : ℝ)) (by norm_num)
  have hs := hconv.slope_le_of_hasDerivAt hr hq h hd
  rw [slope_def_field] at hs
  have hs' := (div_le_iff₀ (sub_pos.mpr h)).mp hs
  nlinarith

/-- Genuine downward height and slope bounds give a lower bound for the actual radial base. -/
theorem radialBase_lower_tangent {u v q height slope : ℝ}
    (hr : 0 < diamondRadius u v) (hq : 0 < q) (hrq : diamondRadius u v ≤ q)
    (hheight : height ≤ radialCoefficient *
      (q ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))))
    (hslope : slope ≤ (47 / 40 : ℝ) * radialCoefficient * q ^ (-(87 / 40 : ℝ))) :
    height + slope * (q - diamondRadius u v) ≤ radialBase u v := by
  have ht := mul_le_mul_of_nonneg_left (rpow_six_fifths_tangent hr hq hrq)
    radialCoefficient_pos.le
  have hs := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hrq)
  have hm := le_max_left
    ((diamondRadius u v) ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))) 0
  have hm' := mul_le_mul_of_nonneg_left hm radialCoefficient_pos.le
  unfold radialBase
  nlinarith

end PartialBalayage.Maximal.Square
