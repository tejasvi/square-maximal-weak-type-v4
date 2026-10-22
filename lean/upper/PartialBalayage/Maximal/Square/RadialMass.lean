/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: exponent 47/40 instead of 6/5 (so 1 - alpha = -7/40, 2 - alpha = 33/40);
the mass is (94/33) c R^(33/40) instead of 3 c R^(4/5). -/
module

public import PartialBalayage.Maximal.Square.DiamondSquareTransport
public import PartialBalayage.Linear.FractionalCutoffBound
public import PartialBalayage.Maximal.Square.Integrability

/-!
# Exact mass of the actual truncated diamond singularity

The actual planar radial base has mass `(94/33) * a * R^(33/40)`. The identity uses
the proved diamond Jacobian and ordinary convergent power integrals at zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin 2 → ℝ

private theorem weighted_radialBase_eq {t : ℝ} (ht : t ∈ Ioc 0 supportRadius) :
    t * radialBase t 0 = radialCoefficient *
      (t ^ (-(7 / 40 : ℝ)) - t * supportRadius ^ (-(47 / 40 : ℝ))) := by
  have hp := Real.rpow_le_rpow_of_nonpos ht.1 ht.2
    (by norm_num : -(47 / 40 : ℝ) ≤ 0)
  have he : t * t ^ (-(47 / 40 : ℝ)) = t ^ (-(7 / 40 : ℝ)) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(47 / 40 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht.1]; norm_num
  simp only [radialBase, diamondRadius, abs_of_pos ht.1, abs_zero, add_zero,
    max_eq_left (sub_nonneg.mpr hp)]
  calc
    _ = radialCoefficient * (t * t ^ (-(47 / 40 : ℝ)) -
        t * supportRadius ^ (-(47 / 40 : ℝ))) := by ring
    _ = _ := by rw [he]

private theorem integrable_weighted_radialBase_near :
    IntegrableOn (fun t : ℝ ↦ t * radialBase t 0) (Ioc 0 supportRadius) := by
  have hp : IntegrableOn (fun t : ℝ ↦ t ^ (-(7 / 40 : ℝ))) (Ioc 0 supportRadius) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff supportRadius_pos).mpr (by norm_num)
  have hi : IntegrableOn (fun t : ℝ ↦ t) (Ioc 0 supportRadius) :=
    continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply ((hp.sub (hi.mul_const (supportRadius ^ (-(47 / 40 : ℝ))))).const_mul
    radialCoefficient).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (weighted_radialBase_eq ht).symm

private theorem weighted_radialBase_far_zero {t : ℝ} (ht : supportRadius < t) :
    t * radialBase t 0 = 0 := by
  rw [radialBase_eq_zero_of_supportRadius_le, mul_zero]
  simpa only [diamondRadius, abs_of_pos (supportRadius_pos.trans ht), abs_zero,
    add_zero] using ht.le

/-- The exact convergent one-dimensional mass integral for the genuine radial base. -/
theorem integral_weighted_radialBase :
    (∫ t in Ioi (0 : ℝ), t * radialBase t 0) =
      (47 / 66 : ℝ) * radialCoefficient * supportRadius ^ (33 / 40 : ℝ) := by
  have hf : IntegrableOn (fun t : ℝ ↦ t * radialBase t 0) (Ioi supportRadius) := by
    apply (integrable_zero ℝ ℝ (volume.restrict (Ioi supportRadius))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (weighted_radialBase_far_zero ht).symm
  have hz : (∫ t in Ioi supportRadius, t * radialBase t 0) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact weighted_radialBase_far_zero ht
  have hd : Disjoint (Ioc (0 : ℝ) supportRadius) (Ioi supportRadius) := by
    apply disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  rw [← Ioc_union_Ioi_eq_Ioi supportRadius_pos.le,
    setIntegral_union hd measurableSet_Ioi integrable_weighted_radialBase_near hf, hz, add_zero]
  have hp : IntegrableOn (fun t : ℝ ↦ t ^ (-(7 / 40 : ℝ))) (Ioc 0 supportRadius) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff supportRadius_pos).mpr (by norm_num)
  have hi : IntegrableOn (fun t : ℝ ↦ t) (Ioc 0 supportRadius) :=
    continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : (∫ t in Ioc 0 supportRadius, t * radialBase t 0) =
      radialCoefficient * ((∫ t in Ioc 0 supportRadius, t ^ (-(7 / 40 : ℝ))) -
        (∫ t in Ioc 0 supportRadius, t) * supportRadius ^ (-(47 / 40 : ℝ))) := by
    calc
      _ = ∫ t in Ioc 0 supportRadius, radialCoefficient *
          (t ^ (-(7 / 40 : ℝ)) - t * supportRadius ^ (-(47 / 40 : ℝ))) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact weighted_radialBase_eq ht
      _ = _ := by rw [integral_const_mul, integral_sub hp (hi.mul_const _), integral_mul_const]
  have hid : (∫ t in Ioc (0 : ℝ) supportRadius, t) = supportRadius ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le supportRadius_pos.le, integral_id]
    norm_num
  have hpow : (∫ t in Ioc (0 : ℝ) supportRadius, t ^ (-(7 / 40 : ℝ))) =
      supportRadius ^ (33 / 40 : ℝ) / (33 / 40) := by
    convert PartialBalayage.Linear.integral_stable_near_zero
      (α := (47 / 40 : ℝ)) (by norm_num) supportRadius_pos using 1 <;> norm_num
  rw [he, hid, hpow]
  have hm : supportRadius ^ (2 : ℕ) * supportRadius ^ (-(47 / 40 : ℝ)) =
      supportRadius ^ (33 / 40 : ℝ) := by
    rw [← Real.rpow_natCast supportRadius 2, ← Real.rpow_add supportRadius_pos]
    norm_num
  calc
    _ = radialCoefficient * (supportRadius ^ (33 / 40 : ℝ) / (33 / 40) -
        (supportRadius ^ (2 : ℕ) * supportRadius ^ (-(47 / 40 : ℝ))) / 2) := by ring
    _ = _ := by rw [hm]; ring

/-- The true planar radial mass, in the original Euclidean volume normalization. -/
theorem integral_radialBase :
    (∫ x : E, radialBase (x 0) (x 1)) =
      94 / 33 * radialCoefficient * supportRadius ^ (33 / 40 : ℝ) := by
  have he := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp'
    (fun x : P ↦ radialBase (x 0) (x 1))
  simp only [MeasurableEquiv.toLp_symm_apply] at he
  rw [he]
  have hr := integral_diamondRadius (fun r ↦ radialBase r 0)
  have hc : ∀ x : P, radialBase (x 0) (x 1) = radialBase (diamondRadius (x 0) (x 1)) 0 := by
    intro x
    have hn : 0 ≤ |x 0| + |x 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    simp only [radialBase, diamondRadius, abs_of_nonneg hn, abs_zero, add_zero]
  simp_rw [hc]
  rw [hr, integral_weighted_radialBase]
  ring

end PartialBalayage.Maximal.Square
