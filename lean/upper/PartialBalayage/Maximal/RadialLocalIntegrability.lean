/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PolarSwap

/-!
# Local radial integrability against compactly supported tests

The polar Jacobian criterion transfers scalar local integrability into actual Euclidean
integrability. A bounded compactly supported test density can then multiply the radial weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set

namespace PartialBalayage

/-- Locally integrable radial weights pair integrably with bounded continuous compactly
supported densities, with no ambient integrability assumption. -/
theorem integrable_radial_mul_of_weighted_local (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) (φ : ℝ → ℝ) {b : ℝ}
    (hφ : ∀ R : ℝ, b < R → IntegrableOn (fun r ↦ r ^ (n - 1) * φ r) (Ioo 0 R))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) :
    Integrable (fun y ↦ φ ‖y - x‖ * g y) := by
  obtain ⟨R, hbR, hR⟩ := hgsupp.isBounded.subset_ball_lt b x
  let φR := (Iio R).indicator φ
  have hweight : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * φR r) (Ioi 0) := by
    have hi : IntegrableOn ((Iio R).indicator (fun r : ℝ ↦ r ^ (n - 1) * φ r))
        (Ioi 0) := by
      rw [integrableOn_indicator_iff measurableSet_Iio, Iio_inter_Ioi]
      exact hφ R hbR
    apply hi.congr_fun
    · intro r _
      by_cases hr : r < R <;> simp [φR, hr]
    · exact measurableSet_Ioi
  have hnorm : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦ φR ‖y‖) := by
    apply (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))).mpr
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hweight
  have hnormx : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦ φR ‖y - x‖) := by
    convert hnorm.comp_add_left (-x) using 1
    funext y
    rw [add_comm, ← sub_eq_add_neg]
  obtain ⟨C, hC⟩ := hgsupp.exists_bound_of_continuous hg
  have hmul := hnormx.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  apply hmul.congr
  filter_upwards with y
  by_cases hyr : ‖y - x‖ < R
  · simp only [φR, Set.indicator_of_mem (show ‖y - x‖ ∈ Iio R from hyr)]
  · have hgy : g y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hy
      have hball := hR hy
      rw [mem_ball, dist_eq_norm] at hball
      exact hyr hball
    simp only [hgy, mul_zero]

end PartialBalayage
