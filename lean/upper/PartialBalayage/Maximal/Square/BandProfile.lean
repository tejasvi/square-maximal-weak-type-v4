/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.DiamondGeneratorExterior
public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.RadialTangent
public import PartialBalayage.Maximal.Square.GeneratorScaling
public import PartialBalayage.Linear.StableGeneratorScaling

/-!
# The radial coordinate generator outside the diamond

At a point `(u, v)` with `u, v > 0` and `u + v > R` the truncated diamond power vanishes near the
point, and its coordinate generator along the first coordinate is the line integral
`∫_{v-R}^{R-v} (u - s)^(-1-α) Ψ(|s| + v) ds`, `Ψ(q) = max (q^(-α) - R^(-α)) 0`.

Per line point `s` the integrand is a product of two nonnegative convex decreasing functions of
`u` and of `v`. Their tangents at a far corner `(u₁, v₁) ≥ (u, v)` therefore give the lower plane
`J(u, v) ≥ J(u₁, v₁) + Du (u₁ - u) + Dv (v₁ - v)` with nonnegative slope integrals `Du`, `Dv`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral PartialBalayage.Linear

namespace PartialBalayage.Maximal.Square

/-- The truncated profile `Ψ(q) = max (q^(-α) - R^(-α)) 0` of the diamond radius. -/
def bandPsi (q : ℝ) : ℝ := max (q ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))) 0

/-- The magnitude of the left derivative of `Ψ`, divided by `α`. -/
def bandPsiSlope (q : ℝ) : ℝ := if q < supportRadius then q ^ (-1 - (47 / 40 : ℝ)) else 0

/-- The exterior first-coordinate line integral. -/
def bandLine (u v : ℝ) : ℝ :=
  ∫ s in (v - supportRadius)..(supportRadius - v), (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v)

/-- The first-coordinate slope integral at a corner. -/
def bandSlopeU (u v : ℝ) : ℝ :=
  ∫ s in (v - supportRadius)..(supportRadius - v),
    (1 + 47 / 40) * (u - s) ^ (-2 - (47 / 40 : ℝ)) * bandPsi (|s| + v)

/-- The second-coordinate slope integral at a corner. -/
def bandSlopeV (u v : ℝ) : ℝ :=
  ∫ s in (v - supportRadius)..(supportRadius - v),
    (47 / 40) * (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsiSlope (|s| + v)

theorem bandPsi_nonneg (q : ℝ) : 0 ≤ bandPsi q := le_max_right _ _

theorem bandPsi_eq_zero {q : ℝ} (hq : supportRadius ≤ q) : bandPsi q = 0 := by
  have hp := Real.rpow_le_rpow_of_nonpos supportRadius_pos hq (by norm_num : -(47 / 40 : ℝ) ≤ 0)
  exact max_eq_right (sub_nonpos.mpr hp)

theorem bandPsiSlope_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ bandPsiSlope q := by
  unfold bandPsiSlope
  split_ifs
  · exact Real.rpow_nonneg hq _
  · exact le_rfl

/-- Tangent inequality of the convex decreasing power `x ↦ x^(-1-α)`. -/
theorem rpow_neg_tangent {x x₁ : ℝ} (hx : 0 < x) (hxx : x ≤ x₁) :
    x₁ ^ (-1 - (47 / 40 : ℝ)) + (1 + 47 / 40) * x₁ ^ (-2 - (47 / 40 : ℝ)) * (x₁ - x) ≤
      x ^ (-1 - (47 / 40 : ℝ)) := by
  have hx₁ : 0 < x₁ := hx.trans_le hxx
  have hc : ConvexOn ℝ (Ioi 0) fun y : ℝ ↦ y ^ (-1 - (47 / 40 : ℝ)) :=
    convexOn_rpow_of_nonpos _ (by norm_num)
  have hd : HasDerivAt (fun y : ℝ ↦ y ^ (-1 - (47 / 40 : ℝ)))
      ((-1 - (47 / 40 : ℝ)) * x₁ ^ (-1 - (47 / 40 : ℝ) - 1)) x₁ :=
    Real.hasDerivAt_rpow_const (Or.inl hx₁.ne')
  rcases hxx.lt_or_eq with hlt | heq
  · have hs := hc.slope_le_of_hasDerivAt (mem_Ioi.mpr hx) (mem_Ioi.mpr hx₁) hlt hd
    rw [slope_def_field] at hs
    have he : (-1 - (47 / 40 : ℝ)) - 1 = -2 - 47 / 40 := by ring
    rw [he] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst heq; simp

/-- Tangent inequality of the truncated profile from the left. -/
theorem bandPsi_tangent {q q₁ : ℝ} (hq : 0 < q) (hqq : q ≤ q₁) :
    bandPsi q₁ + (47 / 40) * bandPsiSlope q₁ * (q₁ - q) ≤ bandPsi q := by
  unfold bandPsiSlope
  split_ifs with h
  · have hq₁ : 0 < q₁ := hq.trans_le hqq
    have hc : ConvexOn ℝ (Ioi 0) fun y : ℝ ↦ y ^ (-(47 / 40 : ℝ)) :=
      convexOn_rpow_of_nonpos _ (by norm_num)
    have hd : HasDerivAt (fun y : ℝ ↦ y ^ (-(47 / 40 : ℝ)))
        ((-(47 / 40 : ℝ)) * q₁ ^ (-(47 / 40 : ℝ) - 1)) q₁ :=
      Real.hasDerivAt_rpow_const (Or.inl hq₁.ne')
    have htan : q₁ ^ (-(47 / 40 : ℝ)) + (47 / 40) * q₁ ^ (-1 - (47 / 40 : ℝ)) * (q₁ - q) ≤
        q ^ (-(47 / 40 : ℝ)) := by
      rcases hqq.lt_or_eq with hlt | heq
      · have hs := hc.slope_le_of_hasDerivAt (mem_Ioi.mpr hq) (mem_Ioi.mpr hq₁) hlt hd
        rw [slope_def_field] at hs
        have he : (-(47 / 40 : ℝ)) - 1 = -1 - 47 / 40 := by ring
        rw [he] at hs
        have hs' := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
        nlinarith
      · subst heq; simp
    have hpos : supportRadius ^ (-(47 / 40 : ℝ)) ≤ q₁ ^ (-(47 / 40 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hq₁ h.le (by norm_num)
    have h₁ : bandPsi q₁ = q₁ ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ)) :=
      max_eq_left (sub_nonneg.mpr hpos)
    rw [h₁]
    calc
      _ ≤ q ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ)) := by linarith
      _ ≤ bandPsi q := le_max_left _ _
  · simp only [mul_zero, zero_mul, add_zero]
    rw [bandPsi_eq_zero (not_lt.mp h)]
    exact bandPsi_nonneg q

/-- The pointwise product inequality behind the far-corner plane. -/
theorem band_product_tangent {u u₁ v v₁ s : ℝ} (hv : 0 < v) (hus : s < u) (huu : u ≤ u₁)
    (hvv : v ≤ v₁) :
    (u₁ - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v₁) +
        (1 + 47 / 40) * (u₁ - s) ^ (-2 - (47 / 40 : ℝ)) * bandPsi (|s| + v₁) * (u₁ - u) +
        (47 / 40) * (u₁ - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsiSlope (|s| + v₁) * (v₁ - v) ≤
      (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v) := by
  have hx : 0 < u - s := sub_pos.mpr hus
  have hxx : u - s ≤ u₁ - s := by linarith
  have hq : 0 < |s| + v := by positivity
  have hqq : |s| + v ≤ |s| + v₁ := by linarith
  have hA := rpow_neg_tangent hx hxx
  have hB := bandPsi_tangent hq hqq
  set A₁ := (u₁ - s) ^ (-1 - (47 / 40 : ℝ))
  set a := (1 + 47 / 40) * (u₁ - s) ^ (-2 - (47 / 40 : ℝ))
  set B₁ := bandPsi (|s| + v₁)
  set b := (47 / 40) * bandPsiSlope (|s| + v₁)
  have hA₁ : 0 ≤ A₁ := Real.rpow_nonneg (by linarith) _
  have ha : 0 ≤ a := mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  have hB₁ : 0 ≤ B₁ := bandPsi_nonneg _
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (bandPsiSlope_nonneg _ (by linarith [abs_nonneg s]))
  have hdu : 0 ≤ u₁ - u := by linarith
  have hdv : 0 ≤ v₁ - v := by linarith
  have hA' : A₁ + a * (u₁ - u) ≤ (u - s) ^ (-1 - (47 / 40 : ℝ)) := by
    simpa [a, A₁, mul_assoc, sub_sub_sub_cancel_right] using hA
  have hB' : B₁ + b * (v₁ - v) ≤ bandPsi (|s| + v) := by
    simpa [b, B₁, mul_assoc, add_sub_add_left_eq_sub] using hB
  have hprod := mul_le_mul hA' hB' (add_nonneg hB₁ (mul_nonneg hb hdv)) (Real.rpow_nonneg hx.le _)
  have hcross : 0 ≤ a * (u₁ - u) * (b * (v₁ - v)) := by positivity
  calc
    _ = A₁ * B₁ + a * (u₁ - u) * B₁ + A₁ * (b * (v₁ - v)) := by ring
    _ ≤ (A₁ + a * (u₁ - u)) * (B₁ + b * (v₁ - v)) := by nlinarith
    _ ≤ _ := hprod

end PartialBalayage.Maximal.Square

namespace PartialBalayage.Maximal.Square

/-- The line integrand. -/
def bandIntegrand (u v s : ℝ) : ℝ := (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v)

theorem bandIntegrand_eq_zero {u v s : ℝ} (hs : supportRadius ≤ |s| + v) : bandIntegrand u v s = 0 := by
  simp [bandIntegrand, bandPsi_eq_zero hs]

theorem continuous_bandPsi_comp {v : ℝ} (hv : 0 < v) : Continuous fun s : ℝ ↦ bandPsi (|s| + v) := by
  unfold bandPsi
  apply (Continuous.sub ?_ continuous_const).max continuous_const
  apply Continuous.rpow_const (continuous_abs.add continuous_const)
  intro s; left
  exact (show (0 : ℝ) < |s| + v by linarith [abs_nonneg s]).ne'

theorem continuousOn_bandIntegrand {u v : ℝ} (hv : 0 < v) (hr : supportRadius < u + v) :
    ContinuousOn (bandIntegrand u v) (Icc (v - supportRadius) (supportRadius - v)) := by
  apply ContinuousOn.mul _ (continuous_bandPsi_comp hv).continuousOn
  apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
  intro s hs; left
  have := hs.2
  exact (show (0 : ℝ) < u - s by linarith).ne'

/-- The exterior profile's coordinate generator integral is the line integral. -/
theorem stableGeneratorIntegral_profile_eq_bandLine {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hvR : v < supportRadius) (hr : supportRadius < u + v) :
    stableGeneratorIntegral (47 / 40)
        (diamondCoordinateTruncatedProfile (47 / 40) supportRadius u v) = bandLine u v := by
  set T := u + supportRadius - v
  have hT : 0 < T := by simp only [T]; linarith
  have hprof (s : ℝ) : diamondCoordinateTruncatedProfile (47 / 40) supportRadius u v s =
      bandPsi (|u + s| + v) := by
    simp [diamondCoordinateTruncatedProfile, diamondCoordinateProfile, bandPsi]
  have hint (t : ℝ) (ht : 0 < t) : t ^ (-1 - (47 / 40 : ℝ)) •
      stableSecondDifference (diamondCoordinateTruncatedProfile (47 / 40) supportRadius u v) t =
        bandIntegrand u v (u - t) := by
    have h₁ : supportRadius ≤ |u + t| + v := by
      rw [abs_of_pos (by linarith)]; linarith
    have h₂ : supportRadius ≤ |u + 0| + v := by rw [add_zero, abs_of_pos hu]; linarith
    simp only [stableSecondDifference, hprof, bandPsi_eq_zero h₁, smul_eq_mul, bandIntegrand]
    rw [show (u + -t) = u - t by ring, bandPsi_eq_zero h₂, sub_sub_cancel]
    ring
  unfold stableGeneratorIntegral
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ hint t ht)]
  have hzero : ∀ t ∈ Ioi (0 : ℝ) \ Ioc 0 T, bandIntegrand u v (u - t) = 0 := by
    intro t ht
    have htT : T < t := by
      rcases ht with ⟨h₀, h₁⟩
      by_contra hle
      exact h₁ ⟨h₀, not_lt.mp hle⟩
    apply bandIntegrand_eq_zero
    rw [abs_of_neg (by simp only [T] at htT; linarith)]
    simp only [T] at htT; linarith
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero,
    ← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_comp_sub_left (bandIntegrand u v) u]
  rw [show u - T = v - supportRadius by simp only [T]; ring, sub_zero]
  have hsplit : (∫ s in (v - supportRadius)..u, bandIntegrand u v s) =
      (∫ s in (v - supportRadius)..(supportRadius - v), bandIntegrand u v s) +
        ∫ s in (supportRadius - v)..u, bandIntegrand u v s := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact (continuousOn_bandIntegrand hv hr).intervalIntegrable_of_Icc (by linarith)
    · apply (intervalIntegrable_const (c := (0 : ℝ))).congr
      rw [uIoc_of_le (by linarith)]
      intro s hs
      show (0 : ℝ) = bandIntegrand u v s
      rw [bandIntegrand_eq_zero]
      rw [abs_of_pos (by linarith [hs.1])]
      linarith [hs.1]
  have hz : (∫ s in (supportRadius - v)..u, bandIntegrand u v s) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    apply bandIntegrand_eq_zero
    rw [abs_of_pos (by linarith [hs.1])]
    linarith [hs.1]
  rw [hsplit, hz, add_zero]
  rfl

end PartialBalayage.Maximal.Square

namespace PartialBalayage.Maximal.Square

theorem bandPsiSlope_comp_eq_indicator (v₁ : ℝ) :
    (fun s : ℝ ↦ bandPsiSlope (|s| + v₁)) =
      {s : ℝ | |s| + v₁ < supportRadius}.indicator (fun s ↦ (|s| + v₁) ^ (-1 - (47 / 40 : ℝ))) := by
  funext s
  simp only [bandPsiSlope, Set.indicator, Set.mem_setOf_eq]

theorem intervalIntegrable_bandPsiSlope {v₁ : ℝ} (hv₁ : 0 < v₁) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ bandPsiSlope (|s| + v₁)) volume a b := by
  rw [bandPsiSlope_comp_eq_indicator]
  have hc : Continuous fun s : ℝ ↦ (|s| + v₁) ^ (-1 - (47 / 40 : ℝ)) := by
    apply Continuous.rpow_const (continuous_abs.add continuous_const)
    intro s; left; exact (show (0 : ℝ) < |s| + v₁ by linarith [abs_nonneg s]).ne'
  have hm : MeasurableSet {s : ℝ | |s| + v₁ < supportRadius} :=
    measurableSet_lt (continuous_abs.add continuous_const).measurable measurable_const
  rw [intervalIntegrable_iff]
  exact (hc.integrableOn_uIcc.mono_set uIoc_subset_uIcc).indicator hm

/-- Outside the corner's own line segment all corner integrands vanish, so the corner integrals
can be taken over the longer segment of a point below the corner. -/
theorem corner_integral_extend {f : ℝ → ℝ} {v v₁ : ℝ} (hvv : v ≤ v₁) (hv₁R : v₁ < supportRadius)
    (hf : ∀ s, supportRadius ≤ |s| + v₁ → f s = 0)
    (hint : IntervalIntegrable f volume (v - supportRadius) (supportRadius - v)) :
    (∫ s in (v₁ - supportRadius)..(supportRadius - v₁), f s) =
      ∫ s in (v - supportRadius)..(supportRadius - v), f s := by
  have h₁ : IntervalIntegrable f volume (v - supportRadius) (v₁ - supportRadius) :=
    hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have h₂ : IntervalIntegrable f volume (v₁ - supportRadius) (supportRadius - v₁) :=
    hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) (by linarith))
  have h₃ : IntervalIntegrable f volume (supportRadius - v₁) (supportRadius - v) :=
    hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have z₁ : (∫ s in (v - supportRadius)..(v₁ - supportRadius), f s) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    apply hf
    rw [abs_of_neg (by linarith [hs.2])]
    linarith [hs.2]
  have z₃ : (∫ s in (supportRadius - v₁)..(supportRadius - v), f s) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    apply hf
    rw [abs_of_pos (by linarith [hs.1])]
    linarith [hs.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ (h₂.trans h₃),
    ← intervalIntegral.integral_add_adjacent_intervals h₂ h₃, z₁, z₃]
  ring

/-- The far-corner tangent plane is a lower bound of the exterior line integral. -/
theorem bandLine_plane_le {u u₁ v v₁ : ℝ} (hu : 0 < u) (hv : 0 < v) (hvR : v < supportRadius)
    (hr : supportRadius < u + v) (huu : u ≤ u₁) (hvv : v ≤ v₁) :
    bandLine u₁ v₁ + bandSlopeU u₁ v₁ * (u₁ - u) + bandSlopeV u₁ v₁ * (v₁ - v) ≤ bandLine u v := by
  have hdom : ∀ s ∈ Icc (v - supportRadius) (supportRadius - v), s < u := fun s hs ↦ by
    linarith [hs.2]
  have hv₁ : 0 < v₁ := hv.trans_le hvv
  have hnonneg : 0 ≤ bandLine u v := by
    unfold bandLine
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hdom s hs]) _) (bandPsi_nonneg _)
  by_cases hv₁R : supportRadius ≤ v₁
  · -- every corner integrand vanishes
    have hz : ∀ (g : ℝ → ℝ) (F : ℝ → ℝ),
        (∫ s in (v₁ - supportRadius)..(supportRadius - v₁), g s * F (|s| + v₁)) = 0 →
          True := fun _ _ _ ↦ trivial
    clear hz
    have hPsi : ∀ s : ℝ, bandPsi (|s| + v₁) = 0 := fun s ↦ bandPsi_eq_zero (by linarith [abs_nonneg s])
    have hSl : ∀ s : ℝ, bandPsiSlope (|s| + v₁) = 0 := fun s ↦ by
      simp only [bandPsiSlope, ite_eq_right_iff]; intro h; linarith [abs_nonneg s]
    simp only [bandLine, bandSlopeU, bandSlopeV, hPsi, hSl, mul_zero, intervalIntegral.integral_zero,
      zero_mul, add_zero]
    exact hnonneg
  · push_neg at hv₁R
    have hc₀ : ContinuousOn (fun s ↦ (u₁ - s) ^ (-1 - (47 / 40 : ℝ)))
        (Icc (v - supportRadius) (supportRadius - v)) := by
      apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      intro s hs; left; exact (show (0 : ℝ) < u₁ - s by linarith [hdom s hs]).ne'
    have hc₂ : ContinuousOn (fun s ↦ (u₁ - s) ^ (-2 - (47 / 40 : ℝ)))
        (Icc (v - supportRadius) (supportRadius - v)) := by
      apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      intro s hs; left; exact (show (0 : ℝ) < u₁ - s by linarith [hdom s hs]).ne'
    have hle : v - supportRadius ≤ supportRadius - v := by linarith
    have iJ : IntervalIntegrable (fun s ↦ (u₁ - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v₁)) volume
        (v - supportRadius) (supportRadius - v) :=
      (hc₀.mul (continuous_bandPsi_comp hv₁).continuousOn).intervalIntegrable_of_Icc hle
    have iU : IntervalIntegrable (fun s ↦ (1 + 47 / 40) * (u₁ - s) ^ (-2 - (47 / 40 : ℝ)) *
        bandPsi (|s| + v₁)) volume (v - supportRadius) (supportRadius - v) :=
      ((continuousOn_const.mul hc₂).mul (continuous_bandPsi_comp hv₁).continuousOn).intervalIntegrable_of_Icc hle
    have iV : IntervalIntegrable (fun s ↦ (47 / 40) * (u₁ - s) ^ (-1 - (47 / 40 : ℝ)) *
        bandPsiSlope (|s| + v₁)) volume (v - supportRadius) (supportRadius - v) := by
      have h : IntervalIntegrable (fun s ↦ ((47 / 40) * (u₁ - s) ^ (-1 - (47 / 40 : ℝ))) *
          bandPsiSlope (|s| + v₁)) volume (v - supportRadius) (supportRadius - v) :=
        (intervalIntegrable_bandPsiSlope hv₁ (v - supportRadius) (supportRadius - v)).continuousOn_mul
          (continuousOn_const.mul (hc₀.mono (uIcc_of_le hle).le))
      exact h
    have eJ := corner_integral_extend hvv hv₁R (fun s hs ↦ by simp [bandPsi_eq_zero hs]) iJ
    have eU := corner_integral_extend hvv hv₁R (fun s hs ↦ by simp [bandPsi_eq_zero hs]) iU
    have eV := corner_integral_extend hvv hv₁R (fun s hs ↦ by
      simp only [bandPsiSlope, mul_ite, mul_zero, ite_eq_right_iff]; intro h; linarith) iV
    have iB : IntervalIntegrable (bandIntegrand u v) volume (v - supportRadius) (supportRadius - v) :=
      (continuousOn_bandIntegrand hv hr).intervalIntegrable_of_Icc hle
    unfold bandLine bandSlopeU bandSlopeV
    rw [eJ, eU, eV, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add iJ (iU.mul_const _),
      ← intervalIntegral.integral_add (iJ.add (iU.mul_const _)) (iV.mul_const _)]
    apply intervalIntegral.integral_mono_on hle ((iJ.add (iU.mul_const _)).add (iV.mul_const _)) iB
    intro s hs
    exact band_product_tangent hv (hdom s hs) huu hvv

end PartialBalayage.Maximal.Square

namespace PartialBalayage.Maximal.Square

/-- Splitting a line integral of the shape `∫ g(s) Ψ(|s| + v)` at the origin and substituting
`q = v ± s` gives the integral over the profile values `q ∈ [v, R]`. -/
theorem line_eq_q_form {g : ℝ → ℝ} {F : ℝ → ℝ} {v : ℝ} (hv : 0 < v) (hvR : v < supportRadius)
    (hc : ContinuousOn (fun s ↦ g s * F (|s| + v)) (Icc (v - supportRadius) (supportRadius - v))) :
    (∫ s in (v - supportRadius)..(supportRadius - v), g s * F (|s| + v)) =
      ∫ q in v..supportRadius, F q * (g (q - v) + g (v - q)) := by
  have hle₁ : v - supportRadius ≤ 0 := by linarith
  have hle₂ : (0 : ℝ) ≤ supportRadius - v := by linarith
  have i₁ : IntervalIntegrable (fun s ↦ g s * F (|s| + v)) volume (v - supportRadius) 0 :=
    (hc.mono (Icc_subset_Icc le_rfl hle₂)).intervalIntegrable_of_Icc hle₁
  have i₂ : IntervalIntegrable (fun s ↦ g s * F (|s| + v)) volume 0 (supportRadius - v) :=
    (hc.mono (Icc_subset_Icc hle₁ le_rfl)).intervalIntegrable_of_Icc hle₂
  rw [← intervalIntegral.integral_add_adjacent_intervals i₁ i₂]
  have e₁ : (∫ s in (v - supportRadius)..0, g s * F (|s| + v)) =
      ∫ q in v..supportRadius, g (v - q) * F (|v - q| + v) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s ↦ g s * F (|s| + v)) v]
    simp only [sub_self]
  have e₂ : (∫ s in (0 : ℝ)..(supportRadius - v), g s * F (|s| + v)) =
      ∫ q in v..supportRadius, g (q - v) * F (|q - v| + v) := by
    rw [intervalIntegral.integral_comp_sub_right (fun s ↦ g s * F (|s| + v)) v]
    simp only [sub_self]
  rw [e₁, e₂]
  have hmap : ∀ f : ℝ → ℝ, IntervalIntegrable (fun s ↦ g s * F (|s| + v)) volume
      (v - supportRadius) (supportRadius - v) → True := fun _ _ ↦ trivial
  clear hmap
  have j₁ : IntervalIntegrable (fun q ↦ g (v - q) * F (|v - q| + v)) volume v supportRadius := by
    have h := i₁.comp_sub_left v
    rw [show v - (v - supportRadius) = supportRadius by ring, sub_zero] at h
    exact h.symm
  have j₂ : IntervalIntegrable (fun q ↦ g (q - v) * F (|q - v| + v)) volume v supportRadius := by
    have h := i₂.comp_sub_right v
    rw [zero_add, show supportRadius - v + v = supportRadius by ring] at h
    exact h
  rw [← intervalIntegral.integral_add j₁ j₂]
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le hvR.le] at hq
  have h₁ : |v - q| + v = q := by rw [abs_of_nonpos (by linarith [hq.1])]; ring
  have h₂ : |q - v| + v = q := by rw [abs_of_nonneg (by linarith [hq.1])]; ring
  simp only [h₁, h₂]
  ring

end PartialBalayage.Maximal.Square

namespace PartialBalayage.Maximal.Square

theorem bandLine_eq_zero_of_le {u v : ℝ} (hv : supportRadius ≤ v) : bandLine u v = 0 := by
  unfold bandLine
  have h : ∀ s : ℝ, (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsi (|s| + v) = 0 := fun s ↦ by
    rw [bandPsi_eq_zero (by linarith [abs_nonneg s]), mul_zero]
  simp only [h, intervalIntegral.integral_zero]

theorem bandSlopeU_eq_zero_of_le {u v : ℝ} (hv : supportRadius ≤ v) : bandSlopeU u v = 0 := by
  unfold bandSlopeU
  have h : ∀ s : ℝ, (1 + 47 / 40) * (u - s) ^ (-2 - (47 / 40 : ℝ)) * bandPsi (|s| + v) = 0 :=
    fun s ↦ by rw [bandPsi_eq_zero (by linarith [abs_nonneg s]), mul_zero]
  simp only [h, intervalIntegral.integral_zero]

theorem bandSlopeV_eq_zero_of_le {u v : ℝ} (hv : supportRadius ≤ v) : bandSlopeV u v = 0 := by
  unfold bandSlopeV
  have h : ∀ s : ℝ, (47 / 40) * (u - s) ^ (-1 - (47 / 40 : ℝ)) * bandPsiSlope (|s| + v) = 0 :=
    fun s ↦ by
      simp only [bandPsiSlope, mul_ite, mul_zero, ite_eq_right_iff]
      intro h; linarith [abs_nonneg s]
  simp only [h, intervalIntegral.integral_zero]

/-- The far-corner plane, also when the line misses the diamond. -/
theorem bandLine_plane_le' {u u₁ v v₁ : ℝ} (hu : 0 < u) (hv : 0 < v) (hr : supportRadius < u + v)
    (huu : u ≤ u₁) (hvv : v ≤ v₁) :
    bandLine u₁ v₁ + bandSlopeU u₁ v₁ * (u₁ - u) + bandSlopeV u₁ v₁ * (v₁ - v) ≤ bandLine u v := by
  by_cases hvR : v < supportRadius
  · exact bandLine_plane_le hu hv hvR hr huu hvv
  · push_neg at hvR
    rw [bandLine_eq_zero_of_le (hvR.trans hvv), bandSlopeU_eq_zero_of_le (hvR.trans hvv),
      bandSlopeV_eq_zero_of_le (hvR.trans hvv), bandLine_eq_zero_of_le hvR]
    simp

/-- The exterior profile's generator integral is the line integral (all exterior points). -/
theorem stableGeneratorIntegral_profile_eq_bandLine' {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : supportRadius < u + v) :
    stableGeneratorIntegral (47 / 40)
        (diamondCoordinateTruncatedProfile (47 / 40) supportRadius u v) = bandLine u v := by
  by_cases hvR : v < supportRadius
  · exact stableGeneratorIntegral_profile_eq_bandLine hu hv hvR hr
  · push_neg at hvR
    rw [bandLine_eq_zero_of_le hvR]
    have h : diamondCoordinateTruncatedProfile (47 / 40) supportRadius u v = fun _ ↦ 0 := by
      funext s
      have hp := Real.rpow_le_rpow_of_nonpos supportRadius_pos
        (show supportRadius ≤ |u + s| + v by linarith [abs_nonneg (u + s)])
        (by norm_num : -(47 / 40 : ℝ) ≤ 0)
      exact max_eq_right (sub_nonpos.mpr hp)
    rw [h]
    simp [stableGeneratorIntegral, stableSecondDifference]

end PartialBalayage.Maximal.Square
