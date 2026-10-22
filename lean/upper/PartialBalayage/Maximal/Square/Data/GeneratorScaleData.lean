/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: our kernel's scale factors: R^(-47/20) with R = 33/20 (20th-power checks),
32^(47/40) (40th-power checks) and the spline factor 1/(a(a-1)(2-a)(3-a)) = 2560000/792561 at a = 47/40. -/
module

public import PartialBalayage.Maximal.Square.RationalInterval
public import PartialBalayage.Maximal.Square.Kernel
public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Exact rational generator scale enclosures

The literal endpoints are candidate root bounds. Their integer-power checks
are proved by ordinary Lean kernel reduction before being connected to the actual
radial and spline scale factors.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Candidate enclosure of the actual incoming-tail radius factor `R^(-47/20)`. -/
def generatorRadiusInterval : RationalInterval := ⟨
  (390761976381628285061141321209 / 1267650600228229401496703205376 : ℚ),
  (195380988190814142530570660605 / 633825300114114700748351602688 : ℚ)⟩

/-- Both endpoints enclose the actual 20th-root power by exact rational arithmetic. -/
theorem generatorRadiusInterval_valid :
    IsPowerEnclosureDeg 20 (33 / 20) (-47) generatorRadiusInterval.lower
      generatorRadiusInterval.upper := by
  unfold IsPowerEnclosureDeg generatorRadiusInterval
  decide +kernel

/-- Candidate enclosure of the actual inverse mesh power `32^(47/40)`. -/
def generatorMeshInterval : RationalInterval := ⟨
  (74396206449927340395078312447425 / 1267650600228229401496703205376 : ℚ),
  (37198103224963670197539156223713 / 633825300114114700748351602688 : ℚ)⟩

/-- Both inverse-mesh endpoints pass the exact rational 40th-power checks. -/
theorem generatorMeshInterval_valid :
    IsPowerEnclosureDeg 40 (1 / 32) (-47) generatorMeshInterval.lower
      generatorMeshInterval.upper := by
  unfold IsPowerEnclosureDeg generatorMeshInterval
  decide +kernel

/-- The actual positive spline generator prefactor. -/
def splineGeneratorFactor : ℝ := (2560000 / 792561 : ℝ) * (32 : ℝ) ^ (47 / 40 : ℝ)

/-- The exact rational interval obtained by genuine positive scalar multiplication. -/
def splineGeneratorFactorInterval : RationalInterval :=
  generatorMeshInterval.scale (2560000 / 792561)

theorem generatorRadiusInterval_contains :
    generatorRadiusInterval.Contains (supportRadius ^ (-47 / 20 : ℝ)) := by
  have h := generatorRadiusInterval_valid.rpow_bounds (by norm_num) (by norm_num : (0 : ℚ) ≤ 33 / 20)
  have hc : (((-47 : ℤ) : ℝ) / ((20 : ℕ) : ℝ)) = -47 / 20 := by norm_num
  rw [hc] at h
  simpa only [RationalInterval.Contains, supportRadius, Rat.cast_div, Rat.cast_ofNat] using h

theorem splineGeneratorFactorInterval_contains :
    splineGeneratorFactorInterval.Contains splineGeneratorFactor := by
  have h : generatorMeshInterval.Contains ((1 / 32 : ℝ) ^ (-47 / 40 : ℝ)) := by
    have hp := generatorMeshInterval_valid.rpow_bounds (by norm_num) (by norm_num : (0 : ℚ) ≤ 1 / 32)
    have hc : (((-47 : ℤ) : ℝ) / ((40 : ℕ) : ℝ)) = -47 / 40 := by norm_num
    rw [hc] at hp
    simpa only [RationalInterval.Contains, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hp
  have hscale := h.scale (2560000 / 792561)
  have he : (1 / 32 : ℝ) ^ (-47 / 40 : ℝ) = (32 : ℝ) ^ (47 / 40 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  simpa only [splineGeneratorFactorInterval, splineGeneratorFactor, Rat.cast_div,
    Rat.cast_ofNat, he] using hscale

theorem splineGeneratorFactorInterval_lower_nonneg : 0 ≤ splineGeneratorFactorInterval.lower := by
  unfold splineGeneratorFactorInterval RationalInterval.scale generatorMeshInterval
  norm_num

theorem splineGeneratorFactor_nonneg : 0 ≤ splineGeneratorFactor := by
  unfold splineGeneratorFactor
  positivity

end PartialBalayage.Maximal.Square
