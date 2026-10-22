/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the kernel majorization facts enter as the instance argument [KernelMajorizationFacts]. -/
module

public import PartialBalayage.Maximal.Square.DilatedKernelSource
public import PartialBalayage.Maximal.Square.DiamondStripVolume
public import PartialBalayage.Maximal.Square.KernelMajorization
public import PartialBalayage.Maximal.Square.Integrability
public import PartialBalayage.Maximal.KernelContactCap

/-!
# Actual diamond averages bounded by the genuine kernel cap

The original closed-diamond indicator is dominated by the real dilated
kernel. The actual planar normalization cancels its radius-squared mass.
True source contact comparisons therefore give the exact half-kernel mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The genuine closed Euclidean diamond averaging region. -/
def closedEuclideanDiamond (x : E) (r : ℝ) : Set E :=
  {y | diamondRadius (y 0 - x 0) (y 1 - x 1) ≤ r}

theorem measurableSet_closedEuclideanDiamond (x : E) (r : ℝ) :
    MeasurableSet (closedEuclideanDiamond x r) := by
  apply IsClosed.measurableSet
  exact isClosed_le (by unfold diamondRadius; fun_prop) continuous_const

/-- The actual planar diamond area, valid at every center. -/
theorem volume_closedEuclideanDiamond (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedEuclideanDiamond x r) = ENNReal.ofReal (2 * r ^ 2) := by
  have hs : MeasurableSet {z : E | diamondRadius (z 0) (z 1) ≤ r} := by
    apply IsClosed.measurableSet
    exact isClosed_le (by unfold diamondRadius; fun_prop) continuous_const
  have he := (measurePreserving_sub_right volume x).measure_preimage hs.nullMeasurableSet
  change volume (closedEuclideanDiamond x r) = _ at he
  exact he.trans (volume_euclidean_diamond_closed hr)

/-- The genuine unnormalized averaging indicator. -/
def euclideanDiamondIndicator (r : ℝ) : E → ℝ :=
  (closedEuclideanDiamond 0 r).indicator (fun _ ↦ (1 : ℝ))

theorem integrable_euclideanDiamondIndicator {r : ℝ} (hr : 0 ≤ r) :
    Integrable (euclideanDiamondIndicator r) volume := by
  apply (integrable_indicator_iff (measurableSet_closedEuclideanDiamond 0 r)).mpr
  exact integrableOn_const (by
    rw [volume_closedEuclideanDiamond 0 hr]
    exact ENNReal.ofReal_ne_top)

theorem euclideanDiamondIndicator_nonneg (r : ℝ) (x : E) :
    0 ≤ euclideanDiamondIndicator r x := by
  classical
  simp only [euclideanDiamondIndicator, indicator_apply]
  split_ifs <;> norm_num

theorem diamondRadius_inv_smul {r : ℝ} (hr : 0 < r) (x : E) :
    diamondRadius ((r⁻¹ • x) 0) ((r⁻¹ • x) 1) = diamondRadius (x 0) (x 1) / r := by
  change |r⁻¹ * x 0| + |r⁻¹ * x 1| = (|x 0| + |x 1|) / r
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  ring

/-- The actual averaging indicator is dominated by the genuine dilated square kernel. -/
theorem euclideanDiamondIndicator_le_dilatedKernel [KernelMajorizationFacts] {r : ℝ} (hr : 0 < r) (x : E) :
    euclideanDiamondIndicator r x ≤ dilatedComparisonKernel r euclideanKernel x := by
  classical
  unfold euclideanDiamondIndicator
  by_cases hx : x ∈ closedEuclideanDiamond 0 r
  · rw [indicator_of_mem hx]
    apply one_le_euclideanKernel_of_diamond
    have hx' : diamondRadius (x 0) (x 1) ≤ r := by
      simpa only [closedEuclideanDiamond, mem_ofPred_eq, PiLp.zero_apply, sub_zero] using hx
    change diamondRadius ((r⁻¹ • x) 0) ((r⁻¹ • x) 1) ≤ 1
    rw [diamondRadius_inv_smul hr]
    exact (div_le_one hr).mpr hx'
  · rw [indicator_of_notMem hx]
    exact euclideanKernel_nonneg _

/-- The genuine translated indicator pairing is exactly the original region integral. -/
theorem integral_euclideanDiamondIndicator_pairing (f : E → ℝ) (x : E) (r : ℝ) :
    (∫ y, euclideanDiamondIndicator r (y - x) * f y) =
      ∫ y in closedEuclideanDiamond x r, f y := by
  rw [← integral_indicator (measurableSet_closedEuclideanDiamond x r)]
  apply integral_congr_ae
  filter_upwards with y
  classical
  have hy : y - x ∈ closedEuclideanDiamond 0 r ↔ y ∈ closedEuclideanDiamond x r := by
    simp only [closedEuclideanDiamond, mem_ofPred_eq, PiLp.zero_apply, sub_zero]
    rfl
  simp only [euclideanDiamondIndicator, indicator_apply, hy]
  split_ifs <;> simp

/-- Actual contact and the density cap bound every true diamond average by half the kernel mass. -/
theorem ae_diamondAverage_le_half_kernel_mass [KernelMajorizationFacts] (f ν : E → ℝ)
    (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume) (hf₀ : ∀ᵐ y, 0 ≤ f y)
    (κ : ℝ) (hcap : ∀ᵐ y, ν y ≤ κ) (P : E → Prop) {r : ℝ} (hr : 0 < r)
    (hcontact : ∀ᵐ x, P x → 0 ≤
      ∫ y, dilatedComparisonKernel r euclideanKernel (y - x) * (ν y - f y)) :
    ∀ᵐ x, P x → (2 * r ^ 2)⁻¹ * (∫ y in closedEuclideanDiamond x r, f y) ≤
      κ * ((∫ y, euclideanKernel y) / 2) := by
  have h := ae_kernel_source_pairing_le_cap (euclideanDiamondIndicator r)
    (dilatedComparisonKernel r euclideanKernel) (integrable_euclideanDiamondIndicator hr.le)
    (Filter.Eventually.of_forall (euclideanDiamondIndicator_nonneg r))
    (integrable_dilatedComparisonKernel integrable_euclideanKernel hr)
    (Filter.Eventually.of_forall (fun x ↦ euclideanKernel_nonneg (r⁻¹ • x)))
    (Filter.Eventually.of_forall (euclideanDiamondIndicator_le_dilatedKernel hr))
    f ν hf hν hf₀ κ hcap P hcontact
  filter_upwards [h] with x hx
  intro hP
  have hb := hx hP
  rw [integral_euclideanDiamondIndicator_pairing,
    integral_dilatedComparisonKernel euclideanKernel hr] at hb
  calc
    _ ≤ (2 * r ^ 2)⁻¹ * (κ * (r ^ 2 * ∫ y, euclideanKernel y)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

end PartialBalayage.Maximal.Square
