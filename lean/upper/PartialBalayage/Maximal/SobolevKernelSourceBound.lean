/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.L1KernelL2
public import PartialBalayage.Maximal.L2MollifiedSource
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Genuine Sobolev transfer of integrable kernel source bounds

The actual positive graph mollifications satisfy the kernel comparison. Strong L² convergence
and the genuine L¹-kernel convolution operator pass the comparison to the original state using
the closed order on L², which itself is established through almost everywhere subsequences.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Filter Set Topology
open CenteredMaximal.Ball
open scoped Convolution ENNReal

namespace PartialBalayage

variable {n : ℕ}

/-- Source pairings use the reflected actual kernel in the usual convolution convention. -/
theorem kernel_source_pairing_eq_reflected_convolution
    (K f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y, K (y - x) * f y) = ((fun z ↦ K (-z)) ⋆[lsmul ℝ ℝ, volume] f) x := by
  rw [convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards with y
  simp only [neg_sub, smul_eq_mul]

/-- The original L² forcing has genuine integrable source pairings almost everywhere. -/
theorem ae_integrable_kernel_source_pairing
    {K f : EuclideanSpace ℝ (Fin n) → ℝ} (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, Integrable (fun y ↦ K (y - x) * f y) := by
  have hKr : Integrable (fun z ↦ K (-z)) := hK.comp_neg
  have hKr0 : ∀ᵐ z ∂volume, 0 ≤ K (-z) :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae.eventually hK0
  filter_upwards [ae_convolution_exists_of_nonneg_L1_L2 hKr hKr0 hf] with x hx
  simpa only [lsmul_apply, neg_sub, smul_eq_mul] using hx.integrable_swap

/-- Actual nonnegative L² distributional states satisfy the original kernel source inequality. -/
theorem integrable_kernel_source_bound_of_L2_distribution
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, -(C * u x) ≤ ∫ y, K (y - x) * g y := by
  let Kr := fun z : EuclideanSpace ℝ (Fin n) ↦ K (-z)
  have hKr : Integrable Kr := hK.comp_neg
  have hKr0 : ∀ᵐ z ∂volume, 0 ≤ Kr z :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae.eventually hK0
  have hineq (k : ℕ) : (-C) • Linear.graphMollifierL2 k u ≤
      nonnegKernelConvolutionL2 hKr hKr0 (Linear.graphMollifierL2 k g) := by
    apply (Lp.coeFn_le _ _).mp
    have hconv : Kr ⋆[lsmul ℝ ℝ, volume] Linear.graphMollifierL2 k g =
        Kr ⋆[lsmul ℝ ℝ, volume]
          ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] g) :=
      convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl (ae volume) Kr)
        (Linear.graphMollifierL2_ae k g)
    filter_upwards [Lp.coeFn_smul (-C) (Linear.graphMollifierL2 k u),
      Linear.graphMollifierL2_ae k u,
      nonnegKernelConvolutionL2_ae hKr hKr0 (Linear.graphMollifierL2 k g)] with x hl hu hr
    rw [hl, hr, hconv]
    simp only [Pi.smul_apply, hu, smul_eq_mul, neg_mul]
    change -(C * ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x) ≤
      ((fun z ↦ K (-z)) ⋆[lsmul ℝ ℝ, volume]
        ((Linear.graphMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] g)) x
    rw [← kernel_source_pairing_eq_reflected_convolution]
    exact graphMollifier_kernel_source_bound k K hK C hsource u g hu0 hΔ x
  have hleft : Tendsto (fun k ↦ (-C) • Linear.graphMollifierL2 k u) atTop (𝓝 ((-C) • u)) :=
    tendsto_const_nhds.smul (Linear.tendsto_graphMollifierL2 u)
  have hright := tendsto_nonnegKernelConvolutionL2 hKr hKr0
    (Linear.tendsto_graphMollifierL2 g)
  have hlimit := le_of_tendsto_of_tendsto' hleft hright hineq
  have hae := (Lp.coeFn_le ((-C) • u) (nonnegKernelConvolutionL2 hKr hKr0 g)).mpr hlimit
  filter_upwards [hae, Lp.coeFn_smul (-C) u, nonnegKernelConvolutionL2_ae hKr hKr0 g]
    with x hx hl hr
  rw [hl, hr] at hx
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul] at hx
  rw [kernel_source_pairing_eq_reflected_convolution]
  exact hx

/-- Contact with the zero obstacle gives an actual nonnegative forcing pairing a.e. -/
theorem integrable_kernel_pairing_nonneg_on_L2_contact
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y) (C : ℝ)
    (hsource : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 v →
      HasCompactSupport v → (∀ y, 0 ≤ v y) →
        -(C * v 0) ≤ ∫ y, K y * Laplacian.laplacian v y)
    (u g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y) (hΔ : HasLocalDistributionalLaplacian n univ u g) :
    ∀ᵐ x ∂volume, Integrable (fun y ↦ K (y - x) * g y) ∧
      (u x = 0 → 0 ≤ ∫ y, K (y - x) * g y) := by
  filter_upwards [ae_integrable_kernel_source_pairing hK hK0 (Lp.memLp g),
    integrable_kernel_source_bound_of_L2_distribution K hK hK0 C hsource u g hu0 hΔ]
    with x hint hbound
  refine ⟨hint, fun hx ↦ ?_⟩
  simpa only [hx, mul_zero, neg_zero] using hbound

end PartialBalayage
