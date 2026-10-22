/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierEnergySplit
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The genuine isotropic Fourier energy graph

The graph of multiplication of the unitary Fourier transform by the isotropic power weight
is a closed subspace of a two-coordinate Hilbert `L²` product. It therefore gives a complete
energy Hilbert space with an actual continuous value map, in every dimension and for vector
outputs. Closedness follows from common almost-everywhere convergent subsequences.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal

namespace PartialBalayage.Linear

variable {X E : Type*}
variable [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "L²" => Lp E 2 (volume : Measure X)
local notation "H" => PiLp 2 (fun _ : Fin 2 ↦ L²)

/-- The actual Fourier graph for a scalar frequency weight. -/
def weightedFourierGraph (w : X → ℂ) : Submodule ℂ H where
  carrier := {U | ∀ᵐ ξ, U 1 ξ = w ξ • (𝓕 (U 0) : L²) ξ}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := (volume : Measure X))] with ξ hξ
    simp only [PiLp.zero_apply, FourierTransform.fourier_zero, hξ, Pi.zero_apply, smul_zero]
  add_mem' := by
    intro U V hU hV
    change ∀ᵐ ξ, (U + V) 1 ξ = w ξ • (𝓕 ((U + V) 0) : L²) ξ
    simp only [PiLp.add_apply]
    rw [FourierTransform.fourier_add]
    filter_upwards [hU, hV, Lp.coeFn_add (U 1) (V 1),
      Lp.coeFn_add (𝓕 (U 0)) (𝓕 (V 0))] with ξ hUξ hVξ hsum hfsum
    rw [hsum, hfsum, Pi.add_apply, Pi.add_apply, hUξ, hVξ, smul_add]
  smul_mem' := by
    intro c U hU
    change ∀ᵐ ξ, (c • U) 1 ξ = w ξ • (𝓕 ((c • U) 0) : L²) ξ
    simp only [PiLp.smul_apply]
    rw [FourierTransform.fourier_smul]
    filter_upwards [hU, Lp.coeFn_smul c (U 1), Lp.coeFn_smul c (𝓕 (U 0))] with ξ hUξ hc hfc
    rw [hc, hfc, Pi.smul_apply, Pi.smul_apply, hUξ, smul_comm]

/-- Every actual scalar Fourier multiplication graph is strongly closed. -/
theorem isClosed_weightedFourierGraph (w : X → ℂ) :
    IsClosed (weightedFourierGraph (E := E) w : Set H) := by
  apply IsSeqClosed.isClosed
  intro U V hU hUV
  have h0 : Tendsto (fun j ↦ (U j) 0) atTop (𝓝 (V 0)) :=
    (PiLp.continuous_apply 2 _ 0).tendsto V |>.comp hUV
  have h1 : Tendsto (fun j ↦ (U j) 1) atTop (𝓝 (V 1)) :=
    (PiLp.continuous_apply 2 _ 1).tendsto V |>.comp hUV
  have hF : Tendsto (fun j ↦ 𝓕 ((U j) 0)) atTop (𝓝 (𝓕 (V 0))) :=
    (Lp.fourierTransformₗᵢ X E).continuous.tendsto (V 0) |>.comp h0
  obtain ⟨s, hs, hFs⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  obtain ⟨r, hr, h1r⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (h1.comp hs.tendsto_atTop)).exists_seq_tendsto_ae
  change ∀ᵐ ξ, V 1 ξ = w ξ • (𝓕 (V 0) : L²) ξ
  filter_upwards [hFs, h1r, ae_all_iff.mpr (fun j ↦ hU (s (r j)))] with ξ hFξ h1ξ hgraph
  have hmul : Tendsto (fun j ↦ w ξ • (𝓕 ((U (s (r j))) 0) : L²) ξ) atTop
      (𝓝 (w ξ • (𝓕 (V 0) : L²) ξ)) := (hFξ.comp hr.tendsto_atTop).const_smul _
  exact tendsto_nhds_unique h1ξ (hmul.congr' (Eventually.of_forall fun j ↦ (hgraph j).symm))

/-- The actual isotropic power-weight graph; `α=2` is the Laplace energy and `α=1` is
the energy of the isotropic square-root Laplacian. -/
def isotropicEnergyGraph (α : ℝ) : Submodule ℂ H :=
  weightedFourierGraph (fun ξ : X ↦ ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ))

/-- The genuine complete Hilbert energy space, represented by value and weighted Fourier data. -/
abbrev IsotropicEnergySpace (α : ℝ) :=
  ↥(isotropicEnergyGraph (X := X) (E := E) α)

instance (α : ℝ) : CompleteSpace (IsotropicEnergySpace (X := X) (E := E) α) :=
  (isClosed_weightedFourierGraph (E := E)
    (fun ξ : X ↦ ((‖ξ‖ ^ (α / 2) : ℝ) : ℂ))).completeSpace_coe

/-- The actual physical-space value inclusion is continuous and linear. -/
def isotropicEnergyValue (α : ℝ) : IsotropicEnergySpace (X := X) (E := E) α →L[ℂ] L² :=
  PiLp.proj 2 (fun _ : Fin 2 ↦ L²) 0 ∘L (isotropicEnergyGraph α).subtypeL

/-- The actual weighted Fourier coordinate of an energy-space element. -/
def isotropicEnergyData (α : ℝ) : IsotropicEnergySpace (X := X) (E := E) α →L[ℂ] L² :=
  PiLp.proj 2 (fun _ : Fin 2 ↦ L²) 1 ∘L (isotropicEnergyGraph α).subtypeL

theorem isotropicEnergyValue_apply (α : ℝ) (U : IsotropicEnergySpace (X := X) (E := E) α) :
    isotropicEnergyValue α U = (U : H) 0 := rfl

theorem isotropicEnergyData_apply (α : ℝ) (U : IsotropicEnergySpace (X := X) (E := E) α) :
    isotropicEnergyData α U = (U : H) 1 := rfl

/-- The graph norm is exactly the physical `L²` norm plus the isotropic energy coordinate. -/
theorem isotropicEnergy_norm_sq (α : ℝ) (U : IsotropicEnergySpace (X := X) (E := E) α) :
    ‖U‖ ^ 2 = ‖isotropicEnergyValue α U‖ ^ 2 + ‖isotropicEnergyData α U‖ ^ 2 := by
  change ‖(U : H)‖ ^ 2 = ‖(U : H) 0‖ ^ 2 + ‖(U : H) 1‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

/-- The weighted coordinate represents the genuine full isotropic energy. -/
theorem isotropicEnergyData_enorm_sq (α : ℝ)
    (U : IsotropicEnergySpace (X := X) (E := E) α) :
    ‖isotropicEnergyData α U‖ₑ ^ (2 : ℕ) =
      fourierEnergy α (isotropicEnergyValue α U) := by
  have he : ‖isotropicEnergyData α U‖ₑ ^ (2 : ℕ) =
      ∫⁻ ξ, ‖isotropicEnergyData α U ξ‖ₑ ^ (2 : ℕ) := by
    rw [Lp.enorm_def]
    simpa [ENNReal.rpow_two] using
      eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
        (Lp.aestronglyMeasurable (isotropicEnergyData α U))
  rw [he, fourierEnergy]
  apply lintegral_congr_ae
  filter_upwards [U.property] with ξ hξ
  change ‖(U : H) 1 ξ‖ₑ ^ (2 : ℕ) =
    ENNReal.ofReal (‖ξ‖ ^ α) * ‖(𝓕 ((U : H) 0) : L²) ξ‖ₑ ^ (2 : ℕ)
  rw [hξ, enorm_smul, mul_pow]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg ξ) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
  congr 1
  congr 1
  norm_num

/-- Finite actual isotropic energy is built into the energy graph, rather than assumed. -/
theorem fourierEnergy_ne_top (α : ℝ) (U : IsotropicEnergySpace (X := X) (E := E) α) :
    fourierEnergy α (isotropicEnergyValue α U) ≠ ⊤ := by
  rw [← isotropicEnergyData_enorm_sq]
  exact ENNReal.pow_ne_top enorm_ne_top

end PartialBalayage.Linear
