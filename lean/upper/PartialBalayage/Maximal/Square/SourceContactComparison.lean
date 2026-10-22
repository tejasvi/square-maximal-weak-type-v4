/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.CompensatedSourceState
public import PartialBalayage.Maximal.Square.MollifiedSourceRegularity
public import PartialBalayage.Maximal.Square.MollifiedSourceEquation
public import PartialBalayage.Maximal.Square.TranslationJumpFormLimit
public import PartialBalayage.Maximal.L1KernelL2
public import PartialBalayage.Maximal.SobolevKernelSourceBound

/-!
# Genuine infinite-source contact comparison for the stable obstacle

True compact mollifications give source graph states with uniform energy bounds.
Their actual equations pass to the genuine nonsmooth state. The full source form
then supplies the comparison on the state zero set, without finite source mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure ContinuousLinearMap Filter Set Topology
open PartialBalayage.Linear
open scoped Convolution ENNReal RealInnerProductSpace

namespace PartialBalayage.Maximal.Square

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "L²" => Lp ℝ 2 (volume : Measure E)

/-- The genuine stable weak PDE gives true kernel contact comparison for an infinite source. -/
theorem ae_kernel_convolution_nonneg_on_stable_contact
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {K : E → ℝ}
    (hK : Integrable K volume) (hK0 : ∀ᵐ y ∂volume, 0 ≤ K y)
    (hKeven : ∀ y, K (-y) = K y) (μ : Measure E) [SigmaFinite μ]
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ → Integrable ψ μ)
    (haway : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      0 ∉ tsupport ψ →
        (∫ y, K y * coordinateStableGenerator α ψ y) = ∫ y, ψ y ∂μ)
    (u g : L²) (hu1 : Integrable (u : E → ℝ) volume)
    (hu0 : ∀ᵐ y ∂volume, 0 ≤ u y)
    (hpde : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ y, u y * coordinateStableGenerator α ψ y) = ∫ y, g y * ψ y) :
    ∀ᵐ x ∂volume, u x = 0 → 0 ≤ ∫ y, K (y - x) * g y := by
  have hm := integrable_compensatedJumpMoment_of_punctured_source
    hα0 hα2 hK μ hlocal haway
  let U (k : ℕ) := graphMollifierL2 k u
  let G (k : ℕ) := PartialBalayage.nonnegKernelConvolutionL2 hK hK0 (graphMollifierL2 k g)
  let b := PartialBalayage.nonnegKernelConvolutionL2 hK hK0 g
  have hmoll (a : L²) (k : ℕ) : ‖graphMollifierL2 k a‖ ≤ ‖a‖ :=
    norm_normalized_convolution_toLp_le
      ((graphMollifierBump 2 k).contDiff_normed (n := (⊤ : ℕ∞))).continuous
      (graphMollifierBump 2 k).hasCompactSupport_normed
      (graphMollifierBump 2 k).nonneg_normed (graphMollifierBump 2 k).integral_normed a
  have hsteps (k : ℕ) :
      ∃ hJ : MemLp (translationJump (U k : E → ℝ)) 2 (volume.prod μ),
        (∀ v : L², Integrable (v : E → ℝ) volume →
          MemLp (translationJump (v : E → ℝ)) 2 (volume.prod μ) →
            translationJumpForm μ (U k) v = -(∫ x, G k x * v x)) ∧
        ‖hJ.toLp (translationJump (U k : E → ℝ))‖ ^ 2 ≤ 2 * ‖G k‖ * ‖U k‖ := by
    let ρ := (graphMollifierBump 2 k).normed volume
    let w := ρ ⋆[lsmul ℝ ℝ, volume] u
    have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := (graphMollifierBump 2 k).contDiff_normed
    have hsρ : HasCompactSupport ρ := (graphMollifierBump 2 k).hasCompactSupport_normed
    have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
    have hw : Continuous w := hsρ.continuous_convolution_left (lsmul ℝ ℝ) hρ.continuous
      ((Lp.memLp u).locallyIntegrable (by norm_num))
    have hw1 : Integrable w volume :=
      (hρ.continuous.integrable_of_hasCompactSupport hsρ).integrable_convolution
        (lsmul ℝ ℝ) hu1
    have hw2 : MemLp w 2 volume := (Lp.memLp (U k)).ae_eq (graphMollifierL2_ae k u)
    have hvalue : hw2.toLp w = U k := Lp.ext
      (hw2.coeFn_toLp.trans (graphMollifierL2_ae k u).symm)
    obtain ⟨C, _, hb⟩ := exists_mollified_symmetricSecondDifference_bound u ρ
      (Lp.memLp u) hsρ hρ
    have hsource : compensatedSourceGenerator μ w =
        K ⋆[lsmul ℝ ℝ, volume] (ρ ⋆[lsmul ℝ ℝ, volume] g) := funext
      (compensatedSourceGenerator_mollification_eq_kernel_forcing hα0 hα2 hK hKeven μ
        hlocal haway hu1 hpde hρ2 hsρ)
    have hG : G k =ᵐ[volume] compensatedSourceGenerator μ w := by
      have he := convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl (ae volume) K)
        (graphMollifierL2_ae k g)
      rw [hsource]
      simpa only [G, he] using
        PartialBalayage.nonnegKernelConvolutionL2_ae hK hK0 (graphMollifierL2 k g)
    have h := compensatedSource_state_weak_equation μ hm hw hw1 hw2 hb (G k) hG
    rwa [hvalue] at h
  choose hJ heq henergy using hsteps
  have hmass : 0 ≤ ∫ y, K y := integral_nonneg_of_ae hK0
  let T := (∫ y, K y) * ‖g‖ * ‖u‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hGnorm (k : ℕ) : ‖G k‖ ≤ (∫ y, K y) * ‖g‖ :=
    (PartialBalayage.norm_nonnegKernelConvolutionL2_le hK hK0 _).trans
      (mul_le_mul_of_nonneg_left (hmoll g k) hmass)
  have hdata (k : ℕ) : ‖(hJ k).toLp (translationJump (U k : E → ℝ))‖ ≤ 2 * T + 1 := by
    have hs : ‖(hJ k).toLp (translationJump (U k : E → ℝ))‖ ^ 2 ≤ 2 * T := by
      calc
        _ ≤ 2 * ‖G k‖ * ‖U k‖ := henergy k
        _ ≤ 2 * ((∫ y, K y) * ‖g‖) * ‖u‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hGnorm k) (by norm_num)) (hmoll u k)
            (norm_nonneg _) (by positivity)
        _ = _ := by dsimp [T]; ring
    nlinarith [sq_nonneg (‖(hJ k).toLp (translationJump (U k : E → ℝ))‖ - 1)]
  obtain ⟨huJ, huEq⟩ := translationJumpForm_equation_of_L2_tendsto μ U G u b hJ
    (norm_nonneg u) (by positivity : 0 ≤ 2 * T + 1) (fun k ↦ hmoll u k) hdata
    (tendsto_graphMollifierL2 u)
    (PartialBalayage.tendsto_nonnegKernelConvolutionL2 hK hK0 (tendsto_graphMollifierL2 g))
    heq
  have hcontact := ae_nonneg_on_contact_of_compensatedSource_form μ hm u b hu0 huJ huEq
  have href : (fun z : E ↦ K (-z)) = K := funext hKeven
  filter_upwards [hcontact, PartialBalayage.nonnegKernelConvolutionL2_ae hK hK0 g]
      with x hx hbx
  intro hux
  have hpos := hx hux
  rw [PartialBalayage.kernel_source_pairing_eq_reflected_convolution, href]
  rwa [← hbx]

end PartialBalayage.Maximal.Square
