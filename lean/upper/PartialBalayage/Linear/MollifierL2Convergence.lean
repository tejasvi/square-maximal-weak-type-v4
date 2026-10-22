/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.MollifierL2
public import CenteredMaximal.Ball.DirichletSmoothComposition
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Genuine strong `L²` approximation by compact smooth mollifiers

The explicit normalized bump sequence converges strongly on continuous functions of compact
support, by dominated convergence on a common compact support. The contraction estimate and
the existing compact smooth density theorem then give convergence for every actual `L²` class.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Filter Metric Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped Convolution RealInnerProductSpace ENNReal Topology Pointwise Classical

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- An explicit compact smooth approximate identity with outer radius `1/(n+1)`. -/
def graphMollifierBump (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨(1 / (n + 1 : ℝ)) / 2, 1 / (n + 1 : ℝ), by positivity,
    half_lt_self (by positivity)⟩

theorem graphMollifierBump_rOut_le (n : ℕ) : (graphMollifierBump d n).rOut ≤ 1 := by
  dsimp [graphMollifierBump]
  apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
  exact_mod_cast Nat.le_add_left 1 n

theorem graphMollifierBump_rOut_tendsto :
    Tendsto (fun n ↦ (graphMollifierBump d n).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifierBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The explicit normalized mollifier as an actual bounded scalar `L²` operator. -/
def graphMollifierL2 (n : ℕ)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  normalizedConvolutionL2 ((graphMollifierBump d n).contDiff_normed (n := (⊤ : ℕ∞))).continuous
    (graphMollifierBump d n).hasCompactSupport_normed
    (graphMollifierBump d n).nonneg_normed (graphMollifierBump d n).integral_normed a

theorem graphMollifierL2_ae (n : ℕ)
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    graphMollifierL2 n a =ᵐ[volume] (graphMollifierBump d n).normed volume ⋆ a := by
  unfold graphMollifierL2
  exact normalizedConvolutionL2_ae _ _ _ _ a

theorem dist_graphMollifierL2_le (n : ℕ)
    (a b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    dist (graphMollifierL2 n a) (graphMollifierL2 n b) ≤ dist a b :=
  dist_normalizedConvolutionL2_le _ _ _ _ a b

/-- Compact continuous inputs converge strongly under the actual bump-convolution operators. -/
theorem tendsto_graphMollifierL2_of_compact_continuous
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun n ↦ graphMollifierL2 n ((hg.memLp_of_hasCompactSupport hgc).toLp g))
      atTop (𝓝 ((hg.memLp_of_hasCompactSupport hgc).toLp g)) := by
  let gm := hg.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgc
  let G := gm.toLp g
  let w (n : ℕ) := (graphMollifierBump d n).normed volume ⋆ g
  let K := tsupport g + closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hK : IsCompact K := hgc.isCompact.add (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  have hwpoint (x : EuclideanSpace ℝ (Fin d)) :
      Tendsto (fun n ↦ w n x) atTop (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous graphMollifierBump_rOut_tendsto hg x
  have hwsupp (n : ℕ) : Function.support (w n) ⊆ K := by
    refine (support_convolution_subset_swap (lsmul ℝ ℝ)).trans (add_subset_add
      (subset_tsupport g) ?_)
    rw [(graphMollifierBump d n).support_normed_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (graphMollifierBump_rOut_le n))
  have hgsupp : Function.support g ⊆ K := by
    intro x hx
    simpa only [add_zero] using add_mem_add (subset_tsupport g hx)
      (show (0 : EuclideanSpace ℝ (Fin d)) ∈ closedBall 0 1 by simp)
  have hwbound (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ‖w n x‖ ≤ C := by
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ)) hC0
      (graphMollifierBump d n).support_normed_eq.subset
      (graphMollifierBump d n).nonneg_normed (graphMollifierBump d n).integral_normed
      hg.aestronglyMeasurable (fun y _ ↦ by simpa only [dist_zero_right] using hC y)
    simpa only [dist_zero_right, w] using h
  have hB : MemLp (K.indicator (fun _ ↦ 2 * C)) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet (2 * C) (Or.inr hK.measure_lt_top.ne)
  have ht : Tendsto (fun n ↦ eLpNorm (fun x ↦ w n x - g x) 2 volume) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated volume hB
    · intro n
      exact ((graphMollifierBump d n).hasCompactSupport_normed.continuous_convolution_left
        (L := lsmul ℝ ℝ)
        ((graphMollifierBump d n).contDiff_normed (n := (⊤ : ℕ∞))).continuous
        (gm.locallyIntegrable (by norm_num))).aestronglyMeasurable.sub hg.aestronglyMeasurable
    · intro n x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * C)]
        exact (norm_sub_le _ _).trans (by linarith [hwbound n x, hC x])
      · have hw0 : w n x = 0 := Function.notMem_support.mp (fun hw ↦ hx (hwsupp n hw))
        have hg0 : g x = 0 := Function.notMem_support.mp (fun hgx ↦ hx (hgsupp hgx))
        simp only [hw0, hg0, sub_zero, norm_zero, Set.indicator_of_notMem hx]
        exact le_rfl
    · filter_upwards with x
      simpa only [sub_self] using (hwpoint x).sub_const (g x)
  have hae (n : ℕ) : graphMollifierL2 n G =ᵐ[volume] w n := by
    have hc : (graphMollifierBump d n).normed volume ⋆ G = w n :=
      convolution_congr (lsmul ℝ ℝ)
        (Filter.EventuallyEq.refl (ae volume) ((graphMollifierBump d n).normed volume))
        gm.coeFn_toLp
    rw [← hc]
    exact graphMollifierL2_ae n G
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n ↦ graphMollifierL2 n G) G).mpr
  convert! ht using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [hae n, gm.coeFn_toLp] with x hx hgx
  simp only [Pi.sub_apply, hx, G, hgx]

/-- Every genuine scalar real `L²` class is strongly approximated by the explicit mollifiers. -/
theorem tendsto_graphMollifierL2
    (a : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Tendsto (fun n ↦ graphMollifierL2 n a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, hgc, hgs, hga⟩ := MemLp.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp a) (by positivity : 0 < ε / 4)
  let gm := hgs.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgc
  let G := gm.toLp g
  have hag : dist a G ≤ ε / 4 := by
    rw [Lp.dist_def]
    have hfun : (a : _ → ℝ) - (G : _ → ℝ) =ᵐ[volume] (a : _ → ℝ) - g := by
      filter_upwards [gm.coeFn_toLp] with x hx
      simp only [G, hx, Pi.sub_apply]
    rw [eLpNorm_congr_ae hfun]
    exact (ENNReal.toReal_mono (by finiteness) hga).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have ht := tendsto_graphMollifierL2_of_compact_continuous hgs.continuous hgc
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hdist := dist_triangle4 (graphMollifierL2 n a) (graphMollifierL2 n G) G a
  have hcontract := dist_graphMollifierL2_le n a G
  have hnear : dist (graphMollifierL2 n G) G < ε / 2 := hN n hn
  rw [dist_comm G a] at hdist
  nlinarith

end PartialBalayage.Linear
