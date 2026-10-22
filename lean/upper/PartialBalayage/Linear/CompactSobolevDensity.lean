/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.MollifierL2Convergence
public import CenteredMaximal.Ball.LocalMollifierLaplacian

/-!
# Compact weak derivative graphs belong to the genuine Sobolev closure

The actual compact smooth mollifiers approximate both a value and its represented weak
derivatives strongly in `L²`. Integration by parts identifies the classical derivatives of
the mollified values, so their test graphs converge in the ambient Hilbert space.
-/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Filter Metric Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped Convolution RealInnerProductSpace ENNReal Topology Pointwise Classical

namespace PartialBalayage.Linear

variable {d : ℕ}

/-- The derivative of a reflected smooth kernel has the expected minus sign. -/
theorem partialD_comp_const_sub {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    partialD i (fun z ↦ ρ (x - z)) y = -partialD i ρ (x - y) := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
  have hc := ((hρ.differentiable (by simp) (x - y)).hasFDerivAt).comp y hsub
  simp only [Function.comp_def] at hc
  rw [partialD, hc.fderiv, partialD]
  simp

/-- A compactly supported actual `L²` function is globally integrable. -/
theorem integrable_of_memLp_two_compact_support
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : MemLp a 2 volume)
    (has : HasCompactSupport a) : Integrable a volume :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport a)).mp
    ((ha.locallyIntegrable (by norm_num)).integrableOn_isCompact has.isCompact)

/-- Genuine weak integration by parts identifies every classical mollified derivative. -/
theorem partialD_convolution_eq_of_weak_derivative
    {a b ρ : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Integrable a volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : HasCompactSupport ρ) (i : Fin d)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ →
      (∫ y, a y * partialD i φ y) = -(∫ y, b y * φ y)) :
    partialD i (ρ ⋆ a) = ρ ⋆ b := by
  funext x
  have htest : IsTestFn Set.univ (fun y ↦ ρ (x - y)) :=
    ⟨by fun_prop, by
      simpa [Function.comp_def, Homeomorph.subLeft, Equiv.subLeft] using
        hρs.comp_homeomorph (Homeomorph.subLeft x), subset_univ _⟩
  have h := hweak (fun y ↦ ρ (x - y)) htest
  have heq : (fun y ↦ a y * partialD i (fun z ↦ ρ (x - z)) y) =
      (fun y ↦ -(a y * partialD i ρ (x - y))) := by
    funext y
    simp only [partialD_comp_const_sub hρ, mul_neg]
  rw [heq, integral_neg] at h
  have h' : (∫ y, a y * partialD i ρ (x - y)) = (∫ y, b y * ρ (x - y)) :=
    neg_injective h
  rw [CenteredMaximal.Ball.partialD_convolution_left a ρ ha hρs hρ i x,
    convolution_lsmul_swap, convolution_lsmul_swap]
  simpa only [smul_eq_mul, mul_comm] using h'

/-- The concrete mollified functions converge strongly, before taking their `L²` classes. -/
theorem tendsto_eLpNorm_graphMollifier_sub
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : MemLp a 2 volume) :
    Tendsto (fun n ↦ eLpNorm ((graphMollifierBump d n).normed volume ⋆ a - a) 2 volume)
      atTop (𝓝 0) := by
  let A := ha.toLp a
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n ↦ graphMollifierL2 n A) A).mp (tendsto_graphMollifierL2 A)
  convert! ht using 1
  funext n
  have hc : (graphMollifierBump d n).normed volume ⋆ A =
      (graphMollifierBump d n).normed volume ⋆ a :=
    convolution_congr (lsmul ℝ ℝ)
      (Filter.EventuallyEq.refl (ae volume) ((graphMollifierBump d n).normed volume))
      ha.coeFn_toLp
  apply eLpNorm_congr_ae
  filter_upwards [graphMollifierL2_ae n A, ha.coeFn_toLp] with x hx hax
  simp only [Pi.sub_apply, hx, hc, A, hax]

/-- Compact represented weak derivatives generate an actual `H01` graph on the whole space. -/
theorem exists_H01_univ_of_compact_weak_derivatives
    {a : EuclideanSpace ℝ (Fin d) → ℝ}
    {b : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : MemLp a 2 volume) (hb : ∀ i, MemLp (b i) 2 volume)
    (has : HasCompactSupport a)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ → ∀ i,
      (∫ y, a y * partialD i φ y) = -(∫ y, b i y * φ y)) :
    ∃ V : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))),
      ((V : H1amb Set.univ) 0) =ᵐ[volume] a ∧
      ∀ i, ((V : H1amb Set.univ) i.succ) =ᵐ[volume] b i := by
  let θ (n : ℕ) := (graphMollifierBump d n).normed volume ⋆ a
  have hθ (n : ℕ) : IsTestFn Set.univ (θ n) := by
    refine ⟨(graphMollifierBump d n).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) ((graphMollifierBump d n).contDiff_normed (n := (⊤ : ℕ∞)))
      (ha.locallyIntegrable (by norm_num)), ?_, subset_univ _⟩
    exact (graphMollifierBump d n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) has
  have hθi (n : ℕ) (i : Fin d) : partialD i (θ n) =
      (graphMollifierBump d n).normed volume ⋆ b i :=
    partialD_convolution_eq_of_weak_derivative
      (integrable_of_memLp_two_compact_support ha has)
      ((graphMollifierBump d n).contDiff_normed (n := (⊤ : ℕ∞)))
      (graphMollifierBump d n).hasCompactSupport_normed i
      (fun φ hφ ↦ hweak φ hφ i)
  have har : MemLp a 2 (volume.restrict Set.univ) := by simpa only [Measure.restrict_univ]
    using ha
  have hbr (i : Fin d) : MemLp (b i) 2 (volume.restrict Set.univ) := by
    simpa only [Measure.restrict_univ] using hb i
  let V : H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    WithLp.toLp 2 (Fin.cons (har.toLp a) (fun i ↦ (hbr i).toLp (b i)))
  have hθ0t : Tendsto (fun n ↦ (hθ n).testCls) atTop (𝓝 (har.toLp a)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' θ (fun n ↦ (hθ n).mem_lp) a har).mpr
    simpa only [Measure.restrict_univ] using tendsto_eLpNorm_graphMollifier_sub ha
  have hθit (i : Fin d) :
      Tendsto (fun n ↦ (hθ n).partialCls i) atTop (𝓝 ((hbr i).toLp (b i))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ partialD i (θ n))
      (fun n ↦ (hθ n).memLp_partialD i) (b i) (hbr i)).mpr
    simp_rw [hθi]
    simpa only [Measure.restrict_univ] using tendsto_eLpNorm_graphMollifier_sub (hb i)
  have hV : V ∈ H01 Set.univ := by
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) ?_
      (Eventually.of_forall fun n ↦
        (Submodule.span ℝ (testGraphSet Set.univ)).le_topologicalClosure
          (Submodule.subset_span ⟨θ n, hθ n, rfl⟩))
    have hgraph : (fun n ↦ (hθ n).testGraph) =
        fun n ↦ WithLp.toLp 2 (Fin.cons (hθ n).testCls (fun i ↦ (hθ n).partialCls i)) := rfl
    rw [hgraph]
    refine ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) ↦ L2D Set.univ).tendsto _).comp
      (tendsto_pi_nhds.mpr fun j ↦ ?_)
    induction j using Fin.cases with
    | zero => simpa only [Fin.cons_zero, V, PiLp.toLp_apply] using hθ0t
    | succ i => simpa only [Fin.cons_succ, V, PiLp.toLp_apply] using hθit i
  refine ⟨⟨V, hV⟩, ?_, fun i ↦ ?_⟩
  · simpa only [V, PiLp.toLp_apply, Fin.cons_zero, Measure.restrict_univ]
      using har.coeFn_toLp
  · simpa only [V, PiLp.toLp_apply, Fin.cons_succ, Measure.restrict_univ]
      using (hbr i).coeFn_toLp

/-- The whole-space graph constraints are the actual weak gradient integral identities. -/
theorem weak_gradient_integral_of_mem_W12_univ
    {U : H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d)))} (hU : U ∈ W12 Set.univ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn Set.univ φ) (i : Fin d) :
    (∫ x, U 0 x * partialD i φ x) = -(∫ x, U i.succ x * φ x) := by
  have hw := (mem_W12_iff U).mp hU φ hφ i
  rw [L2.inner_def, L2.inner_def] at hw
  simp only [Measure.restrict_univ] at hw
  have heqa : (∫ x, inner ℝ (hφ.partialCls i x) (U 0 x)) =
      ∫ x, U 0 x * partialD i φ x := by
    apply integral_congr_ae
    have hae : hφ.partialCls i =ᵐ[volume] partialD i φ := by
      simpa only [IsTestFn.partialCls, Measure.restrict_univ] using
        (hφ.memLp_partialD i).coeFn_toLp
    filter_upwards [hae] with x hx
    simp only [Real.inner_apply, hx, mul_comm]
  have heqb : (∫ x, inner ℝ (hφ.testCls x) (U i.succ x)) =
      ∫ x, U i.succ x * φ x := by
    apply integral_congr_ae
    have hae : hφ.testCls =ᵐ[volume] φ := by
      simpa only [IsTestFn.testCls, Measure.restrict_univ] using hφ.mem_lp.coeFn_toLp
    filter_upwards [hae] with x hx
    simp only [Real.inner_apply, hx, mul_comm]
  rw [heqa, heqb] at hw
  linarith

/-- Restriction to a compact set supplies an actual compact representative. -/
theorem hasCompactSupport_indicator_of_isCompact
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (a : EuclideanSpace ℝ (Fin d) → ℝ) : HasCompactSupport (K.indicator a) := by
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  exact hx (Set.indicator_of_notMem hxK a)

/-- A genuine whole-space weak derivative graph with a compact value representative belongs
to the genuine test-function closure. No compactness of its derivative representatives is needed. -/
theorem mem_H01_univ_of_compact_weak_graph
    {U : H1amb (Set.univ : Set (EuclideanSpace ℝ (Fin d)))} (hU : U ∈ W12 Set.univ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hzero : ∀ᵐ x ∂volume, x ∉ K → U 0 x = 0) : U ∈ H01 Set.univ := by
  let a := K.indicator (U 0)
  have hUlp (j : Fin (d + 1)) : MemLp (U j) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (U j)
  have ha : MemLp a 2 volume := (hUlp 0).indicator hK.measurableSet
  have hae : a =ᵐ[volume] U 0 := by
    filter_upwards [hzero] with x hx
    by_cases hxK : x ∈ K
    · exact Set.indicator_of_mem hxK (U 0)
    · simp only [a, Set.indicator_of_notMem hxK, hx hxK]
  have hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ → ∀ i,
      (∫ x, a x * partialD i φ x) = -(∫ x, U i.succ x * φ x) := by
    intro φ hφ i
    rw [← weak_gradient_integral_of_mem_W12_univ hU hφ i]
    exact integral_congr_ae (hae.fun_mul (Filter.EventuallyEq.refl (ae volume) (partialD i φ)))
  obtain ⟨V, hV0, hVi⟩ := exists_H01_univ_of_compact_weak_derivatives ha
    (fun i ↦ hUlp i.succ) (hasCompactSupport_indicator_of_isCompact hK (U 0)) hweak
  have hVU : (V : H1amb Set.univ) = U := by
    apply PiLp.ext
    intro j
    apply Lp.ext
    simp only [Measure.restrict_univ]
    induction j using Fin.cases with
    | zero => exact hV0.trans hae
    | succ i => exact hVi i
  rw [← hVU]
  exact V.property

end PartialBalayage.Linear
