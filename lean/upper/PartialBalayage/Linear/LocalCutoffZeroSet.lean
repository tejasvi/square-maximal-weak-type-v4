/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.FourierSobolevGraph
public import PartialBalayage.Linear.SecondGraphWeakLaplacian
public import PartialBalayage.Linear.LocalCutoffRegularity
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Genuine second-gradient locality for compact Fourier Sobolev states

Order-two Fourier regularity and a compact value representative construct actual first and
second `H01` graphs. The first-gradient zero-set theorem makes the derivative values compact,
so the second graphs also enter the genuine test-function closure. No graph membership or
second-derivative locality is added as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal SchwartzMap Laplacian

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A compact actual order-two Fourier Sobolev state has genuine iterated `H01` graphs. -/
theorem exists_second_H01_graph_of_compact_memSobolev_two
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 2 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hzero : ∀ᵐ x ∂volume, x ∉ K → (u x : ℂ).re = 0) :
    ∃ U : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))),
      ∃ G : Fin d → H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))),
        (U.val 0 =ᵐ[volume] fun x ↦ (u x : ℂ).re) ∧ IsSecondGradientGraph U G := by
  let hu1 := TemperedDistribution.MemSobolev.mono (by norm_num : (1 : ℝ) ≤ 2) hu
  let V := fourierSobolevRealGraph u hu1
  have hV0 : V.val 0 =ᵐ[volume] fun x ↦ (u x : ℂ).re :=
    complexL2GradientGraph_value_ae u _
  have hVzero : ∀ᵐ x ∂volume, x ∉ K → V.val 0 x = 0 := by
    filter_upwards [hV0, hzero] with x hx hz
    exact fun hxK ↦ hx.trans (hz hxK)
  let U : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    ⟨V.val, mem_H01_univ_of_compact_weak_graph V.property hK hVzero⟩
  let g (i : Fin d) := sobolevL2Partial u hu1 i
  have hg (i : Fin d) : TemperedDistribution.MemSobolev 1 2
      (g i : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :=
    memSobolev_one_sobolevL2Partial_of_memSobolev_two u hu i
  let W (i : Fin d) := fourierSobolevRealGraph (g i) (hg i)
  have hW0 (i : Fin d) : (W i).val 0 =ᵐ[volume] U.val i.succ :=
    (complexL2GradientGraph_value_ae (g i) _).trans
      (complexL2GradientGraph_partial_ae u _ i).symm
  have hWzero (i : Fin d) : ∀ᵐ x ∂volume, x ∉ K → (W i).val 0 x = 0 := by
    have hlocal : ∀ᵐ x ∂volume, U.val 0 x = 0 → U.val i.succ x = 0 := by
      simpa only [Measure.restrict_univ] using
        ae_gradient_eq_zero_on_value_zero isOpen_univ U i
    filter_upwards [hW0 i, hVzero, hlocal] with x hw hz hl
    exact fun hxK ↦ hw.trans (hl (hz hxK))
  let G (i : Fin d) : H01 (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    ⟨(W i).val, mem_H01_univ_of_compact_weak_graph (W i).property hK (hWzero i)⟩
  refine ⟨U, G, hV0, fun i ↦ ?_⟩
  simpa only [Filter.EventuallyEq, Measure.restrict_univ] using hW0 i

/-- The actual `L²` weak Laplacian of a compact order-two state vanishes on its value zero set. -/
theorem ae_weak_laplacian_zero_of_compact_memSobolev_two
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.MemSobolev 2 2
      (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hzero : ∀ᵐ x ∂volume, x ∉ K → (u x : ℂ).re = 0)
    {q : EuclideanSpace ℝ (Fin d) → ℝ} (hq : MemLp q 2 volume)
    (heq : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ →
      (∫ x, (u x : ℂ).re * Δ φ x) = ∫ x, q x * φ x) :
    ∀ᵐ x ∂volume, (u x : ℂ).re = 0 → q x = 0 := by
  obtain ⟨U, G, hU0, hG⟩ := exists_second_H01_graph_of_compact_memSobolev_two u hu hK hzero
  have heqU : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ →
      (∫ x, U.val 0 x * Δ φ x) = ∫ x, q x * φ x := by
    intro φ hφ
    rw [← heq φ hφ]
    exact integral_congr_ae (hU0.fun_mul (Filter.EventuallyEq.refl (ae volume) (Δ φ)))
  have hqeq := ae_secondGraphLaplacian_eq_of_weak_laplacian U G hG hq heqU
  have hlocal : ∀ᵐ x ∂volume, U.val 0 x = 0 → secondGraphLaplacian G x = 0 := by
    simpa only [Measure.restrict_univ] using
      ae_secondGraphLaplacian_eq_zero_on_value_zero isOpen_univ U G hG
  filter_upwards [hU0, hqeq, hlocal] with x hu0 hqx hx
  exact fun hz ↦ hqx.symm.trans (hx (hu0.trans hz))

/-- Every actual interior cutoff kills the forcing on the original Dirichlet state zero set.
The second Sobolev graphs used here are constructed from the actual weak PDE, rather than
required as an additional regularity hypothesis. -/
theorem ae_cutoff_mul_forcing_eq_zero_on_value_zero (hΩ : IsOpen Ω)
    (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    ∀ᵐ x ∂(volume.restrict Ω), U.val 0 x = 0 → χ x * g x = 0 := by
  obtain ⟨u, huvalue, hu⟩ := exists_cutoff_memSobolev_two hΩ.measurableSet U g heq hχ
  let q := Ω.indicator (dirichletCutoffForcing U g χ)
  have hucompact : ∀ᵐ x ∂volume, x ∉ tsupport χ → (u x : ℂ).re = 0 := by
    filter_upwards [huvalue] with x hx
    intro hxK
    have hχzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxK
    rw [hx, Complex.ofReal_re]
    by_cases hxΩ : x ∈ Ω
    · simp only [Set.indicator_of_mem hxΩ, hχzero, mul_zero]
    · exact Set.indicator_of_notMem hxΩ _
  have hq : MemLp q 2 volume := memLp_indicator_cutoff_forcing hΩ.measurableSet U g hχ
  have hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Set.univ φ →
      (∫ x, (u x : ℂ).re * Δ φ x) = ∫ x, q x * φ x := by
    intro φ hφ
    rw [← weak_laplacian_indicator_cutoff hΩ.measurableSet U g heq hχ hφ.1]
    apply integral_congr_ae
    filter_upwards [huvalue] with x hx
    rw [hx, Complex.ofReal_re]
  have hqlocal := ae_weak_laplacian_zero_of_compact_memSobolev_two u hu hχ.2.1.isCompact
    hucompact hq hweak
  filter_upwards [ae_restrict_of_ae huvalue, ae_restrict_of_ae hqlocal,
    ae_all_gradients_eq_zero_on_value_zero hΩ U, ae_restrict_mem hΩ.measurableSet]
    with x huval hqx hgrad hxΩ
  intro hxzero
  have huzero : (u x : ℂ).re = 0 := by
    rw [huval, Complex.ofReal_re, Set.indicator_of_mem hxΩ, hxzero, zero_mul]
  have hqzero : dirichletCutoffForcing U g χ x = 0 := by
    simpa only [q, Set.indicator_of_mem hxΩ] using hqx huzero
  have hgradzero (i : Fin d) : U.val i.succ x = 0 := hgrad hxzero i
  simp only [dirichletCutoffForcing, hxzero, hgradzero, zero_mul,
    Finset.sum_const_zero, mul_zero, add_zero, neg_mul] at hqzero
  have h : g x * χ x = 0 := neg_eq_zero.mp hqzero
  simpa only [mul_comm] using h

/-- Every point of an open domain has an actual smooth interior cutoff equal to one there. -/
theorem exists_testFn_eq_one_at (hΩ : IsOpen Ω) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Ω χ ∧ χ x = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let χ : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hχ : IsTestFn Ω χ := by
    refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [χ]; linarith)).trans hball
  refine ⟨χ, hχ, χ.one_of_mem_closedBall ?_⟩
  simp only [Metric.mem_closedBall, dist_self]
  exact χ.rIn_pos.le

/-- The forcing of an actual `H01` weak Laplace solution vanishes on its value zero set.
This is genuine interior second-order locality, with no second-gradient graph hypothesis. -/
theorem ae_forcing_eq_zero_on_value_zero_of_weak_laplacian (hΩ : IsOpen Ω)
    (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W) :
    ∀ᵐ x ∂(volume.restrict Ω), U.val 0 x = 0 → g x = 0 := by
  let ι := {χ : EuclideanSpace ℝ (Fin d) → ℝ // IsTestFn Ω χ}
  let O (χ : ι) := {x | χ.val x ≠ 0}
  have hOo (χ : ι) : IsOpen (O χ) := by
    exact (isClosed_eq χ.property.continuous continuous_const).isOpen_compl
  have hcover : Ω ⊆ ⋃ χ : ι, O χ := by
    intro x hx
    obtain ⟨χ, hχ, hχx⟩ := exists_testFn_eq_one_at hΩ hx
    refine mem_iUnion.mpr ⟨⟨χ, hχ⟩, ?_⟩
    change χ x ≠ (0 : ℝ)
    rw [hχx]
    exact one_ne_zero
  obtain ⟨r, hr, hrc⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    O hOo hcover
  have : Countable r := hr.to_subtype
  have hall : ∀ᵐ x ∂(volume.restrict Ω), ∀ χ : r, U.val 0 x = 0 → χ.val.val x * g x = 0 :=
    ae_all_iff.mpr fun χ ↦ ae_cutoff_mul_forcing_eq_zero_on_value_zero hΩ U g heq χ.val.property
  filter_upwards [hall, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  intro hzero
  obtain ⟨χ, hχr, hxχ⟩ := mem_iUnion₂.mp (hrc hxΩ)
  have hχne : χ.val x ≠ 0 := hxχ
  exact (mul_eq_zero.mp (hx ⟨χ, hχr⟩ hzero)).resolve_left hχne

end PartialBalayage.Linear
