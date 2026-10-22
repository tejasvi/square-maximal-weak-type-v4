/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.VectorDirichletMass
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Smooth multivariate compositions in the Dirichlet graph space

Finite families of scalar Sobolev graphs are composed simultaneously with smooth
vector functions. The construction first treats actual compactly supported smooth
test families and then passes through the defining graph closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal NNReal RealInnerProductSpace

namespace PartialBalayage.Linear

section FiniteLp

variable {m : ℕ}

theorem norm_euclidean_le_sum_norm (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ≤ ∑ j : Fin m, ‖v j‖ := by
  let e : Fin m → EuclideanSpace ℝ (Fin m) := fun j ↦ PiLp.single 2 j (v j)
  have hsum : (∑ j : Fin m, e j) = v := by
    ext k
    simp [e]
  calc
    ‖v‖ = ‖∑ j : Fin m, e j‖ := congrArg norm hsum.symm
    _ ≤ ∑ j : Fin m, ‖e j‖ := norm_sum_le Finset.univ e
    _ = ∑ j : Fin m, ‖v j‖ := by simp only [e, PiLp.norm_single]

theorem tendsto_eLpNorm_vector_of_coordinates {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F : ℕ → X → EuclideanSpace ℝ (Fin m)}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hcoord : ∀ j : Fin m, Tendsto (fun n ↦ eLpNorm (fun x ↦ F n x j) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun j _ ↦ hcoord j)
  simp only [Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
  intro n
  calc
    eLpNorm (F n) 2 μ ≤ eLpNorm (fun x ↦ ∑ j : Fin m, ‖F n x j‖) 2 μ := by
      apply eLpNorm_mono (hF n)
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
      exact norm_euclidean_le_sum_norm (F n x)
    _ ≤ ∑ j : Fin m, eLpNorm (fun x ↦ ‖F n x j‖) 2 μ := by
      convert! eLpNorm_sum_le (μ := μ) (p := 2) one_le_two
        (s := Finset.univ) (f := fun j : Fin m ↦ fun x ↦ ‖F n x j‖) using 1
      congr 1
      funext x
      simp
    _ = ∑ j : Fin m, eLpNorm (fun x ↦ F n x j) 2 μ := by
      exact Finset.sum_congr rfl fun j _ ↦ eLpNorm_norm _
        ((PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) j).comp_aestronglyMeasurable (hF n))

end FiniteLp

section TestFamilies

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Reading a finite family of actual test functions as its vector value. -/
def testVector (φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j ↦ φ j x)

theorem contDiff_testVector {φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ∀ j, IsTestFn Ω (φ j)) : ContDiff ℝ (⊤ : ℕ∞) (testVector φ) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (hφ j).1

/-- A smooth scalar function fixing zero turns a finite test family into an actual test function. -/
theorem isTestFn_vector_comp {φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ∀ j, IsTestFn Ω (φ j)) {F : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF0 : F 0 = 0) :
    IsTestFn Ω (F ∘ testVector φ) := by
  have hcompact : IsCompact (⋃ j, tsupport (φ j)) :=
    isCompact_iUnion (fun j ↦ (hφ j).2.1)
  have hsupport : Function.support (F ∘ testVector φ) ⊆ ⋃ j, tsupport (φ j) := by
    intro x hx
    by_contra hnot
    have hzero : testVector φ x = 0 := by
      ext j
      change φ j x = 0
      exact image_eq_zero_of_notMem_tsupport (fun hj ↦ hnot (mem_iUnion.mpr ⟨j, hj⟩))
    exact hx (by simp only [Function.comp_apply, hzero, hF0])
  have htsupport : tsupport (F ∘ testVector φ) ⊆ ⋃ j, tsupport (φ j) :=
    closure_minimal hsupport hcompact.isClosed
  exact ⟨hF.comp (contDiff_testVector hφ),
    hcompact.of_isClosed_subset isClosed_closure htsupport,
    htsupport.trans (iUnion_subset (fun j ↦ (hφ j).2.2))⟩

/-- The vector-valued derivative of a smooth test family is its vector of coordinate partials. -/
theorem fderiv_testVector_apply {φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ∀ j, IsTestFn Ω (φ j)) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (testVector φ) x (EuclideanSpace.single i 1) =
      WithLp.toLp 2 (fun j ↦ partialD i (φ j) x) := by
  ext j
  have h := (PiLp.hasFDerivAt_apply 2 (testVector φ x) j).comp x
    ((contDiff_testVector hφ).differentiable (by simp) x).hasFDerivAt
  have heq := h.fderiv
  exact (congrArg (fun L ↦ L (EuclideanSpace.single i 1)) heq).symm

/-- The genuine multivariate chain rule for each scalar test function. -/
theorem partialD_vector_comp {φ : Fin m → EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ∀ j, IsTestFn Ω (φ j)) {F : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (F ∘ testVector φ) x = fderiv ℝ F (testVector φ x)
      (WithLp.toLp 2 (fun j ↦ partialD i (φ j) x)) := by
  rw [partialD, fderiv_comp x (hF.differentiable (by simp) _)
    ((contDiff_testVector hφ).differentiable (by simp) x),
    ContinuousLinearMap.comp_apply, fderiv_testVector_apply hφ]

end TestFamilies

section GraphClosure

/-- Evaluation of a measurable field of operators on a measurable field of vectors. -/
theorem aeStronglyMeasurable_apply_field {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {L : X → E →L[ℝ] ℝ} {v : X → E}
    (hL : AEStronglyMeasurable L μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x ↦ L x (v x)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hL.prodMk hv)

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Smooth Lipschitz scalar functions of a finite Sobolev family obey the genuine
multivariate chain rule in the defining Dirichlet graph closure. -/
theorem exists_H01_vector_smooth_comp (U : Fin m → H01 Ω)
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {C : ℝ≥0} (hLip : LipschitzWith C F) (hF0 : F 0 = 0) :
    ∃ W : H01 Ω,
      (((W : H1amb Ω) 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x ↦ F (sobolevVectorValue U x)) ∧
      ∀ i : Fin d,
        (((W : H1amb Ω) i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] (fun x ↦ fderiv ℝ F (sobolevVectorValue U x)
            (sobolevVectorGradient U i x)) := by
  classical
  have happrox (j : Fin m) :
      ∃ X : ℕ → H1amb Ω, (∀ n, X n ∈ testGraphSet Ω) ∧
        Tendsto X atTop (𝓝 (U j : H1amb Ω)) := by
    have hcl : (U j : H1amb Ω) ∈ closure
        ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact (U j).property
    obtain ⟨X, hmem, ht⟩ := mem_closure_iff_seq_limit.mp hcl
    refine ⟨X, fun n ↦ ?_, ht⟩
    have hh := hmem n
    rw [span_testGraphSet] at hh
    exact hh
  choose X hX htX using happrox
  choose φ hφ hXφ using hX
  let v := sobolevVectorValue U
  let g := sobolevVectorGradient U
  let q : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) :=
    fun n ↦ testVector (fun j ↦ φ j n)
  let r : Fin d → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) :=
    fun i n x ↦ WithLp.toLp 2 (fun j ↦ partialD i (φ j n) x)
  have hvm : MemLp v 2 (volume.restrict Ω) :=
    memLp_l2VectorValue (fun j ↦ (U j : H1amb Ω) 0)
  have hgm (i : Fin d) : MemLp (g i) 2 (volume.restrict Ω) :=
    memLp_l2VectorValue (fun j ↦ (U j : H1amb Ω) i.succ)
  have hqm (n : ℕ) : MemLp (q n) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun j ↦ (hφ j n).mem_lp
  have hrm (i : Fin d) (n : ℕ) : MemLp (r i n) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun j ↦ (hφ j n).memLp_partialD i
  have hXcoord (j : Fin m) : Tendsto (fun n ↦ (X j n).ofLp) atTop
      (𝓝 (U j : H1amb Ω).ofLp) :=
    ((PiLp.continuous_ofLp 2 fun _ : Fin (d + 1) ↦ L2D Ω).tendsto _).comp (htX j)
  have hqt : Tendsto (fun n ↦ eLpNorm (q n - v) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_vector_of_coordinates _
      (fun n ↦ (hqm n).aestronglyMeasurable.sub hvm.aestronglyMeasurable)
    intro j
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (tendsto_pi_nhds.mp (hXcoord j) 0)
    refine ht.congr fun n ↦ eLpNorm_congr_ae ?_
    have heq : X j n 0 = (hφ j n).testCls := by
      rw [hXφ j n, IsTestFn.testGraph_zero]
    rw [heq]
    filter_upwards [(hφ j n).mem_lp.coeFn_toLp] with x hx
    simpa only [IsTestFn.testCls, Pi.sub_apply, q, v, testVector,
      sobolevVectorValue, PiLp.sub_apply, PiLp.toLp_apply] using congrArg
        (fun z : ℝ ↦ z - ((U j : H1amb Ω) 0 x : ℝ)) hx
  have hrt (i : Fin d) : Tendsto
      (fun n ↦ eLpNorm (r i n - g i) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_vector_of_coordinates _
      (fun n ↦ (hrm i n).aestronglyMeasurable.sub (hgm i).aestronglyMeasurable)
    intro j
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (tendsto_pi_nhds.mp (hXcoord j) i.succ)
    refine ht.congr fun n ↦ eLpNorm_congr_ae ?_
    have heq : X j n i.succ = (hφ j n).partialCls i := by
      rw [hXφ j n, IsTestFn.testGraph_succ]
    rw [heq]
    filter_upwards [((hφ j n).memLp_partialD i).coeFn_toLp] with x hx
    simpa only [IsTestFn.partialCls, Pi.sub_apply, r, g,
      sobolevVectorGradient, PiLp.sub_apply, PiLp.toLp_apply] using congrArg
        (fun z : ℝ ↦ z - ((U j : H1amb Ω) i.succ x : ℝ)) hx
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hqt
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  let ψ : ℕ → Fin m → EuclideanSpace ℝ (Fin d) → ℝ := fun n j ↦ φ j (ns n)
  have hψ (n : ℕ) (j : Fin m) : IsTestFn Ω (ψ n j) := hφ j (ns n)
  let θ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n ↦ F ∘ testVector (ψ n)
  have hθ (n : ℕ) : IsTestFn Ω (θ n) := isTestFn_vector_comp (hψ n) hF hF0
  have hθgrad (n : ℕ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
      partialD i (θ n) x = fderiv ℝ F (q (ns n) x) (r i (ns n) x) :=
    partialD_vector_comp (hψ n) hF i x
  have hderivcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hderiv (x : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ F x‖ ≤ C :=
    norm_fderiv_le_of_lipschitz ℝ hLip
  have hwm (i : Fin d) : MemLp (fun x ↦ fderiv ℝ F (v x) (g i x)) 2
      (volume.restrict Ω) := by
    refine (hgm i).of_le_mul (c := (C : ℝ)) ?_ (Eventually.of_forall fun x ↦ ?_)
    · exact aeStronglyMeasurable_apply_field
        (hderivcont.comp_aestronglyMeasurable hvm.aestronglyMeasurable)
        (hgm i).aestronglyMeasurable
    · exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hderiv _) (norm_nonneg _))
  let vlp := hvm.toLp v
  let w0 : L2D Ω := hLip.compLp hF0 vlp
  let w : H1amb Ω := WithLp.toLp 2 (Fin.cons w0 fun i ↦ (hwm i).toLp _)
  have hw0 : ((w 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x ↦ F (v x) := by
    filter_upwards [hLip.coeFn_compLp hF0 vlp, hvm.coeFn_toLp] with x hx hy
    exact hx.trans (congrArg F hy)
  have hwi (i : Fin d) : ((w i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x ↦ fderiv ℝ F (v x) (g i x) := by
    simpa only [w, PiLp.toLp_apply, Fin.cons_succ] using (hwm i).coeFn_toLp
  have hθ0t : Tendsto (fun n ↦ (hθ n).testCls) atTop (𝓝 w0) := by
    have hqtLp : Tendsto (fun n ↦ (hqm n).toLp _) atTop (𝓝 vlp) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' q hqm v hvm).mpr hqt
    have hcomp := ((hLip.continuous_compLp hF0).tendsto vlp).comp
      (hqtLp.comp hns.tendsto_atTop)
    refine hcomp.congr fun n ↦ ?_
    apply Lp.ext
    filter_upwards [(hθ n).mem_lp.coeFn_toLp,
      hLip.coeFn_compLp hF0 ((hqm (ns n)).toLp _), (hqm (ns n)).coeFn_toLp]
      with x hx hy hz
    simpa only [θ, Function.comp_apply, ψ, q, IsTestFn.testCls] using
      (hy.trans (congrArg F hz)).trans hx.symm
  have hθit (i : Fin d) : Tendsto (fun n ↦ (hθ n).partialCls i) atTop
      (𝓝 ((hwm i).toLp _)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n ↦ partialD i (θ n)) (fun n ↦ (hθ n).memLp_partialD i)
      (fun x ↦ fderiv ℝ F (v x) (g i x)) (hwm i)).mpr
    let A : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun n x ↦ fderiv ℝ F (q (ns n) x) (r i (ns n) x - g i x)
    let B : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun n x ↦ (fderiv ℝ F (q (ns n) x) - fderiv ℝ F (v x)) (g i x)
    have hsplit (n : ℕ) : (partialD i (θ n) - fun x ↦ fderiv ℝ F (v x) (g i x)) =
        A n + B n := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, A, B, hθgrad,
        ContinuousLinearMap.map_sub, sub_apply]
      ring
    have hAm (n : ℕ) : AEStronglyMeasurable (A n) (volume.restrict Ω) :=
      aeStronglyMeasurable_apply_field
        (hderivcont.comp_aestronglyMeasurable (hqm (ns n)).aestronglyMeasurable)
        ((hrm i (ns n)).aestronglyMeasurable.sub (hgm i).aestronglyMeasurable)
    have hBm (n : ℕ) : AEStronglyMeasurable (B n) (volume.restrict Ω) :=
      aeStronglyMeasurable_apply_field
        ((hderivcont.comp_aestronglyMeasurable (hqm (ns n)).aestronglyMeasurable).sub
          (hderivcont.comp_aestronglyMeasurable hvm.aestronglyMeasurable))
        (hgm i).aestronglyMeasurable
    have hAt : Tendsto (fun n ↦ eLpNorm (A n) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      have hlim := ENNReal.Tendsto.const_mul
        ((hrt i).comp hns.tendsto_atTop)
        (Or.inr (ENNReal.ofReal_lt_top.ne : ENNReal.ofReal (C : ℝ) ≠ ⊤))
      rw [mul_zero] at hlim
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ ↦ zero_le) fun n ↦ ?_
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hAm n)
        (Eventually.of_forall fun x ↦ (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hderiv _) (norm_nonneg _))) 2
    have hBt : Tendsto (fun n ↦ eLpNorm (B n) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      apply tendsto_eLpNorm_two_zero_of_dominated (volume.restrict Ω)
        ((hgm i).norm.const_mul (2 * (C : ℝ))) hBm
      · intro n x
        have hdiff : ‖fderiv ℝ F (q (ns n) x) - fderiv ℝ F (v x)‖ ≤ 2 * (C : ℝ) :=
          (norm_sub_le _ _).trans ((add_le_add (hderiv _) (hderiv _)).trans_eq (by ring))
        calc
          ‖B n x‖ ≤ (2 * (C : ℝ)) * ‖g i x‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
          _ = ‖(2 * (C : ℝ)) * ‖g i x‖‖ :=
            (Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).symm
      · filter_upwards [hae] with x hx
        have hp := ((hderivcont.tendsto (v x)).comp hx).sub
          (tendsto_const_nhds (x := fderiv ℝ F (v x)))
        have ht := ((ContinuousLinearMap.apply ℝ ℝ (g i x)).continuous.tendsto _).comp hp
        simpa only [B, Function.comp_def, sub_self, ContinuousLinearMap.apply_apply,
          zero_apply] using ht
    have hsum := hAt.add hBt
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun n ↦ ?_
    rw [hsplit]
    exact eLpNorm_add_le one_le_two
  have hwmem : w ∈ H01 Ω := by
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) ?_
      (Eventually.of_forall fun n ↦ (Submodule.span ℝ (testGraphSet Ω)).le_topologicalClosure
        (Submodule.subset_span ⟨θ n, hθ n, rfl⟩))
    change Tendsto (fun n ↦ WithLp.toLp 2 (Fin.cons (hθ n).testCls
      fun i ↦ (hθ n).partialCls i)) atTop (𝓝 w)
    refine ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) ↦ L2D Ω).tendsto _).comp
      (tendsto_pi_nhds.mpr fun j ↦ ?_)
    induction j using Fin.cases with
    | zero => simpa only [Fin.cons_zero, w, PiLp.toLp_apply] using hθ0t
    | succ i => simpa only [Fin.cons_succ, w, PiLp.toLp_apply] using hθit i
  exact ⟨⟨w, hwmem⟩, hw0, hwi⟩

end GraphClosure

section Regularized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_regularizedDirection {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedDirection (E := E) ε) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (regularizedNorm (E := E) ε) :=
    ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun v ↦ by positivity)
  exact (hs.inv (fun v ↦ (regularizedNorm_pos hε v).ne')).smul contDiff_id

/-- A uniform Jacobian bound sufficient for the actual Sobolev composition construction. -/
theorem norm_regularizedDirectionDeriv_le {ε : ℝ} (hε : 0 < ε) (v : E) :
    ‖regularizedDirectionDeriv ε v‖ ≤ 2 / ε := by
  let s := regularizedNorm ε v
  have hs : 0 < s := regularizedNorm_pos hε v
  have hv : ‖v‖ ≤ s := norm_le_regularizedNorm ε v
  have hεs : ε ≤ s := by
    calc
      ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ s := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖v‖])
  have hinv : s⁻¹ ^ 3 * ‖v‖ ^ 2 ≤ s⁻¹ := by
    calc
      s⁻¹ ^ 3 * ‖v‖ ^ 2 ≤ s⁻¹ ^ 3 * s ^ 2 := by gcongr
      _ = s⁻¹ := by field_simp
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hterm : ‖s⁻¹ ^ 3 • (⟪v, z⟫ • v)‖ ≤ s⁻¹ * ‖z‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.mpr hs) 3)]
    calc
      s⁻¹ ^ 3 * (|⟪v, z⟫| * ‖v‖) ≤ s⁻¹ ^ 3 * ((‖v‖ * ‖z‖) * ‖v‖) := by
        gcongr
        exact abs_real_inner_le_norm v z
      _ = (s⁻¹ ^ 3 * ‖v‖ ^ 2) * ‖z‖ := by ring
      _ ≤ s⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  calc
    ‖regularizedDirectionDeriv ε v z‖ = ‖s⁻¹ • z - s⁻¹ ^ 3 • (⟪v, z⟫ • v)‖ := by
      simp only [regularizedDirectionDeriv, sub_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
      rfl
    _ ≤ ‖s⁻¹ • z‖ + ‖s⁻¹ ^ 3 • (⟪v, z⟫ • v)‖ := norm_sub_le _ _
    _ ≤ s⁻¹ * ‖z‖ + s⁻¹ * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
      exact add_le_add le_rfl hterm
    _ ≤ ε⁻¹ * ‖z‖ + ε⁻¹ * ‖z‖ := by
      gcongr
    _ = (2 / ε) * ‖z‖ := by ring

/-- The regularized norm direction is globally Lipschitz, including through the origin. -/
theorem lipschitzWith_regularizedDirection {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨2 / ε, by positivity⟩ (regularizedDirection (E := E) ε) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_regularizedDirection hε).differentiable (by simp))
  intro v
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, (hasFDerivAt_regularizedDirection hε v).fderiv]
  exact norm_regularizedDirectionDeriv_le hε v

end Regularized

section ActualNormTestGraphs

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The regularized norm direction is an actual admissible vector `H01` test graph,
constructed from the defining graph closure without any chain-rule hypothesis. -/
theorem exists_regularizedDirectionGraph {ε : ℝ} (hε : 0 < ε) (U : Fin m → H01 Ω) :
    ∃ V : Fin m → H01 Ω, IsRegularizedDirectionGraph ε U V := by
  classical
  let P (j : Fin m) : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin m ↦ ℝ) j
  let F (j : Fin m) : EuclideanSpace ℝ (Fin m) → ℝ :=
    P j ∘ regularizedDirection ε
  have hF (j : Fin m) : ContDiff ℝ (⊤ : ℕ∞) (F j) :=
    (P j).contDiff.comp (contDiff_regularizedDirection hε)
  have hLip (j : Fin m) : LipschitzWith (‖P j‖₊ * ⟨2 / ε, by positivity⟩) (F j) :=
    (P j).lipschitzWith.comp (lipschitzWith_regularizedDirection hε)
  have hzero (j : Fin m) : F j 0 = 0 := by
    simp only [F, Function.comp_apply, regularizedDirection, smul_zero, map_zero]
  have hex (j : Fin m) := exists_H01_vector_smooth_comp U (hF j) (hLip j) (hzero j)
  choose V hv hg using hex
  refine ⟨V, ?_, fun i ↦ ?_⟩
  · filter_upwards [ae_all_iff.mpr hv] with x hx
    ext j
    exact hx j
  · filter_upwards [ae_all_iff.mpr (fun j ↦ hg j i)] with x hx
    ext j
    have hderiv := (P j).hasFDerivAt.comp (sobolevVectorValue U x)
      (hasFDerivAt_regularizedDirection hε (sobolevVectorValue U x))
    have hj := hx j
    rw [hderiv.fderiv] at hj
    exact hj

/-- The vector Dirichlet equation itself implies the active-volume mass estimate.
All regularized norm tests are supplied by actual Sobolev graph closure. -/
theorem cap_mul_volume_active_le_of_vector_weak_equation
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ}
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, (W : H1amb Ω) 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖) :
    κ * ((volume.restrict Ω) {x | sobolevVectorValue U x ≠ 0}).toReal ≤
      ∫ x, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) :=
  cap_mul_volume_active_le_of_weak_equation U f ν hpde hpair
    (fun n ↦ exists_regularizedDirectionGraph (by positivity) U)

end ActualNormTestGraphs

end PartialBalayage.Linear
