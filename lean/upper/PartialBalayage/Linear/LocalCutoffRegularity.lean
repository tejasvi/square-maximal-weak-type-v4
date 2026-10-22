/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.LocalCutoffLaplacian
public import PartialBalayage.Linear.LocalSecondSobolev

/-!
# Represented cutoff forcing for actual Dirichlet solutions

The cutoff forcing is constructed in `L²`, using the actual value and gradient coordinates
of the Dirichlet graph. Its zero extension satisfies the genuine whole-space weak equation.
This is an interior localization construction, without any boundary regularity assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Ball.DirichletSobolev
open scoped RealInnerProductSpace SchwartzMap Laplacian LineDeriv Classical

namespace PartialBalayage.Linear

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Multiplication by a genuine compactly supported smooth cutoff preserves `L²`. -/
theorem memLp_L2_mul_cutoff (a : L2D Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    MemLp (fun x ↦ (a x : ℝ) * χ x) 2 (volume.restrict Ω) := by
  obtain ⟨C, hC⟩ := hχ.2.1.exists_bound_of_continuous hχ.continuous
  refine (Lp.memLp a).of_le_mul (c := C)
    ((Lp.memLp a).aestronglyMeasurable.mul hχ.continuous.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖(a x : ℝ)‖ * ‖χ x‖ ≤ ‖(a x : ℝ)‖ * C :=
      mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
    _ = C * ‖(a x : ℝ)‖ := mul_comm _ _

/-- The actual interior forcing after multiplication of a scalar Dirichlet state by a cutoff. -/
def dirichletCutoffForcing (U : H01 Ω) (g : L2D Ω)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(g x : ℝ) * χ x +
    2 * (∑ i : Fin d, ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x) +
      ∑ i : Fin d, ((U : H1amb Ω) 0 x : ℝ) * partialD i (partialD i χ) x

/-- The cutoff forcing belongs to `L²` by the actual first-derivative graph bounds. -/
theorem memLp_dirichletCutoffForcing (U : H01 Ω) (g : L2D Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    MemLp (dirichletCutoffForcing U g χ) 2 (volume.restrict Ω) := by
  have hB : MemLp (fun x ↦ ∑ i : Fin d,
      ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x) 2 (volume.restrict Ω) :=
    memLp_finsetSum Finset.univ (fun i _ ↦
      memLp_L2_mul_cutoff ((U : H1amb Ω) i.succ) (hχ.partialD i))
  have hD : MemLp (fun x ↦ ∑ i : Fin d,
      ((U : H1amb Ω) 0 x : ℝ) * partialD i (partialD i χ) x) 2 (volume.restrict Ω) :=
    memLp_finsetSum Finset.univ (fun i _ ↦
      memLp_L2_mul_cutoff ((U : H1amb Ω) 0) ((hχ.partialD i).partialD i))
  convert! ((memLp_L2_mul_cutoff g hχ).neg.add (hB.const_smul (2 : ℝ))).add hD using 1
  funext x
  simp only [dirichletCutoffForcing, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The constructed forcing is exactly the right side of the genuine localized weak equation. -/
theorem weak_laplacian_dirichletCutoffForcing (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x in Ω, ((U : H1amb Ω) 0 x : ℝ) * χ x * Laplacian.laplacian φ x) =
      ∫ x in Ω, dirichletCutoffForcing U g χ x * φ x := by
  have hg := integrable_L2_mul_cutoff_smooth g hχ hφ
  have hB (i : Fin d) := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) i.succ)
    (hχ.partialD i) hφ
  have hD (i : Fin d) := integrable_L2_mul_cutoff_smooth ((U : H1amb Ω) 0)
    ((hχ.partialD i).partialD i) hφ
  have hBs := integrable_finsetSum Finset.univ (fun i _ ↦ hB i)
  have hDs := integrable_finsetSum Finset.univ (fun i _ ↦ hD i)
  have hN : Integrable (fun x ↦ -((g x : ℝ) * χ x * φ x)) (volume.restrict Ω) := hg.neg
  have hT : Integrable (fun x ↦
      2 * (∑ i : Fin d, ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x))
      (volume.restrict Ω) := hBs.const_mul 2
  have hNT : Integrable (fun x ↦ -((g x : ℝ) * χ x * φ x) +
      2 * (∑ i : Fin d, ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x))
      (volume.restrict Ω) := hN.add hT
  rw [weak_laplacian_cutoff_product U g heq hχ hφ]
  symm
  calc
    _ = ∫ x in Ω,
        -((g x : ℝ) * χ x * φ x) +
          2 * (∑ i : Fin d, ((U : H1amb Ω) i.succ x : ℝ) * partialD i χ x * φ x) +
            ∑ i : Fin d, ((U : H1amb Ω) 0 x : ℝ) * partialD i (partialD i χ) x * φ x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [dirichletCutoffForcing, add_mul, mul_assoc, Finset.sum_mul]
      ring
    _ = _ := by
      rw [integral_add hNT hDs, integral_add hN hT, integral_neg, integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ ↦ hB i),
        integral_finsetSum Finset.univ (fun i _ ↦ hD i)]

/-- The actual zero-extended cutoff state is in whole-space `L²`. -/
theorem memLp_indicator_cutoff_state (hΩ : MeasurableSet Ω) (U : H01 Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    MemLp (Ω.indicator (fun x ↦ ((U : H1amb Ω) 0 x : ℝ) * χ x)) 2 volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (memLp_L2_mul_cutoff ((U : H1amb Ω) 0) hχ)

/-- The actual zero-extended forcing is in whole-space `L²`. -/
theorem memLp_indicator_cutoff_forcing (hΩ : MeasurableSet Ω) (U : H01 Ω) (g : L2D Ω)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    MemLp (Ω.indicator (dirichletCutoffForcing U g χ)) 2 volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (memLp_dirichletCutoffForcing U g hχ)

/-- The constructed zero extensions satisfy the actual whole-space weak Laplace equation. -/
theorem weak_laplacian_indicator_cutoff (hΩ : MeasurableSet Ω) (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn Ω χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x, Ω.indicator (fun y ↦ ((U : H1amb Ω) 0 y : ℝ) * χ y) x *
      Laplacian.laplacian φ x) =
      ∫ x, Ω.indicator (dirichletCutoffForcing U g χ) x * φ x := by
  have hinL : (fun x ↦ Ω.indicator (fun y ↦ ((U : H1amb Ω) 0 y : ℝ) * χ y) x *
      Laplacian.laplacian φ x) =
      Ω.indicator (fun x ↦ ((U : H1amb Ω) 0 x : ℝ) * χ x * Laplacian.laplacian φ x) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hinR : (fun x ↦ Ω.indicator (dirichletCutoffForcing U g χ) x * φ x) =
      Ω.indicator (fun x ↦ dirichletCutoffForcing U g χ x * φ x) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [hinL, hinR, integral_indicator hΩ, integral_indicator hΩ]
  exact weak_laplacian_dirichletCutoffForcing U g heq hχ hφ

/-- An actual real weak Laplace equation gives order-two Fourier Sobolev regularity
of its complexification. The test equation, rather than regularity, is the hypothesis. -/
theorem memSobolev_two_complexification_of_real_weak_laplacian
    (a b : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (∫ x, (a x : ℝ) * Laplacian.laplacian φ x) = ∫ x, (b x : ℝ) * φ x) :
    TemperedDistribution.MemSobolev 2 2
      (Complex.ofRealCLM.compLp a : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  let u := Complex.ofRealCLM.compLp a
  let g := Complex.ofRealCLM.compLp b
  apply memSobolev_two_of_L2_laplacian u g
  apply laplacian_L2_eq_of_weak_integrals
  intro φ
  have hu := Complex.ofRealCLM.coeFn_compLp a
  have hg := Complex.ofRealCLM.coeFn_compLp b
  have hL : Integrable (fun x ↦ (Δ φ) x • (u x : ℂ)) volume := by
    simpa only [smul_eq_mul] using (Δ φ).memLp 2 |>.integrable_mul (Lp.memLp u)
  have hR : Integrable (fun x ↦ φ x • (g x : ℂ)) volume := by
    convert! (φ.memLp 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))).integrable_mul
      (Lp.memLp g) using 1
  have hproj (l : ℂ →L[ℝ] ℝ) :
      l (∫ x, (Δ φ) x • (u x : ℂ)) = l (∫ x, φ x • (g x : ℂ)) := by
    rw [← l.integral_comp_comm hL, ← l.integral_comp_comm hR]
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (l ∘ (φ : EuclideanSpace ℝ (Fin d) → ℂ)) :=
      l.contDiff.comp (φ.smooth ⊤)
    have hΔ (x : EuclideanSpace ℝ (Fin d)) :
        Laplacian.laplacian (l ∘ (φ : EuclideanSpace ℝ (Fin d) → ℂ)) x = l ((Δ φ) x) := by
      simpa only [Function.comp_apply, SchwartzMap.laplacian_apply] using
        (φ.contDiffAt 2).laplacian_CLM_comp_left (l := l) (x := x)
    have hmul (z : ℂ) (r : ℝ) : l (z * (r : ℂ)) = r * l z := by
      rw [mul_comm, ← Complex.real_smul, l.map_smul]
      rfl
    convert! hweak _ hφ using 1
    · apply integral_congr_ae
      filter_upwards [hu] with x hx
      simp only [u, hx, Complex.ofRealCLM_apply, smul_eq_mul, hmul, hΔ]
    · apply integral_congr_ae
      filter_upwards [hg] with x hx
      simp only [g, hx, Complex.ofRealCLM_apply, smul_eq_mul, hmul, Function.comp_apply]
  exact Complex.ext (by simpa only [Complex.reCLM_apply] using hproj Complex.reCLM)
    (by simpa only [Complex.imCLM_apply] using hproj Complex.imCLM)

/-- Multiplication by an actual interior cutoff constructs a represented `H²` function
from the genuine `H01` weak solution, with its correct almost-everywhere value. -/
theorem exists_cutoff_memSobolev_two (hΩ : MeasurableSet Ω) (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    ∃ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (∀ᵐ x ∂volume, (u x : ℂ) =
        (Ω.indicator (fun y ↦ ((U : H1amb Ω) 0 y : ℝ) * χ y) x : ℝ)) ∧
      TemperedDistribution.MemSobolev 2 2
        (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  let ha := memLp_indicator_cutoff_state hΩ U hχ
  let hb := memLp_indicator_cutoff_forcing hΩ U g hχ
  let a := ha.toLp (Ω.indicator (fun x ↦ ((U : H1amb Ω) 0 x : ℝ) * χ x))
  let b := hb.toLp (Ω.indicator (dirichletCutoffForcing U g χ))
  have hweak : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (∫ x, (a x : ℝ) * Laplacian.laplacian φ x) = ∫ x, (b x : ℝ) * φ x := by
    intro φ hφ
    convert! weak_laplacian_indicator_cutoff hΩ U g heq hχ hφ using 1
    · apply integral_congr_ae
      filter_upwards [ha.coeFn_toLp] with x hx
      simp only [a, hx]
    · apply integral_congr_ae
      filter_upwards [hb.coeFn_toLp] with x hx
      simp only [b, hx]
  refine ⟨Complex.ofRealCLM.compLp a, ?_,
    memSobolev_two_complexification_of_real_weak_laplacian a b hweak⟩
  filter_upwards [Complex.ofRealCLM.coeFn_compLp a, ha.coeFn_toLp] with x hx hax
  simp only [hx, Complex.ofRealCLM_apply, a, hax]

/-- The actual interior cutoff state has represented second distributional derivatives
in every pair of directions. No regularity assumption on the graph gradients is added. -/
theorem exists_cutoff_L2_second_derivatives (hΩ : MeasurableSet Ω)
    (U : H01 Ω) (g : L2D Ω)
    (heq : ∀ W : H01 Ω, laplaceBilin Ω U W = l2Functional Ω g W)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn Ω χ) :
    ∃ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (∀ᵐ x ∂volume, (u x : ℂ) =
        (Ω.indicator (fun y ↦ ((U : H1amb Ω) 0 y : ℝ) * χ y) x : ℝ)) ∧
      ∀ v w : EuclideanSpace ℝ (Fin d),
        ∃ H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
          ∂_{w} (∂_{v} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) =
            (H : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  obtain ⟨u, hu, hreg⟩ := exists_cutoff_memSobolev_two hΩ U g heq hχ
  refine ⟨u, hu, fun v w ↦ ?_⟩
  have hv : TemperedDistribution.MemSobolev 1 2
      (∂_{v} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using hreg.lineDerivOp (m := v)
  have hw : TemperedDistribution.MemSobolev 0 2
      (∂_{w} (∂_{v} (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)))) := by
    simpa only [sub_self] using hv.lineDerivOp (m := w)
  exact TemperedDistribution.memSobolev_zero_iff.mp hw

end PartialBalayage.Linear
