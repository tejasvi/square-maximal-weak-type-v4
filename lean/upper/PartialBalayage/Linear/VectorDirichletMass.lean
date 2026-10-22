/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Linear.CapComplementarity
public import PartialBalayage.Linear.SobolevZeroSet
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Testing a vector Dirichlet equation against a regularized norm

The regularized direction has norm at most one and a positive semidefinite
Jacobian. Thus actual Sobolev graphs with the regularized norm chain rule give
nonnegative Dirichlet energy. Together with the actual weak equation this yields
a positive mass comparison. The admissibility of those simultaneous vector
Sobolev compositions is an explicit prerequisite of the final testing theorem;
it is not asserted here or replaced by a mass bound hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open CenteredMaximal.Ball.DirichletSobolev
open scoped ENNReal RealInnerProductSpace Classical

namespace PartialBalayage.Linear

section Direction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The positive regularized norm used to smooth the norm derivative. -/
def regularizedNorm (ε : ℝ) (v : E) : ℝ := Real.sqrt (‖v‖ ^ 2 + ε ^ 2)

/-- A smooth direction of norm at most one, including at the zero vector. -/
def regularizedDirection (ε : ℝ) (v : E) : E := (regularizedNorm ε v)⁻¹ • v

/-- The Jacobian of the regularized direction, written as a continuous linear map. -/
def regularizedDirectionDeriv (ε : ℝ) (v : E) : E →L[ℝ] E :=
  (regularizedNorm ε v)⁻¹ • ContinuousLinearMap.id ℝ E -
    (regularizedNorm ε v)⁻¹ ^ 3 • (innerSL ℝ v).smulRight v

omit [InnerProductSpace ℝ E] in
theorem regularizedNorm_pos {ε : ℝ} (hε : 0 < ε) (v : E) :
    0 < regularizedNorm ε v := by
  apply Real.sqrt_pos.mpr
  positivity

omit [InnerProductSpace ℝ E] in
theorem norm_le_regularizedNorm (ε : ℝ) (v : E) : ‖v‖ ≤ regularizedNorm ε v := by
  calc
    ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ ≤ regularizedNorm ε v := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

theorem norm_regularizedDirection_le {ε : ℝ} (hε : 0 < ε) (v : E) :
    ‖regularizedDirection ε v‖ ≤ 1 := by
  rw [regularizedDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (regularizedNorm_pos hε v)), inv_mul_eq_div]
  exact (div_le_one (regularizedNorm_pos hε v)).mpr (norm_le_regularizedNorm ε v)

theorem continuous_regularizedDirection {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedDirection (E := E) ε) := by
  have hs : Continuous (regularizedNorm (E := E) ε) :=
    ((continuous_norm.pow 2).add continuous_const).sqrt
  exact (hs.inv₀ (fun v ↦ (regularizedNorm_pos hε v).ne')).smul continuous_id

/-- The stated chain-rule operator is the actual derivative of the norm-test direction. -/
theorem hasFDerivAt_regularizedDirection {ε : ℝ} (hε : 0 < ε) (v : E) :
    HasFDerivAt (regularizedDirection ε) (regularizedDirectionDeriv ε v) v := by
  let s := regularizedNorm ε v
  have hs : 0 < s := regularizedNorm_pos hε v
  have harg := (hasStrictFDerivAt_norm_sq v).hasFDerivAt.add_const (ε ^ 2)
  have hnorm : HasFDerivAt (regularizedNorm ε) (s⁻¹ • innerSL ℝ v) v := by
    convert! harg.sqrt (by positivity : ‖v‖ ^ 2 + ε ^ 2 ≠ 0) using 1
    ext z
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, two_smul]
    change s⁻¹ * ⟪v, z⟫ = 1 / (2 * s) * (⟪v, z⟫ + ⟪v, z⟫)
    field_simp
    ring
  have hinv := (hasDerivAt_inv hs.ne').comp_hasFDerivAt v hnorm
  have h := hinv.smul (hasFDerivAt_id v)
  convert! h using 1
  ext z
  simp only [regularizedDirectionDeriv, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  change s⁻¹ • z - s⁻¹ ^ 3 • (⟪v, z⟫ • v) =
    s⁻¹ • z + ((-(s ^ 2)⁻¹) * (s⁻¹ * ⟪v, z⟫)) • v
  rw [smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 1
  congr 1
  field_simp

/-- Cauchy--Schwarz makes the Jacobian of the regularized norm direction nonnegative. -/
theorem inner_regularizedDirectionDeriv_nonneg {ε : ℝ} (hε : 0 < ε) (v z : E) :
    0 ≤ ⟪z, regularizedDirectionDeriv ε v z⟫ := by
  let s := regularizedNorm ε v
  have hs : 0 < s := regularizedNorm_pos hε v
  have hs2 : s ^ 2 = ‖v‖ ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hcs := real_inner_mul_inner_self_le v z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hnumer : 0 ≤ s ^ 2 * ‖z‖ ^ 2 - ⟪v, z⟫ ^ 2 := by
    rw [hs2]
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖z‖)]
  have heq : ⟪z, regularizedDirectionDeriv ε v z⟫ =
      (s ^ 2 * ‖z‖ ^ 2 - ⟪v, z⟫ ^ 2) / s ^ 3 := by
    simp only [regularizedDirectionDeriv, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm v z]
    change s⁻¹ * ‖z‖ ^ 2 - s⁻¹ ^ 3 * (⟪v, z⟫ * ⟪v, z⟫) = _
    field_simp
  rw [heq]
  exact div_nonneg hnumer (pow_pos hs 3).le

theorem regularizedDirection_tendsto (v : E) :
    Tendsto (fun n : ℕ ↦ regularizedDirection (1 / (n + 1 : ℝ)) v) atTop
      (𝓝 (capSupportVector 1 v)) := by
  by_cases hv : v = 0
  · subst v
    simp only [regularizedDirection, smul_zero, capSupportVector]
    exact tendsto_const_nhds
  · have hε := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hs : Tendsto (fun n : ℕ ↦ regularizedNorm (1 / (n + 1 : ℝ)) v)
        atTop (𝓝 ‖v‖) := by
      have hconst : Tendsto (fun _ : ℕ ↦ ‖v‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2)) :=
        tendsto_const_nhds
      have h := (hconst.add (hε.pow 2)).sqrt
      simpa only [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg v),
        regularizedNorm] using h
    have h := (hs.inv₀ (norm_ne_zero_iff.mpr hv)).smul_const v
    simpa only [regularizedDirection, capSupportVector, one_div] using h

end Direction

section MassLimit

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure X}

/-- Passage from regularized norm tests to the exact active-set mass comparison.
The test premise is a residual pairing inequality, not the asserted mass conclusion. -/
theorem active_mass_le_of_regularized_tests {u f ν : X → E} {κ : ℝ}
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ n : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ) :
    (∫ x, if u x ≠ 0 then κ else 0 ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
  let ε : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hε : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hdir n : AEStronglyMeasurable
      (fun x ↦ regularizedDirection (ε n) (u x)) μ :=
    (continuous_regularizedDirection (hε n)).comp_aestronglyMeasurable hu
  have hbound (a : X → E) (n : ℕ) (x : X) :
      ‖⟪a x, regularizedDirection (ε n) (u x)⟫‖ ≤ ‖a x‖ := by
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_regularizedDirection_le (hε n) (u x)) (norm_nonneg (a x)))
  have hint (a : X → E) (ha : Integrable a μ) (n : ℕ) :
      Integrable (fun x ↦ ⟪a x, regularizedDirection (ε n) (u x)⟫) μ :=
    ha.norm.mono' (ha.aestronglyMeasurable.inner (hdir n))
      (Eventually.of_forall (hbound a n))
  have hle n : (∫ x, ⟪ν x, regularizedDirection (ε n) (u x)⟫ ∂μ) ≤
      ∫ x, ‖f x‖ ∂μ := by
    have h := htest n
    simp only [inner_sub_left] at h
    rw [integral_sub (hint f hf n) (hint ν hν n)] at h
    exact (by linarith : (∫ x, ⟪ν x, regularizedDirection (ε n) (u x)⟫ ∂μ) ≤
      ∫ x, ⟪f x, regularizedDirection (ε n) (u x)⟫ ∂μ).trans
      (integral_mono (hint f hf n) hf.norm fun x ↦
        (real_inner_le_norm _ _).trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (norm_regularizedDirection_le (hε n) (u x)) (norm_nonneg (f x))))
  have hlim : Tendsto (fun n ↦ ∫ x, ⟪ν x, regularizedDirection (ε n) (u x)⟫ ∂μ)
      atTop (𝓝 (∫ x, if u x ≠ 0 then κ else 0 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖ν x‖)
      (fun n ↦ hν.aestronglyMeasurable.inner (hdir n)) hν.norm
      (fun n ↦ Eventually.of_forall (hbound ν n))
    filter_upwards [hpair] with x hx
    have hc : Tendsto (fun _ : ℕ ↦ ν x) atTop (𝓝 (ν x)) := tendsto_const_nhds
    have h := hc.inner (𝕜 := ℝ) (regularizedDirection_tendsto (u x))
    have heq : ⟪ν x, capSupportVector 1 (u x)⟫ = if u x ≠ 0 then κ else 0 := by
      by_cases hux : u x = 0
      · simp [hux, capSupportVector]
      · rw [ite_eq_left hux, capSupportVector, real_inner_smul_right,
          real_inner_comm (u x) (ν x), hx]
        field_simp [norm_ne_zero_iff.mpr hux]
    simpa only [heq, ε] using h
  exact le_of_tendsto hlim (Eventually.of_forall hle)

/-- The active mass comparison in the explicit volume form. -/
theorem cap_mul_measure_active_le_of_regularized_tests [IsFiniteMeasure μ]
    {u f ν : X → E} {κ : ℝ}
    (hu : AEStronglyMeasurable u μ) (hf : Integrable f μ) (hν : Integrable ν μ)
    (hpair : ∀ᵐ x ∂μ, ⟪u x, ν x⟫ = κ * ‖u x‖)
    (htest : ∀ n : ℕ, 0 ≤ ∫ x, ⟪f x - ν x,
      regularizedDirection (1 / (n + 1 : ℝ)) (u x)⟫ ∂μ) :
    κ * (μ {x | u x ≠ 0}).toReal ≤ ∫ x, ‖f x‖ ∂μ := by
  have hs : NullMeasurableSet {x | u x ≠ 0} μ := by
    have hzero := hu.norm.nullMeasurableSet_eq_fun
      (aestronglyMeasurable_const (b := (0 : ℝ)))
    simpa only [norm_eq_zero, Set.compl_ofPred] using hzero.compl
  have h := active_mass_le_of_regularized_tests hu hf hν hpair htest
  have heq : (fun x ↦ if u x ≠ 0 then κ else 0) =
      {x | u x ≠ 0}.indicator (fun _ ↦ κ) := by
    funext x
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator₀ hs, integral_const] at h
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using h

end MassLimit

section Graph

variable {d m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A finite family of actual scalar `L²` elements read as its vector field. -/
def l2VectorValue (f : Fin m → L2D Ω) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j ↦ (f j x : ℝ))

theorem memLp_l2VectorValue (f : Fin m → L2D Ω) :
    MemLp (l2VectorValue f) 2 (volume.restrict Ω) := by
  apply MemLp.of_eval_piLp
  intro j
  exact Lp.memLp (f j)

theorem integrable_l2VectorValue [IsFiniteMeasure (volume.restrict Ω)]
    (f : Fin m → L2D Ω) : Integrable (l2VectorValue f) (volume.restrict Ω) :=
  (memLp_l2VectorValue f).integrable one_le_two

/-- Scalar `L²` pairings sum to the integral of the genuine Euclidean vector pairing. -/
theorem sum_pairings_eq_integral_vector_pairing (f g : Fin m → L2D Ω) :
    (∑ j : Fin m, ⟪f j, g j⟫) =
      ∫ x, ⟪l2VectorValue f x, l2VectorValue g x⟫ ∂(volume.restrict Ω) := by
  simp only [L2.inner_def]
  rw [← integral_finsetSum]
  · rfl
  · intro j _
    exact L2.integrable_inner (𝕜 := ℝ) _ _

theorem integrable_vector_pairing (f g : Fin m → L2D Ω) :
    Integrable (fun x ↦ ⟪l2VectorValue f x, l2VectorValue g x⟫)
      (volume.restrict Ω) := by
  change Integrable (fun x ↦ ∑ j : Fin m, ⟪f j x, g j x⟫) _
  exact integrable_finsetSum _ (fun j _ ↦ L2.integrable_inner (𝕜 := ℝ) _ _)

/-- A finite family of scalar Sobolev graphs read as its genuine vector value. -/
def sobolevVectorValue (U : Fin m → H01 Ω) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j ↦ ((U j : H1amb Ω) 0 x : ℝ))

/-- A finite family of scalar Sobolev graphs read as one vector gradient coordinate. -/
def sobolevVectorGradient (U : Fin m → H01 Ω) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j ↦ ((U j : H1amb Ω) i.succ x : ℝ))

/-- An actual vector Sobolev test graph with the regularized norm chain rule. -/
def IsRegularizedDirectionGraph (ε : ℝ) (U V : Fin m → H01 Ω) : Prop :=
  (sobolevVectorValue V =ᵐ[volume.restrict Ω]
    fun x ↦ regularizedDirection ε (sobolevVectorValue U x)) ∧
  ∀ i : Fin d, sobolevVectorGradient V i =ᵐ[volume.restrict Ω]
    fun x ↦ regularizedDirectionDeriv ε (sobolevVectorValue U x)
      (sobolevVectorGradient U i x)

/-- Actual regularized norm test graphs have nonnegative Dirichlet energy. -/
theorem laplace_energy_nonneg_of_regularizedDirectionGraph {ε : ℝ} (hε : 0 < ε)
    (U V : Fin m → H01 Ω) (hgraph : IsRegularizedDirectionGraph ε U V) :
    0 ≤ ∑ j : Fin m, laplaceBilin Ω (U j) (V j) := by
  simp only [laplaceBilin_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro i _
  simp only [L2.inner_def]
  rw [← integral_finsetSum]
  · apply integral_nonneg_of_ae
    filter_upwards [hgraph.2 i] with x hx
    change 0 ≤ ⟪sobolevVectorGradient U i x, sobolevVectorGradient V i x⟫
    rw [hx]
    exact inner_regularizedDirectionDeriv_nonneg hε _ _
  · intro j _
    exact L2.integrable_inner (𝕜 := ℝ) _ _

/-- The actual coordinatewise weak Laplace equation tested by an actual regularized graph
gives the regularized residual pairing inequality. -/
theorem regularized_residual_pairing_nonneg_of_weak_equation {ε : ℝ} (hε : 0 < ε)
    (U V : Fin m → H01 Ω) (f ν : Fin m → L2D Ω)
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, (W : H1amb Ω) 0⟫)
    (hgraph : IsRegularizedDirectionGraph ε U V) :
    0 ≤ ∫ x, ⟪l2VectorValue f x - l2VectorValue ν x,
      regularizedDirection ε (sobolevVectorValue U x)⟫ ∂(volume.restrict Ω) := by
  have henergy := laplace_energy_nonneg_of_regularizedDirectionGraph hε U V hgraph
  simp only [hpde, inner_sub_left, Finset.sum_sub_distrib] at henergy
  rw [sum_pairings_eq_integral_vector_pairing, sum_pairings_eq_integral_vector_pairing,
    ← integral_sub (integrable_vector_pairing f (fun j ↦ (V j : H1amb Ω) 0))
      (integrable_vector_pairing ν (fun j ↦ (V j : H1amb Ω) 0))] at henergy
  have heq : (fun x ↦ ⟪l2VectorValue f x, sobolevVectorValue V x⟫ -
      ⟪l2VectorValue ν x, sobolevVectorValue V x⟫) =ᵐ[volume.restrict Ω]
      (fun x ↦ ⟪l2VectorValue f x - l2VectorValue ν x,
        regularizedDirection ε (sobolevVectorValue U x)⟫) := by
    filter_upwards [hgraph.1] with x hx
    rw [← inner_sub_left, hx]
  change 0 ≤ ∫ x, ⟪l2VectorValue f x, sobolevVectorValue V x⟫ -
    ⟪l2VectorValue ν x, sobolevVectorValue V x⟫ ∂(volume.restrict Ω) at henergy
  rwa [integral_congr_ae heq] at henergy

/-- Active-set mass comparison for an actual vector Dirichlet equation, conditional on
admissibility of its regularized norm graphs. No mass bound is included in the hypotheses. -/
theorem cap_mul_volume_active_le_of_weak_equation
    [IsFiniteMeasure (volume.restrict Ω)]
    (U : Fin m → H01 Ω) (f ν : Fin m → L2D Ω) {κ : ℝ}
    (hpde : ∀ j (W : H01 Ω), laplaceBilin Ω (U j) W = ⟪f j - ν j, (W : H1amb Ω) 0⟫)
    (hpair : ∀ᵐ x ∂(volume.restrict Ω),
      ⟪sobolevVectorValue U x, l2VectorValue ν x⟫ = κ * ‖sobolevVectorValue U x‖)
    (hcomp : ∀ n : ℕ, ∃ V : Fin m → H01 Ω,
      IsRegularizedDirectionGraph (1 / (n + 1 : ℝ)) U V) :
    κ * ((volume.restrict Ω) {x | sobolevVectorValue U x ≠ 0}).toReal ≤
      ∫ x, ‖l2VectorValue f x‖ ∂(volume.restrict Ω) := by
  apply cap_mul_measure_active_le_of_regularized_tests
    (memLp_l2VectorValue (fun j ↦ (U j : H1amb Ω) 0)).aestronglyMeasurable
    (integrable_l2VectorValue f) (integrable_l2VectorValue ν) hpair
  intro n
  obtain ⟨V, hV⟩ := hcomp n
  exact regularized_residual_pairing_nonneg_of_weak_equation (by positivity) U V f ν hpde hV

end Graph

end PartialBalayage.Linear
