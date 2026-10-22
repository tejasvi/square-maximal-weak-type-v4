/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.SemigroupDefinitions
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Positive-time continuity of the actual heat and Poisson convolutions

On every compact interval of positive times, the original kernels have a uniform
spatial bound. Multiplication by an integrable input therefore has an integrable
dominating function. Dominated convergence proves continuity in time at every spatial
point, with no regularity or boundedness assumption on the input beyond integrability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PartialBalayage

/-- The ordinary real heat convolution, before taking the supremum in time. -/
def heatConvolution {n : ℕ} (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, heatKernel n t (x - y) * f y

/-- The ordinary real Poisson convolution, before taking the supremum in height. -/
def poissonConvolution {n : ℕ} (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, poissonKernel n t (x - y) * f y

theorem continuousAt_heatKernel_time (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : ContinuousAt (fun s ↦ heatKernel n s x) t := by
  unfold heatKernel
  have hbase : ContinuousAt (fun s : ℝ ↦ 4 * Real.pi * s) t := by fun_prop
  have hp := hbase.rpow_const (p := -(n : ℝ) / 2) (Or.inl (by positivity))
  have he : ContinuousAt (fun s : ℝ ↦ Real.exp (-‖x‖ ^ 2 / (4 * s))) t := by
    exact Real.continuous_exp.continuousAt.comp
      (continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity))
  exact hp.mul he

theorem continuousAt_poissonKernel_time (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : ContinuousAt (fun s ↦ poissonKernel n s x) t := by
  unfold poissonKernel
  fun_prop (disch := positivity)

theorem continuous_heatKernel_space (n : ℕ) (t : ℝ) :
    Continuous (heatKernel n t) := by
  unfold heatKernel
  fun_prop

theorem continuous_poissonKernel_space (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous (poissonKernel n t) := by
  unfold poissonKernel
  have hb : Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ t ^ 2 + ‖x‖ ^ 2) := by
    fun_prop
  exact continuous_const.div
    (hb.rpow_const (p := ((n : ℝ) + 1) / 2) (fun _ ↦ Or.inr (by positivity)))
    (fun x ↦ (Real.rpow_pos_of_pos (by positivity : 0 < t ^ 2 + ‖x‖ ^ 2) _).ne')

/-- A positive lower bound on time gives a uniform bound on the actual heat kernel. -/
theorem heatKernel_le_time_bound (n : ℕ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatKernel n t x ≤ (4 * Real.pi * r) ^ (-(n : ℝ) / 2) := by
  have ht : 0 < t := hr.trans_le hrt
  have hpow : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) ≤
      (4 * Real.pi * r) ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left hrt (by positivity)) (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
  have hexp : Real.exp (-‖x‖ ^ 2 / (4 * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    heatKernel n t x ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ _ := by simpa only [mul_one] using hpow

/-- Positive lower and upper bounds on height give a uniform bound on the Poisson kernel. -/
theorem poissonKernel_le_time_bound (n : ℕ) {r t s : ℝ} (hr : 0 < r)
    (hrt : r ≤ t) (hts : t ≤ s) (x : EuclideanSpace ℝ (Fin n)) :
    poissonKernel n t x ≤
      Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
        s / (r ^ 2) ^ (((n : ℝ) + 1) / 2) := by
  have ht : 0 < t := hr.trans_le hrt
  have hs : 0 < s := ht.trans_le hts
  have hc : 0 < Real.Gamma (((n : ℝ) + 1) / 2) /
      Real.pi ^ (((n : ℝ) + 1) / 2) := by
    exact div_pos (Real.Gamma_pos_of_pos (by positivity)) (by positivity)
  have hden : 0 < (r ^ 2) ^ (((n : ℝ) + 1) / 2) := by positivity
  have hbase : r ^ 2 ≤ t ^ 2 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hpow : (r ^ 2) ^ (((n : ℝ) + 1) / 2) ≤
      (t ^ 2 + ‖x‖ ^ 2) ^ (((n : ℝ) + 1) / 2) :=
    Real.rpow_le_rpow (sq_nonneg _) hbase (by positivity)
  unfold poissonKernel
  calc
    _ ≤ Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
        s / (t ^ 2 + ‖x‖ ^ 2) ^ (((n : ℝ) + 1) / 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hts hc.le) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hc.le hs.le) hden hpow

/-- A locally uniform bound on actual kernels transfers pointwise time continuity to an
integral against any integrable input. -/
theorem continuousAt_integral_mul_of_locally_bounded_kernel {E : Type*}
    [MeasurableSpace E] {μ : Measure E} (K : ℝ → E → ℝ) (f : E → ℝ)
    (hf : Integrable f μ) {t : ℝ}
    (hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (K s) μ)
    (hc : ∀ y, ContinuousAt (fun s ↦ K s y) t)
    (hb : ∃ C : ℝ, ∀ᶠ s in 𝓝 t, ∀ y, ‖K s y‖ ≤ C) :
    ContinuousAt (fun s ↦ ∫ y, K s y * f y ∂μ) t := by
  obtain ⟨C, hC⟩ := hb
  apply tendsto_integral_filter_of_dominated_convergence (fun y ↦ C * ‖f y‖)
  · filter_upwards [hm] with s hs
    exact hs.mul hf.aestronglyMeasurable
  · filter_upwards [hC] with s hs
    exact Eventually.of_forall fun y ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hs y) (norm_nonneg _)
  · exact hf.norm.const_mul C
  · exact Eventually.of_forall fun y ↦ (hc y).mul_const (f y)

/-- At every positive time and every point, the actual heat pairing with an `L¹` input exists. -/
theorem integrable_heatKernel_mul (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ heatKernel n t (x - y) * f y) := by
  have hk : Continuous (fun y ↦ heatKernel n t (x - y)) :=
    (continuous_heatKernel_space n t).comp (continuous_const.sub continuous_id)
  apply (hf.norm.const_mul ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))).mono'
    (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun y ↦ by
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (heatKernel_pos n ht _)]
    exact mul_le_mul_of_nonneg_right (heatKernel_le_time_bound n ht le_rfl _) (norm_nonneg _)

/-- At every positive height and every point, the actual Poisson pairing with an `L¹` input
exists. -/
theorem integrable_poissonKernel_mul (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ poissonKernel n t (x - y) * f y) := by
  let C := Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
    t / (t ^ 2) ^ (((n : ℝ) + 1) / 2)
  have hk : Continuous (fun y ↦ poissonKernel n t (x - y)) :=
    (continuous_poissonKernel_space n ht).comp (continuous_const.sub continuous_id)
  apply (hf.norm.const_mul C).mono'
    (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun y ↦ by
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (poissonKernel_pos n ht _)]
    exact mul_le_mul_of_nonneg_right (poissonKernel_le_time_bound n ht le_rfl le_rfl _)
      (norm_nonneg _)

/-- The ordinary heat convolution of an integrable input is continuous at every positive time
at every spatial point. -/
theorem continuousAt_heatConvolution {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun s ↦ heatConvolution s f x) t := by
  have hnear : ∀ᶠ s in 𝓝 t, t / 2 < s := Ioi_mem_nhds (by linarith)
  apply continuousAt_integral_mul_of_locally_bounded_kernel
    (fun s y ↦ heatKernel n s (x - y)) f hf
  · filter_upwards [hnear] with s hs
    exact ((continuous_heatKernel_space n s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact fun y ↦ continuousAt_heatKernel_time n ht (x - y)
  · refine ⟨(4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2), ?_⟩
    filter_upwards [hnear] with s hs
    intro y
    rw [Real.norm_eq_abs, abs_of_pos (heatKernel_pos n (by linarith) _)]
    exact heatKernel_le_time_bound n (by linarith) hs.le _

/-- The ordinary Poisson convolution of an integrable input is continuous at every positive
height at every spatial point. -/
theorem continuousAt_poissonConvolution {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun s ↦ poissonConvolution s f x) t := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo (t / 2) (2 * t) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  apply continuousAt_integral_mul_of_locally_bounded_kernel
    (fun s y ↦ poissonKernel n s (x - y)) f hf
  · filter_upwards [hnear] with s hs
    exact ((continuous_poissonKernel_space n (by linarith [hs.1])).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact fun y ↦ continuousAt_poissonKernel_time n ht (x - y)
  · refine ⟨Real.Gamma (((n : ℝ) + 1) / 2) / Real.pi ^ (((n : ℝ) + 1) / 2) *
      (2 * t) / ((t / 2) ^ 2) ^ (((n : ℝ) + 1) / 2), ?_⟩
    filter_upwards [hnear] with s hs
    intro y
    rw [Real.norm_eq_abs, abs_of_pos (poissonKernel_pos n (by linarith [hs.1]) _)]
    exact poissonKernel_le_time_bound n (by linarith) hs.1.le hs.2.le _

end PartialBalayage
