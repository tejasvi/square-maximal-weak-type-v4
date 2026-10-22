/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
Modified by Tejasvi Singh Tomar, 2026: derived from `CenteredMaximal/Lattice/Smear.lean`. The atoms
are those of an arbitrary periodic configuration (`Config`), the kept atoms are those of the period
cells `(a, b)` with `|a|, |b| ≤ N + 1`, and the level bound uses witness sides `L ≥ ell` with
smearing squares of side `ε * ell`.
-/
module

public import CenteredMaximal.Basic
public import CenteredMaximal.Periodic.Witness
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# Smearing the periodic configuration into an integrable function

The configuration is truncated to the atoms `atomBox N` and each atom of mass `m` at `p` is replaced
by `m δ⁻²` times the indicator of the closed square of side `δ` centred at `p`. The resulting
function `smeared N δ` is integrable, with `‖smeared N δ‖₁` equal to the total mass of the kept
atoms.

If `(L, A)` witnesses level one at `z` and every atom of `A` is kept, the square of side `L + δ`
centred at `z` contains the smeared mass of every atom of `A`, so the maximal function at `z` is at
least `L² / (L + δ)²`. With `δ = ε * ell` and `L ≥ ell` this is at least `(1 + ε)⁻² > 1 - 2ε`
(`lt_maximalFunction_smeared`). This is the device of Aldaz (2000, Lemma 1.1), with weighted atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Finset
open scoped ENNReal

namespace CenteredMaximal.Periodic.Config

variable (c : Config)

/-- The position `(ax i + a · px, ay i + b · py)` of the atom with index `(i, a, b)`. -/
def atom (p : ℕ × ℤ × ℤ) : Fin 2 → ℝ := ![c.ax p.1 + p.2.1 * c.px, c.ay p.1 + p.2.2 * c.py]

/-- The atoms kept at scale `N`: the atoms of the period cells `(a, b)` with `|a|, |b| ≤ N + 1`. -/
def atomBox (N : ℕ) : Finset (ℕ × ℤ × ℤ) :=
  range c.n ×ˢ (Icc (-(N : ℤ) - 1) (N + 1) ×ˢ Icc (-(N : ℤ) - 1) (N + 1))

/-- The mass of a period cell. -/
def cellMass : ℝ := ∑ i ∈ range c.n, c.am i

/-- The truncated configuration with each atom smeared over the closed square of side `δ`. -/
def smeared (N : ℕ) (δ : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  ∑ p ∈ c.atomBox N, c.mass p / δ ^ 2 * (closedBall (c.atom p) (δ / 2)).indicator 1 z

theorem smeared_nonneg (N : ℕ) (δ : ℝ) (z : Fin 2 → ℝ) : 0 ≤ c.smeared N δ z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (div_nonneg (c.mass_nonneg _) (sq_nonneg _))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem integrable_smeared (N : ℕ) (δ : ℝ) : Integrable (c.smeared N δ) := by
  refine integrable_finsetSum _ fun p _ => Integrable.const_mul ?_ _
  exact (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)

/-- The atoms of `atomBox N` carry total mass `(2N + 3)²` times the mass of a period cell: the kept
atoms are the atoms of `(2N + 3)²` period cells. -/
theorem sum_mass_atomBox (N : ℕ) :
    ∑ p ∈ c.atomBox N, c.mass p = (2 * N + 3) ^ 2 * c.cellMass := by
  have hcard : #(Icc (-(N : ℤ) - 1) (N + 1)) = 2 * N + 3 := by grind [Int.card_Icc]
  simp only [atomBox, mass, sum_product, sum_const, card_product, hcard, nsmul_eq_mul, cellMass]
  rw [← Finset.mul_sum]
  push_cast
  ring

theorem ofReal_mul_indicator_one {s : Set (Fin 2 → ℝ)} (a : ℝ) (z : Fin 2 → ℝ) :
    ENNReal.ofReal (a * s.indicator 1 z) = s.indicator (fun _ => ENNReal.ofReal a) z := by
  by_cases hz : z ∈ s <;> simp [hz]

theorem enorm_smeared (N : ℕ) (δ : ℝ) (z : Fin 2 → ℝ) :
    ‖c.smeared N δ z‖ₑ = ∑ p ∈ c.atomBox N, (closedBall (c.atom p) (δ / 2)).indicator
      (fun _ => ENNReal.ofReal (c.mass p / δ ^ 2)) z := by
  rw [Real.enorm_eq_ofReal (c.smeared_nonneg N δ z), smeared, ENNReal.ofReal_sum_of_nonneg]
  · simp_rw [ofReal_mul_indicator_one]
  · exact fun _ _ => mul_nonneg (div_nonneg (c.mass_nonneg _) (sq_nonneg _))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- A smeared atom has integral equal to its mass. -/
theorem ofReal_div_sq_mul_volume {δ : ℝ} (hδ : 0 < δ) (p : ℕ × ℤ × ℤ) :
    ENNReal.ofReal (c.mass p / δ ^ 2) * volume (closedBall (c.atom p) (δ / 2)) =
      ENNReal.ofReal (c.mass p) := by
  rw [volume_closedBall_eq _ (by positivity), ← ENNReal.ofReal_mul
    (div_nonneg (c.mass_nonneg _) (sq_nonneg _))]
  congr 1
  field_simp

theorem lintegral_smeared (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ z, ‖c.smeared N δ z‖ₑ = ENNReal.ofReal (∑ p ∈ c.atomBox N, c.mass p) := by
  simp_rw [enorm_smeared]
  rw [lintegral_finsetSum _ fun _ _ => measurable_const.indicator measurableSet_closedBall,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => c.mass_nonneg _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lintegral_indicator_const measurableSet_closedBall, c.ofReal_div_sq_mul_volume hδ]

variable {c}

private theorem IsWitness.closedBall_atom_subset_closedBall {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℕ × ℤ × ℤ)} (hw : c.IsWitness (z 0) (z 1) L A) (δ : ℝ) {p : ℕ × ℤ × ℤ}
    (hp : p ∈ A) :
    closedBall (c.atom p) (δ / 2) ⊆ closedBall z ((L + δ) / 2) := by
  -- every atom of a witness lies within `L / 2` of `z` in the sup metric
  have : dist (c.atom p) z ≤ L / 2 := by
    rw [dist_pi_le_iff', Fin.forall_fin_two]
    simpa [atom, Real.dist_eq] using hw.2.2 p hp
  exact closedBall_subset_closedBall' (by linarith)

/-- If `(L, A)` witnesses level one at `z` and `atomBox N` keeps every atom of `A`, then the closed
square of side `L + δ` centred at `z` (a `closedBall` in the sup metric) carries smeared mass at
least `L ^ 2`. Unlike `lintegral_smeared`, which integrates over the whole plane, this bounds the
mass inside a single square, as `lt_maximalFunction_smeared` needs. -/
theorem ofReal_sq_le_setLIntegral_smeared {N : ℕ} {δ : ℝ} (hδ : 0 < δ) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℕ × ℤ × ℤ)} (hA : A ⊆ c.atomBox N) (hw : c.IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (L ^ 2) ≤ ∫⁻ y in closedBall z ((L + δ) / 2), ‖c.smeared N δ y‖ₑ :=
  calc ENNReal.ofReal (L ^ 2) ≤ ∑ p ∈ A, ENNReal.ofReal (c.mass p) :=
        (ENNReal.ofReal_le_ofReal hw.2.1).trans_eq
          (ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ c.mass_nonneg _)
    _ = ∫⁻ y in closedBall z ((L + δ) / 2), ∑ p ∈ A, (closedBall (c.atom p) (δ / 2)).indicator
          (fun _ ↦ ENNReal.ofReal (c.mass p / δ ^ 2)) y := by
        -- each smeared atom of `A` lies inside the square, so it contributes its whole mass
        rw [lintegral_finsetSum _ fun _ _ ↦ measurable_const.indicator measurableSet_closedBall]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_eq_self _ (hw.closedBall_atom_subset_closedBall δ hp),
          c.ofReal_div_sq_mul_volume hδ]
    _ ≤ _ := lintegral_mono fun y ↦ (sum_le_sum_of_subset hA).trans_eq (c.enorm_smeared N δ y).symm

/-- If `(L, A)` witnesses level one at `z` and `atomBox N` keeps every atom of `A`, then the maximal
function of `smeared N (ε * ell)` at `z` exceeds `1 - 2ε`. The bound is uniform in `N` and in the
witness, so it holds at every point that has some witness inside `atomBox N`. Compare
`ofReal_sq_le_setLIntegral_smeared`, which bounds the mass of the square of side `L + δ` rather than
the maximal function. -/
theorem lt_maximalFunction_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℕ × ℤ × ℤ)} (hA : A ⊆ c.atomBox N) (hw : c.IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (1 - 2 * ε) < maximalFunction (c.smeared N (ε * c.ell)) z := by
  have hℓ : 0 < c.ell := c.ell_pos
  have hL : c.ell ≤ L := hw.1
  have hL₀ : 0 < L := hℓ.trans_le hL
  have hδ : 0 < ε * c.ell := mul_pos hε hℓ
  have hr : 0 < (L + ε * c.ell) / 2 := by positivity
  refine lt_of_lt_of_le ?_ (le_maximalFunction _ z hr)
  rw [volume_closedBall_eq z hr.le]
  calc ENNReal.ofReal (1 - 2 * ε) < ENNReal.ofReal (L ^ 2 / (L + ε * c.ell) ^ 2) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ (by positivity)]
        -- `L² - (1 - 2ε)(L + εℓ)² = 2εL(L - ℓ) + ε²ℓ(4L - ℓ) + 2ε³ℓ²` is positive since `ℓ ≤ L`
        have h₁ : 0 ≤ 2 * ε * L * (L - c.ell) :=
          mul_nonneg (by positivity) (sub_nonneg.2 hL)
        have h₂ : 0 < ε ^ 2 * c.ell * (4 * L - c.ell) := by
          have : 0 < 4 * L - c.ell := by linarith
          positivity
        have h₃ : 0 < 2 * ε ^ 3 * c.ell ^ 2 := by positivity
        nlinarith [h₁, h₂, h₃]
    _ = (ENNReal.ofReal ((2 * ((L + ε * c.ell) / 2)) ^ 2))⁻¹ * ENNReal.ofReal (L ^ 2) := by
        rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.div_eq_inv_mul]
    _ ≤ _ := mul_le_mul_right (ofReal_sq_le_setLIntegral_smeared hδ hA hw) _

end CenteredMaximal.Periodic.Config
