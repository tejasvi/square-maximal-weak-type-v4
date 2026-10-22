/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
Modified by Tejasvi Singh Tomar, 2026: derived from `CenteredMaximal/Lattice/LowerBound.lean`. The
period cell is `[0, px) × [0, py)` of an arbitrary periodic configuration (`Config`), the witnessed
set `G` is a hypothesis (with an area bound `a`) instead of the explicit set `cell \ slots`, and the
conclusion is `a / cellMass ≤ C` for every weak type bound `C`.
-/
module

public import CenteredMaximal.Periodic.Smear

/-!
# Lower bounds from periodic configurations

Let `G` be a measurable subset of the period cell `cell = [0, px) × [0, py)` such that every point
of `G` has a level-one witness using atoms of the period cell `(0, 0)` and of its eight neighbours.
The `(2N + 1)²` translates `copy G k l`, `|k|, |l| ≤ N`, are disjoint and lie in the level set of
`smeared N (ε * ell)` at height `1 - 2ε`, while `‖smeared N (ε * ell)‖₁ = (2N + 3)² cellMass`. With
`ε = 1 / (2N + 3)` a weak type bound `C` therefore satisfies
`C ≥ ((2N + 1)/(2N + 3))³ |G| / cellMass`, and `N → ∞` gives `C ≥ |G| / cellMass`
(`ofReal_div_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Periodic.Config

variable (c : Config)

/-- The period cell `[0, px) × [0, py)`. -/
def cell : Set (Fin 2 → ℝ) :=
  univ.pi fun i => Ico 0 (![c.px, c.py] i)

/-- The period vector of the cell with index `(k, l)`. -/
def shift (k l : ℤ) : Fin 2 → ℝ := ![k * c.px, l * c.py]

/-- The translate of `G` into the cell with index `(k, l)`. -/
def copy (G : Set (Fin 2 → ℝ)) (k l : ℤ) : Set (Fin 2 → ℝ) := (fun z => -c.shift k l + z) ⁻¹' G

theorem mem_cell {z : Fin 2 → ℝ} :
    z ∈ c.cell ↔ (0 ≤ z 0 ∧ z 0 < c.px) ∧ (0 ≤ z 1 ∧ z 1 < c.py) := by
  simp [cell, Fin.forall_fin_two]

theorem volume_copy (G : Set (Fin 2 → ℝ)) (k l : ℤ) : volume (c.copy G k l) = volume G :=
  measure_preimage_add volume (-c.shift k l) G

theorem measurableSet_copy {G : Set (Fin 2 → ℝ)} (hG : MeasurableSet G) (k l : ℤ) :
    MeasurableSet (c.copy G k l) :=
  hG.preimage (measurable_const_add _)

theorem mem_copy {G : Set (Fin 2 → ℝ)} {k l : ℤ} {z : Fin 2 → ℝ} :
    z ∈ c.copy G k l ↔ ![z 0 - k * c.px, z 1 - l * c.py] ∈ G := by
  have : -c.shift k l + z = ![z 0 - k * c.px, z 1 - l * c.py] := by
    ext i
    fin_cases i <;> simp [shift] <;> ring
  rw [copy, Set.mem_preimage, this]

variable {c}

/-- The translates `copy G k l`, `(k, l) : ℤ × ℤ`, of a subset `G` of the period cell are pairwise
disjoint. The index set is all of `ℤ × ℤ`: restrict it to a finite box with
`Set.PairwiseDisjoint.subset` before adding up volumes with `measure_biUnion_finset`, as
`ofReal_le_volume_levelSet` does. -/
theorem pairwiseDisjoint_copy {G : Set (Fin 2 → ℝ)} (hG : G ⊆ c.cell) :
    (univ : Set (ℤ × ℤ)).PairwiseDisjoint fun p => c.copy G p.1 p.2 := by
  rintro ⟨k, l⟩ - ⟨k', l'⟩ - hne
  refine Set.disjoint_left.2 fun z hz hz' ↦ hne ?_
  have hz₁ := c.mem_cell.1 (hG (c.mem_copy.1 hz))
  have hz₂ := c.mem_cell.1 (hG (c.mem_copy.1 hz'))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hz₁ hz₂
  have hpx := c.px_pos
  have hpy := c.py_pos
  -- distinct integers are at distance at least one, but `z` lying in both half-open cells puts
  -- `k, k'` (in units of `px`) and `l, l'` (in units of `py`) less than one apart
  refine Prod.ext (Int.pairwise_one_le_dist.eq ?_) (Int.pairwise_one_le_dist.eq ?_) <;>
    refine not_le.2 <| (Int.dist_eq _ _).trans_lt <| abs_sub_lt_iff.2 ⟨?_, ?_⟩ <;> nlinarith

/-- Every point `z` of the translate `copy G k l` has a level-one witness `(L, A)` whose atoms lie
in `nearBox k l`, if every point of `G` has one with atoms in `nearBox 0 0`. -/
theorem exists_isWitness_of_mem_copy {G : Set (Fin 2 → ℝ)}
    (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A) {k l : ℤ}
    {z : Fin 2 → ℝ} (hz : z ∈ c.copy G k l) :
    ∃ L A, A ⊆ c.nearBox k l ∧ c.IsWitness (z 0) (z 1) L A := by
  obtain ⟨L, A, hA, hw⟩ := hGw _ (c.mem_copy.1 hz)
  -- translating the witness by `(k, l)` moves it to `z` and its atoms into `nearBox k l`
  refine ⟨L, _, map_shiftIdx_subset_nearBox hA k l, ?_⟩
  simpa using hw.translate k l

/-- For `|k|, |l| ≤ N`, the atoms `nearBox k l` available to a witness in the cell with index
`(k, l)` are kept in `atomBox N`. -/
theorem nearBox_subset_atomBox {N : ℕ} {k l : ℤ} (hk : |k| ≤ N) (hl : |l| ≤ N) :
    c.nearBox k l ⊆ c.atomBox N := by
  intro p hp
  simp only [nearBox, atomBox, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp ⊢
  rw [abs_le] at hk hl
  omega

/-- The level set of `smeared N (ε * ell)` at height `1 - 2ε` has measure at least `(2N + 1)²`
times the lower bound `a` on the area of `G`, for every `ε > 0`: it contains the `(2N + 1)²`
disjoint copies `copy G k l`, `|k|, |l| ≤ N`, of `G`. This is the level-set side of the weak type
inequality in `ofReal_mul_div_le`. -/
theorem ofReal_le_volume_levelSet {G : Set (Fin 2 → ℝ)} (hGm : MeasurableSet G) (hG : G ⊆ c.cell)
    (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A) {a : ℝ}
    (ha : ENNReal.ofReal a ≤ volume G) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((2 * N + 1) ^ 2 * a) ≤
      volume {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (c.smeared N (ε * c.ell)) z} := by
  -- the `(2N + 1)²` indices `(k, l)` with `|k|, |l| ≤ N`
  set S := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hcard : S.card = (2 * N + 1) ^ 2 := by grind [Finset.card_product, Int.card_Icc]
  calc ENNReal.ofReal ((2 * N + 1) ^ 2 * a)
      = S.card • ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_nsmul, hcard, nsmul_eq_mul]
        norm_cast
    -- each copy `copy G k l` is a translate of `G`, so has at least that area
    _ ≤ ∑ p ∈ S, volume (c.copy G p.1 p.2) :=
        S.card_nsmul_le_sum _ _ fun _ _ ↦ ha.trans_eq (c.volume_copy ..).symm
    -- the copies are pairwise disjoint
    _ = volume (⋃ p ∈ S, c.copy G p.1 p.2) :=
        (measure_biUnion_finset ((pairwiseDisjoint_copy hG).subset (subset_univ _))
          fun p _ ↦ c.measurableSet_copy hGm p.1 p.2).symm
    -- every point of a copy has a witness with atoms in `nearBox k l ⊆ atomBox N`, so it lies in
    -- the level set
    _ ≤ _ := measure_mono <| iUnion₂_subset fun p hp z hz ↦ by
        obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_mem_copy hGw hz
        refine lt_maximalFunction_smeared hε (hA.trans <| nearBox_subset_atomBox ?_ ?_) hw <;>
          grind

private theorem ofReal_mul_ofReal_le_of_isWeakTypeBound {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C)
    {G : Set (Fin 2 → ℝ)} (hGm : MeasurableSet G) (hG : G ⊆ c.cell)
    (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A) {a : ℝ}
    (ha : ENNReal.ofReal a ≤ volume G) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (1 - 2 * ε) * ENNReal.ofReal ((2 * N + 1) ^ 2 * a) ≤
      C * ENNReal.ofReal ((2 * N + 3) ^ 2 * c.cellMass) :=
  -- the weak type inequality for `smeared N (ε * ell)` at level `1 - 2ε`, with the level set
  -- bounded below by `ofReal_le_volume_levelSet` and the mass `‖smeared N (ε * ell)‖₁` computed
  (mul_le_mul_right (ofReal_le_volume_levelSet hGm hG hGw ha N hε) _).trans <|
    (hC _ (c.integrable_smeared N _) _).trans <| mul_le_mul_right
      ((c.lintegral_smeared N (mul_pos hε c.ell_pos)).trans (by rw [c.sum_mass_atomBox N])).le _

private theorem div_pow_three_mul_div_eq (N : ℕ) {a : ℝ} (hm : 0 < c.cellMass) :
    ((2 * N + 1) / (2 * N + 3)) ^ 3 * (a / c.cellMass) =
    (2 * N + 1) / (2 * N + 3) * ((2 * N + 1) ^ 2 * a) / ((2 * N + 3) ^ 2 * c.cellMass) := by
  have : (0 : ℝ) < 2 * N + 3 := by positivity
  field_simp

/-- A weak type bound in dimension two is at least `((2N + 1)/(2N + 3))³ a / cellMass`, for every
`N`. This is the finite-`N` form of `ofReal_div_le`, which lets `N → ∞`. -/
theorem ofReal_mul_div_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) {G : Set (Fin 2 → ℝ)}
    (hGm : MeasurableSet G) (hG : G ⊆ c.cell)
    (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A) {a : ℝ}
    (ha : ENNReal.ofReal a ≤ volume G) (hm : 0 < c.cellMass) (N : ℕ) :
    ENNReal.ofReal (((2 * N + 1) / (2 * N + 3)) ^ 3 * (a / c.cellMass)) ≤ C := by
  -- test the weak type bound on `smeared N (ε * ell)` with `ε = 1 / (2N + 3)`, whose level `1 - 2ε`
  -- is `(2N + 1)/(2N + 3)`, and divide by the mass `(2N + 3)² cellMass`
  have hq : 1 - 2 * (1 / (2 * N + 3)) = ((2 * N + 1) / (2 * N + 3) : ℝ) := by
    field_simp
    ring
  rw [div_pow_three_mul_div_eq N hm,
    ENNReal.ofReal_div_of_pos (mul_pos (by positivity) hm),
    ENNReal.ofReal_mul (by positivity), ← hq]
  exact ENNReal.div_le_of_le_mul
    (ofReal_mul_ofReal_le_of_isWeakTypeBound hC hGm hG hGw ha N (by positivity))

/-- Every weak type bound in dimension two is at least `a / cellMass`, if `a` bounds from below the
area of a measurable subset `G` of the period cell whose points all have level-one witnesses with
atoms in `nearBox 0 0`. `ofReal_mul_div_le` is the weaker bound for a single `N`. -/
theorem ofReal_div_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) {G : Set (Fin 2 → ℝ)}
    (hGm : MeasurableSet G) (hG : G ⊆ c.cell)
    (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A) {a : ℝ}
    (ha : ENNReal.ofReal a ≤ volume G) (hm : 0 < c.cellMass) :
    ENNReal.ofReal (a / c.cellMass) ≤ C := by
  -- the finite-`N` bounds `ofReal_mul_div_le` tend to `a / cellMass`, as `(2N + 1)/(2N + 3) → 1`
  refine le_of_tendsto' (x := atTop) (ENNReal.tendsto_ofReal ?_)
    (ofReal_mul_div_le hC hGm hG hGw ha hm)
  simpa [add_comm] using
    ((tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 3 2 two_ne_zero).pow 3).mul_const
      (a / c.cellMass)

/-- The weak type constant `c₂` is at least `a / cellMass` under the hypotheses of
`ofReal_div_le`. -/
theorem ofReal_div_le_weakTypeConstant {G : Set (Fin 2 → ℝ)} (hGm : MeasurableSet G)
    (hG : G ⊆ c.cell) (hGw : ∀ z ∈ G, ∃ L A, A ⊆ c.nearBox 0 0 ∧ c.IsWitness (z 0) (z 1) L A)
    {a : ℝ} (ha : ENNReal.ofReal a ≤ volume G) (hm : 0 < c.cellMass) :
    ENNReal.ofReal (a / c.cellMass) ≤ weakTypeConstant 2 :=
  le_weakTypeConstant fun _ hC => ofReal_div_le hC hGm hG hGw ha hm

end CenteredMaximal.Periodic.Config
