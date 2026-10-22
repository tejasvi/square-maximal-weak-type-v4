/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
Modified by Tejasvi Singh Tomar, 2026: derived from `CenteredMaximal/Lattice/Witness.lean`. The
two-mass lattice is replaced by an arbitrary periodic configuration of point masses (`Config`), the
witness side is bounded below by `ell` instead of `1`, and the reflections and the six explicit
witnesses are removed (witnesses now come from a checked certificate).
-/
module

public import CenteredMaximal.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Witnesses for a periodic configuration of point masses

A configuration has `n` atoms per period cell: atom `i` sits at `(ax i, ay i)` and has mass `am i`,
and it is repeated with periods `px` and `py`. The atom with index `(i, a, b) ∈ ℕ × ℤ × ℤ` sits at
`(ax i + a · px, ay i + b · py)` and has mass `am i`. A *witness* for the point `(x, y)` is a side
`L ≥ ell` and a finite set `A` of atoms, all within sup-distance `L/2` of `(x, y)`, of total mass at
least `L²`: the closed square of side `L` centred at `(x, y)` then has average at least `1`.

Translations by the periods preserve the atom masses, so they transport witnesses from the period
cell with index `(0, 0)` to the cell with index `(k, l)` (`IsWitness.translate`).
-/

@[expose] public section

noncomputable section

open Finset

namespace CenteredMaximal.Periodic

/-- A periodic configuration of point masses: `n` atoms per period cell, atom `i` at `(ax i, ay i)`
with mass `am i`, repeated with periods `px` and `py`. Witness sides are at least `ell > 0`. -/
structure Config where
  /-- The horizontal period. -/
  px : ℝ
  /-- The vertical period. -/
  py : ℝ
  /-- The number of atoms in a period cell. -/
  n : ℕ
  /-- The first coordinate of atom `i`. -/
  ax : ℕ → ℝ
  /-- The second coordinate of atom `i`. -/
  ay : ℕ → ℝ
  /-- The mass of atom `i`. -/
  am : ℕ → ℝ
  /-- The least side of a witness square. -/
  ell : ℝ
  px_pos : 0 < px
  py_pos : 0 < py
  am_nonneg : ∀ i, 0 ≤ am i
  ell_pos : 0 < ell

namespace Config

variable (c : Config)

/-- The mass of the atom with index `(i, a, b)`: the mass `am i` of atom `i` of the period cell. -/
def mass (p : ℕ × ℤ × ℤ) : ℝ := c.am p.1

/-- `(L, A)` witnesses level one at `(x, y)`: `L ≥ ell`, the atoms of `A` have total mass at least
`L²`, and every atom of `A` lies in the closed square of side `L` centred at `(x, y)`. -/
def IsWitness (x y L : ℝ) (A : Finset (ℕ × ℤ × ℤ)) : Prop :=
  c.ell ≤ L ∧ L ^ 2 ≤ ∑ p ∈ A, c.mass p ∧
    ∀ p ∈ A, |c.ax p.1 + p.2.1 * c.px - x| ≤ L / 2 ∧ |c.ay p.1 + p.2.2 * c.py - y| ≤ L / 2

/-- The atoms that a witness for a point of the period cell with index `(k, l)` may use: atoms of
the cell `(k, l)` and of its eight neighbours. -/
def nearBox (k l : ℤ) : Finset (ℕ × ℤ × ℤ) :=
  range c.n ×ˢ (Icc (k - 1) (k + 1) ×ˢ Icc (l - 1) (l + 1))

/-- The shift of atom indices by `(k, l)` period cells. -/
def shiftIdx (k l : ℤ) : ℕ × ℤ × ℤ ↪ ℕ × ℤ × ℤ :=
  ⟨fun p ↦ (p.1, p.2.1 + k, p.2.2 + l), fun p q h ↦ by
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)⟩

@[simp] theorem shiftIdx_apply (k l : ℤ) (p : ℕ × ℤ × ℤ) :
    shiftIdx k l p = (p.1, p.2.1 + k, p.2.2 + l) := rfl

theorem mass_nonneg (p : ℕ × ℤ × ℤ) : 0 ≤ c.mass p := c.am_nonneg p.1

variable {c}

/-- Translating the atoms by `(k, l)` period cells turns a witness for `(x, y)` into a witness for
`(x + k * px, y + l * py)` with the same side; `map_shiftIdx_subset_nearBox` tracks the moved
atoms. -/
theorem IsWitness.translate {x y L : ℝ} {A : Finset (ℕ × ℤ × ℤ)} (hw : c.IsWitness x y L A)
    (k l : ℤ) :
    c.IsWitness (x + k * c.px) (y + l * c.py) L (A.map (shiftIdx k l)) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [shiftIdx_apply, mass] using hm, forall_mem_map.2 fun p hp ↦ ?_⟩
  have h₁ : c.ax p.1 + ((p.2.1 + k : ℤ) : ℝ) * c.px - (x + k * c.px) =
      c.ax p.1 + p.2.1 * c.px - x := by push_cast; ring
  have h₂ : c.ay p.1 + ((p.2.2 + l : ℤ) : ℝ) * c.py - (y + l * c.py) =
      c.ay p.1 + p.2.2 * c.py - y := by push_cast; ring
  simp only [shiftIdx_apply]
  rw [h₁, h₂]
  exact hd p hp

/-- Translating a subset of `nearBox 0 0` by `(k, l)` period cells lands in `nearBox k l`: the
atom-set companion of `IsWitness.translate`. -/
theorem map_shiftIdx_subset_nearBox {A : Finset (ℕ × ℤ × ℤ)} (hA : A ⊆ c.nearBox 0 0) (k l : ℤ) :
    A.map (shiftIdx k l) ⊆ c.nearBox k l := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_map.1 hq
  have := hA hp
  simp only [nearBox, mem_product, mem_range, mem_Icc, shiftIdx_apply] at this ⊢
  omega

end Config

end CenteredMaximal.Periodic
