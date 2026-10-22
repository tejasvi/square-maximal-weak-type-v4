/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafSparseCheck

/-!
# Exact integer forms of the cubic rows and Taylor intervals of a leaf

Rational arithmetic is slow in the kernel because every operation normalizes. The cubic rows of a
leaf are polynomials in the cell coefficients, whose denominators all divide `3 · 2^41`, and in a
dyadic midpoint, so they are integers over a known denominator. The Taylor intervals of the shared
cache are integers over a common denominator as well. This file proves the integer forms of the
cubic rows, the Bernstein bounds, the reflected Taylor intervals and the scaled interval terms; the
leaf check then sums integers and divides once.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The common denominator `3 · 2^41` of all generator cell coefficients. -/
def cellIntDen : ℕ := 6597069766656

theorem cellIntDen_pos : (0 : ℚ) < cellIntDen := by norm_num [cellIntDen]

/-- One knot's four cubic coefficients as integer numerators. -/
structure IntCellRow where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  deriving Inhabited, DecidableEq

namespace IntCellRow

/-- Coefficient `j`. -/
def get (r : IntCellRow) (j : Fin 4) : ℤ :=
  if j.val = 0 then r.c0 else if j.val = 1 then r.c1 else if j.val = 2 then r.c2 else r.c3

@[simp] theorem get_zero (r : IntCellRow) : r.get 0 = r.c0 := rfl
@[simp] theorem get_one (r : IntCellRow) : r.get 1 = r.c1 := rfl
@[simp] theorem get_two (r : IntCellRow) : r.get 2 = r.c2 := rfl
@[simp] theorem get_three (r : IntCellRow) : r.get 3 = r.c3 := rfl

/-- The row lists the cubic `c` over the denominator `D`. -/
def Spec (D : ℕ) (r : IntCellRow) (c : Fin 4 → ℚ) : Prop := ∀ j, c j = (r.get j : ℚ) / D

/-- The cubic re-expanded at the dyadic point `M / 2^e`, as numerators over `D · 2^(3e)`. -/
def centered (r : IntCellRow) (M e : ℕ) : IntCellRow :=
  let m : ℤ := M
  let t : ℤ := 2 ^ e
  ⟨r.c0 * t ^ 3 + r.c1 * m * t ^ 2 + r.c2 * m ^ 2 * t + r.c3 * m ^ 3,
    (r.c1 * t ^ 2 + 2 * r.c2 * m * t + 3 * r.c3 * m ^ 2) * t,
    (r.c2 * t + 3 * r.c3 * m) * t ^ 2,
    r.c3 * t ^ 3⟩

theorem centered_spec {D : ℕ} (hD : (0 : ℚ) < D) {r : IntCellRow} {c : Fin 4 → ℚ}
    (hr : r.Spec D c) (M e : ℕ) :
    (r.centered M e).Spec (D * 2 ^ (3 * e)) (cubicAffineCoefficients c ((M : ℚ) / 2 ^ e) 1) := by
  intro j
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  simp only [get_zero, get_one, get_two, get_three] at h0 h1 h2 h3
  have he : (0 : ℚ) < 2 ^ e := by positivity
  fin_cases j <;>
    simp [cubicAffineCoefficients, centered, get, h0, h1, h2, h3] <;>
    field_simp <;>
    ring

/-- The cubic on `[J / 2^d, (J + 1) / 2^d]` in the variable of the unit interval: numerators
over `D · 2^(3d)`. -/
def affine (r : IntCellRow) (J d : ℕ) : IntCellRow :=
  let L : ℤ := J
  let t : ℤ := 2 ^ d
  ⟨r.c0 * t ^ 3 + r.c1 * L * t ^ 2 + r.c2 * L ^ 2 * t + r.c3 * L ^ 3,
    r.c1 * t ^ 2 + 2 * r.c2 * L * t + 3 * r.c3 * L ^ 2,
    r.c2 * t + 3 * r.c3 * L,
    r.c3⟩

/-- Three times its Bernstein coefficients, numerators over `3 D 2^(3d)`. -/
def bernsteinNum (r : IntCellRow) (J d : ℕ) : IntCellRow :=
  let f := r.affine J d
  ⟨3 * f.c0, 3 * f.c0 + f.c1, 3 * f.c0 + 2 * f.c1 + f.c2, 3 * (f.c0 + f.c1 + f.c2 + f.c3)⟩

/-- The Bernstein bound of the cubic on `[J / 2^d, (J + 1) / 2^d]`, as an integer over
`3 D 2^(3d)`. -/
def bound (r : IntCellRow) (J d : ℕ) : ℤ :=
  let b := r.bernsteinNum J d
  max (max |b.c0| |b.c1|) (max |b.c2| |b.c3|)

private theorem max_div_pos {a b D : ℚ} (hD : 0 < D) : max (a / D) (b / D) = max a b / D := by
  rcases le_total a b with h | h
  · rw [max_eq_right (div_le_div_of_nonneg_right h hD.le), max_eq_right h]
  · rw [max_eq_left (div_le_div_of_nonneg_right h hD.le), max_eq_left h]

theorem bernsteinNum_spec {D : ℕ} (hD : (0 : ℚ) < D) {r : IntCellRow} {c : Fin 4 → ℚ}
    (hr : r.Spec D c) (J d : ℕ) :
    (r.bernsteinNum J d).Spec (3 * D * 2 ^ (3 * d))
      (cubicBernsteinCoefficients (cubicAffineCoefficients c ((J : ℚ) / 2 ^ d) (1 / 2 ^ d))) := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  simp only [get_zero, get_one, get_two, get_three] at h0 h1 h2 h3
  have hd : (0 : ℚ) < 2 ^ d := by positivity
  intro j
  fin_cases j <;>
    simp [cubicBernsteinCoefficients, cubicAffineCoefficients, bernsteinNum, affine, get, h0, h1,
      h2, h3] <;>
    field_simp <;>
    ring

theorem bound_spec {D : ℕ} (hD : (0 : ℚ) < D) {r : IntCellRow} {c : Fin 4 → ℚ}
    (hr : r.Spec D c) (J d : ℕ) :
    bernsteinAbsMax (cubicAffineCoefficients c ((J : ℚ) / 2 ^ d) (1 / 2 ^ d)) =
      (r.bound J d : ℚ) / ((3 * D * 2 ^ (3 * d) : ℕ) : ℚ) := by
  have hQ : (0 : ℚ) < ((3 * D * 2 ^ (3 * d) : ℕ) : ℚ) := by
    have : (0 : ℚ) < 3 * D * 2 ^ (3 * d) := by positivity
    exact_mod_cast this
  have hb := bernsteinNum_spec hD hr J d
  have e0 := hb 0
  have e1 := hb 1
  have e2 := hb 2
  have e3 := hb 3
  simp only [get_zero, get_one, get_two, get_three] at e0 e1 e2 e3
  unfold bernsteinAbsMax bound
  rw [e0, e1, e2, e3, abs_div, abs_div, abs_div, abs_div, abs_of_pos hQ, max_div_pos hQ,
    max_div_pos hQ, max_div_pos hQ]
  push_cast
  rfl

end IntCellRow

/-- One knot's four Taylor intervals and its error, as integer numerators. -/
structure IntTaylorRow where
  lo0 : ℤ
  hi0 : ℤ
  lo1 : ℤ
  hi1 : ℤ
  lo2 : ℤ
  hi2 : ℤ
  lo3 : ℤ
  hi3 : ℤ
  e : ℤ
  deriving Inhabited, DecidableEq

namespace IntTaylorRow

/-- Lower numerator of interval `i`. -/
def lo (R : IntTaylorRow) (i : Fin 4) : ℤ :=
  if i.val = 0 then R.lo0 else if i.val = 1 then R.lo1 else if i.val = 2 then R.lo2 else R.lo3

/-- Upper numerator of interval `i`. -/
def hi (R : IntTaylorRow) (i : Fin 4) : ℤ :=
  if i.val = 0 then R.hi0 else if i.val = 1 then R.hi1 else if i.val = 2 then R.hi2 else R.hi3

/-- The row lists the Taylor intervals of `T` over `DH` and its error over `DE`. -/
def Spec (DH DE : ℕ) (R : IntTaylorRow) (T : GeneratorPowerTaylorData) : Prop :=
  (∀ i, T.intervals i = ⟨(R.lo i : ℚ) / DH, (R.hi i : ℚ) / DH⟩) ∧ T.error = (R.e : ℚ) / DE

/-- The row of the reflected datum: the odd intervals change sign. -/
def refl (R : IntTaylorRow) : IntTaylorRow :=
  ⟨R.lo0, R.hi0, -R.hi1, -R.lo1, R.lo2, R.hi2, -R.hi3, -R.lo3, R.e⟩

private theorem scale_neg (q : ℚ) (I : RationalInterval) :
    I.scale (-q) = ⟨-(I.scale q).upper, -(I.scale q).lower⟩ := by
  unfold RationalInterval.scale
  by_cases h1 : 0 ≤ q <;> by_cases h2 : 0 ≤ -q
  · have hq : q = 0 := le_antisymm (by linarith) h1
    subst hq
    simp
  · simp only [h1, h2, ↓reduceIte, RationalInterval.mk.injEq]
    constructor <;> ring
  · simp only [h1, h2, ↓reduceIte, RationalInterval.mk.injEq]
    constructor <;> ring
  · exact absurd (by linarith : 0 ≤ -q) h2

private theorem sign_reflect (T : GeneratorPowerTaylorData) (hc : 0 < T.center) (a : ℚ) :
    a * rationalCenterSign (-T.center) = -(a * rationalCenterSign T.center) := by
  have hs : rationalCenterSign T.center = 1 := by simp [rationalCenterSign, hc]
  have hs' : rationalCenterSign (-T.center) = -1 := by
    simp [rationalCenterSign, not_lt.mpr (neg_nonpos.mpr hc.le)]
  rw [hs, hs']
  ring

theorem intervals_reflect_zero (T : GeneratorPowerTaylorData) :
    T.reflect.intervals 0 = T.intervals 0 := by
  unfold GeneratorPowerTaylorData.intervals
  by_cases hb : T.boundary = true
  · simp [hb, GeneratorPowerTaylorData.reflect]
  · simp [hb, absPowerTaylorIntervals, GeneratorPowerTaylorData.reflect]

theorem intervals_reflect_two (T : GeneratorPowerTaylorData) :
    T.reflect.intervals 2 = T.intervals 2 := by
  unfold GeneratorPowerTaylorData.intervals
  by_cases hb : T.boundary = true
  · simp [hb, GeneratorPowerTaylorData.reflect]
  · simp [hb, absPowerTaylorIntervals, GeneratorPowerTaylorData.reflect]

theorem intervals_reflect_one (T : GeneratorPowerTaylorData) (hc : 0 < T.center) :
    T.reflect.intervals 1 = ⟨-(T.intervals 1).upper, -(T.intervals 1).lower⟩ := by
  unfold GeneratorPowerTaylorData.intervals
  by_cases hb : T.boundary = true
  · have hb' : T.reflect.boundary = true := hb
    simp only [hb, hb', ↓reduceIte, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero]
    rw [show T.reflect.powers = T.powers from rfl, GeneratorPowerTaylorData.reflect_center,
      sign_reflect T hc, scale_neg]
  · have hb' : ¬ T.reflect.boundary = true := hb
    simp only [hb, hb', Bool.false_eq_true, ↓reduceIte, absPowerTaylorIntervals, Fin.isValue,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [show T.reflect.powers = T.powers from rfl, GeneratorPowerTaylorData.reflect_center,
      sign_reflect T hc, scale_neg]

theorem intervals_reflect_three (T : GeneratorPowerTaylorData) (hc : 0 < T.center) :
    T.reflect.intervals 3 = ⟨-(T.intervals 3).upper, -(T.intervals 3).lower⟩ := by
  unfold GeneratorPowerTaylorData.intervals
  by_cases hb : T.boundary = true
  · have hb' : T.reflect.boundary = true := hb
    simp [hb, hb', RationalInterval.point]
  · have hb' : ¬ T.reflect.boundary = true := hb
    simp only [hb, hb', Bool.false_eq_true, ↓reduceIte, absPowerTaylorIntervals, Fin.isValue,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show T.reflect.powers = T.powers from rfl, GeneratorPowerTaylorData.reflect_center,
      sign_reflect T hc, scale_neg]

theorem Spec.refl {DH DE : ℕ} {R : IntTaylorRow} {T : GeneratorPowerTaylorData}
    (h : R.Spec DH DE T) (hc : 0 < T.center) : R.refl.Spec DH DE T.reflect := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i
    · show T.reflect.intervals 0 = ⟨(R.refl.lo 0 : ℚ) / DH, (R.refl.hi 0 : ℚ) / DH⟩
      rw [intervals_reflect_zero, h.1 0]
      rfl
    · show T.reflect.intervals 1 = ⟨(R.refl.lo 1 : ℚ) / DH, (R.refl.hi 1 : ℚ) / DH⟩
      rw [intervals_reflect_one T hc, h.1 1]
      simp only [lo, hi, IntTaylorRow.refl, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte,
        Int.cast_neg, neg_div]
    · show T.reflect.intervals 2 = ⟨(R.refl.lo 2 : ℚ) / DH, (R.refl.hi 2 : ℚ) / DH⟩
      rw [intervals_reflect_two, h.1 2]
      rfl
    · show T.reflect.intervals 3 = ⟨(R.refl.lo 3 : ℚ) / DH, (R.refl.hi 3 : ℚ) / DH⟩
      rw [intervals_reflect_three T hc, h.1 3]
      simp only [lo, hi, IntTaylorRow.refl, Fin.isValue, show ((3 : Fin 4) : ℕ) = 3 from rfl,
        show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
        ↓reduceIte, Int.cast_neg, neg_div]
  · rw [show T.reflect.error = T.error from rfl, h.2]
    rfl

end IntTaylorRow

/-- The sign-split product of an integer and an integer interval. -/
def intScale (n : ℤ) (a b : ℤ) : ℤ × ℤ := if 0 ≤ n then (n * a, n * b) else (n * b, n * a)

theorem sparseScaleInterval_int {Dc DH : ℕ} (hc : (0 : ℚ) < Dc) (hh : (0 : ℚ) < DH) (n a b : ℤ) :
    sparseScaleInterval ((n : ℚ) / Dc) ⟨(a : ℚ) / DH, (b : ℚ) / DH⟩ =
      ⟨((intScale n a b).1 : ℚ) / (Dc * DH), ((intScale n a b).2 : ℚ) / (Dc * DH)⟩ := by
  rw [sparseScaleInterval_eq]
  unfold RationalInterval.scale intScale
  by_cases hn : 0 ≤ n
  · have hq : (0 : ℚ) ≤ (n : ℚ) / Dc := div_nonneg (by exact_mod_cast hn) hc.le
    simp only [hq, hn, ↓reduceIte]
    congr 1 <;> push_cast <;> field_simp
  · have hq : ¬ ((0 : ℚ) ≤ (n : ℚ) / Dc) := by
      rw [div_nonneg_iff]
      push Not
      exact ⟨fun h ↦ absurd (by exact_mod_cast h) hn, fun _ ↦ hc⟩
    simp only [hq, hn, ↓reduceIte]
    congr 1 <;> push_cast <;> field_simp

/-- A sum over `Fin n` of terms read from two lists of length `n`. -/
theorem sum_fin_eq_zipWith {α β : Type*} {n : ℕ} (l₁ : List α) (l₂ : List β) (h₁ : l₁.length = n)
    (h₂ : l₂.length = n) (f : α → β → ℚ) :
    (∑ k : Fin n, f (l₁[k.val]'(by rw [h₁]; exact k.isLt)) (l₂[k.val]'(by rw [h₂]; exact k.isLt))) =
      (List.zipWith f l₁ l₂).sum := by
  subst h₁
  have hz : List.zipWith f l₁ l₂ =
      List.ofFn (fun k : Fin l₁.length ↦ f (l₁[k.val]) (l₂[k.val]'(by rw [h₂]; exact k.isLt))) := by
    apply List.ext_getElem
    · simp [h₂]
    · intro i hi₁ hi₂
      simp
  rw [hz, List.sum_ofFn]

end PartialBalayage.Maximal.Square
