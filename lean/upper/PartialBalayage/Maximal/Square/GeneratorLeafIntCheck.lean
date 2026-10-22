/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.GeneratorIntData

/-!
# The leaf check with integer tensor sums

The sixteen tensor intervals and the approximation error of a leaf are computed from the integer
cell rows and the integer Taylor rows in one pass over the 145 knots, and divided once. The result
is the same rational lower bound as `GeneratorLeafData.sparseLowerBound`
(`GeneratorLeafData.intLowerBound_eq`), so a kernel check of the integer form proves the leaf.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The Taylor rows of the 145 knots of a coordinate in cell `c`, in knot order: the knots up to
the cell use family A from the cell outward, the others the reflected family B. -/
def intTaylorFamily (A B : List IntTaylorRow) (c : ℕ) : List IntTaylorRow :=
  (A.take (c + 73)).reverse ++ (B.take (72 - c)).map IntTaylorRow.refl

private theorem getD_eq_getElem' {α : Type*} (l : List α) (d : α) {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem intTaylorFamily_getD (A B : List IntTaylorRow) (c : ℕ) (hA : A.length = 144)
    (hB : B.length = 72) (hc : c < 72) (k : ℕ) (hk : k < 145) :
    (intTaylorFamily A B c).getD k default =
      if k ≤ c + 72 then A.getD (c + 72 - k) default else (B.getD (k - 73 - c) default).refl := by
  have hlt : (A.take (c + 73)).length = c + 73 := by
    rw [List.length_take, hA]; omega
  have hlr : (A.take (c + 73)).reverse.length = c + 73 := by rw [List.length_reverse, hlt]
  unfold intTaylorFamily
  by_cases h : k ≤ c + 72
  · rw [if_pos h]
    have h1 : k < (A.take (c + 73)).reverse.length := by rw [hlr]; omega
    have h2 : c + 72 - k < A.length := by rw [hA]; omega
    have h3 : (A.take (c + 73)).length - 1 - k < (A.take (c + 73)).length := by rw [hlt]; omega
    rw [getD_eq_getElem' _ _ (by simp only [List.length_append]; omega),
      getD_eq_getElem' _ _ h2, List.getElem_append_left h1, List.getElem_reverse,
      List.getElem_take]
    congr 1
    rw [hlt]
    omega
  · rw [if_neg h]
    have h1 : (A.take (c + 73)).reverse.length ≤ k := by rw [hlr]; omega
    have h2 : k - 73 - c < B.length := by rw [hB]; omega
    have h4 : k < ((A.take (c + 73)).reverse ++ (B.take (72 - c)).map IntTaylorRow.refl).length := by
      simp only [List.length_append, List.length_map, List.length_take, hlr, hB]; omega
    rw [getD_eq_getElem' _ _ h4, getD_eq_getElem' _ _ h2, List.getElem_append_right h1,
      List.getElem_map, List.getElem_take]
    congr 2
    rw [hlr]
    omega

namespace GeneratorCoordinateData

/-- The integer coefficient rows of the cell. -/
def intCells (D : GeneratorCoordinateData) : List IntCellRow := generatorCellIntRows D.cellIndex

/-- The integer rows of the cubic re-expanded at the coordinate midpoint. -/
def intCentered (D : GeneratorCoordinateData) : List IntCellRow :=
  D.intCells.map (·.centered (2 * shapeIndex D.shape + 1) (shapeDepth D.shape + 1))

/-- The integer Bernstein bounds of the cubic on the coordinate interval. -/
def intBounds (D : GeneratorCoordinateData) : List ℤ :=
  D.intCells.map (·.bound (shapeIndex D.shape) (shapeDepth D.shape))

/-- The integer Taylor rows of the 145 knots. -/
def intTaylor (D : GeneratorCoordinateData) : List IntTaylorRow :=
  intTaylorFamily (generatorTaylorIntA D.shape) (generatorTaylorIntB D.shape) D.cellIndex.val

/-- The denominator of `intCentered`. -/
def centeredDen (D : GeneratorCoordinateData) : ℕ := cellIntDen * 2 ^ (3 * (shapeDepth D.shape + 1))

/-- The denominator of `intBounds`. -/
def boundDen (D : GeneratorCoordinateData) : ℕ := 3 * cellIntDen * 2 ^ (3 * shapeDepth D.shape)

theorem intCells_length (D : GeneratorCoordinateData) : D.intCells.length = 145 :=
  generatorCellIntRows_length D.cellIndex

theorem intTaylor_length (D : GeneratorCoordinateData) : D.intTaylor.length = 145 := by
  have hA := generatorTaylorIntA_length D.shape
  have hB := generatorTaylorIntB_length D.shape
  have hc := D.cellIndex.isLt
  simp only [intTaylor, intTaylorFamily, List.length_append, List.length_reverse,
    List.length_take, List.length_map, hA, hB]
  omega

theorem centeredDen_pos (D : GeneratorCoordinateData) : (0 : ℚ) < D.centeredDen := by
  unfold centeredDen
  have := cellIntDen_pos
  push_cast
  positivity

theorem boundDen_pos (D : GeneratorCoordinateData) : (0 : ℚ) < D.boundDen := by
  unfold boundDen
  have := cellIntDen_pos
  push_cast
  positivity

theorem cell_spec (D : GeneratorCoordinateData) (k : Fin 145) :
    (D.intCells.getD k.val default).Spec cellIntDen (generatorCellCoefficients D.cellIndex k) :=
  fun j ↦ generatorCellIntRows_spec D.cellIndex k j

private theorem shapeMid_eq (s : Fin generatorShapeCount) :
    shapeLower s + shapeWidth s / 2 =
      ((2 * shapeIndex s + 1 : ℕ) : ℚ) / 2 ^ (shapeDepth s + 1) := by
  unfold shapeLower shapeWidth
  push_cast
  rw [pow_succ]
  field_simp

theorem cubic_centered_eq (D : GeneratorCoordinateData) (k : Fin 145) (j : Fin 4) :
    D.cubic.centered k j = ((D.intCentered.getD k.val default).get j : ℚ) / D.centeredDen := by
  have hlen := D.intCells_length
  have hk : k.val < D.intCells.length := by rw [hlen]; exact k.isLt
  have hget : D.intCentered.getD k.val default =
      (D.intCells.getD k.val default).centered (2 * shapeIndex D.shape + 1)
        (shapeDepth D.shape + 1) := by
    simp only [intCentered, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
  have h := IntCellRow.centered_spec cellIntDen_pos (D.cell_spec k)
    (2 * shapeIndex D.shape + 1) (shapeDepth D.shape + 1) j
  rw [hget]
  simp only [cubic, shapeCubic]
  rw [shapeMid_eq]
  exact h

theorem cubic_bound_eq (D : GeneratorCoordinateData) (k : Fin 145) :
    D.cubic.bound k = (D.intBounds.getD k.val default : ℚ) / D.boundDen := by
  have hlen := D.intCells_length
  have hk : k.val < D.intCells.length := by rw [hlen]; exact k.isLt
  have hget : D.intBounds.getD k.val default =
      (D.intCells.getD k.val default).bound (shapeIndex D.shape) (shapeDepth D.shape) := by
    simp only [intBounds, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
  have h := IntCellRow.bound_spec cellIntDen_pos (D.cell_spec k)
    (shapeIndex D.shape) (shapeDepth D.shape)
  rw [hget]
  simp only [cubic, shapeCubic, boundDen]
  have hl : shapeLower D.shape = (shapeIndex D.shape : ℚ) / 2 ^ shapeDepth D.shape := rfl
  have hw : shapeWidth D.shape = 1 / 2 ^ shapeDepth D.shape := rfl
  rw [hl, hw, h]

theorem powers_spec (D : GeneratorCoordinateData) (k : Fin 145) :
    (D.intTaylor.getD k.val default).Spec taylorIntDen errorIntDen (D.powers k) := by
  have hA := generatorTaylorIntA_length D.shape
  have hB := generatorTaylorIntB_length D.shape
  have hc := D.cellIndex.isLt
  rw [intTaylor, intTaylorFamily_getD _ _ _ hA hB hc k.val k.isLt]
  by_cases hk : k.val ≤ D.cellIndex.val + 72
  · have hneg : D.negative k = false := by
      simp only [negative, decide_eq_false_iff_not, not_lt]
      exact hk
    have hpow : D.powers k = generatorPowerCacheA D.shape ⟨D.cellIndex.val + 72 - k.val, by omega⟩ := by
      simp only [powers, GeneratorPowerTaylorData.signedFamily, hneg, Bool.false_eq_true, ↓reduceIte]
      unfold rootData
      rw [dif_pos hk]
    rw [if_pos hk, hpow]
    exact generatorTaylorIntA_spec D.shape ⟨D.cellIndex.val + 72 - k.val, by omega⟩
  · have hneg : D.negative k = true := by
      simp only [negative, decide_eq_true_eq]
      omega
    have hpow : D.powers k =
        (generatorPowerCacheB D.shape ⟨k.val - 73 - D.cellIndex.val, by omega⟩).reflect := by
      simp only [powers, GeneratorPowerTaylorData.signedFamily, hneg, ↓reduceIte]
      unfold rootData
      rw [dif_neg hk]
    have hcen : 0 < (generatorPowerCacheB D.shape ⟨k.val - 73 - D.cellIndex.val, by omega⟩).center := by
      rw [(generatorPowerCacheB_valid D.shape ⟨k.val - 73 - D.cellIndex.val, by omega⟩).2.1]
      have hm := shapeLower_add_width_le D.shape
      have hw := shapeWidth_pos D.shape
      unfold shapeMid
      have : (0 : ℚ) ≤ ((k.val - 73 - D.cellIndex.val : ℕ) : ℚ) := by positivity
      simp only [Fin.val_mk]
      linarith
    rw [if_neg hk, hpow]
    exact (generatorTaylorIntB_spec D.shape ⟨k.val - 73 - D.cellIndex.val, by omega⟩).refl hcen

end GeneratorCoordinateData

/-- One orientation of a tensor interval, lower endpoint, as an integer sum. -/
def intTensorLo (cs : List IntCellRow) (hs : List IntTaylorRow) (j i : Fin 4) : ℤ :=
  (List.zipWith (fun c h ↦ (intScale (c.get j) (h.lo i) (h.hi i)).1) cs hs).sum

/-- One orientation of a tensor interval, upper endpoint, as an integer sum. -/
def intTensorHi (cs : List IntCellRow) (hs : List IntTaylorRow) (j i : Fin 4) : ℤ :=
  (List.zipWith (fun c h ↦ (intScale (c.get j) (h.lo i) (h.hi i)).2) cs hs).sum

private theorem cast_zipWith_sum {α β : Type*} (g : α → β → ℤ) :
    ∀ (l₁ : List α) (l₂ : List β),
      ((List.zipWith g l₁ l₂).sum : ℚ) = (List.zipWith (fun a b ↦ (g a b : ℚ)) l₁ l₂).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
    simp only [List.zipWith_cons_cons, List.sum_cons, Int.cast_add]
    rw [cast_zipWith_sum g l₁ l₂]

private theorem sum_getD_eq_zipWith {α β : Type*} [Inhabited α] [Inhabited β] (l₁ : List α)
    (l₂ : List β) (h₁ : l₁.length = 145) (h₂ : l₂.length = 145) (f : α → β → ℚ) :
    (∑ k : Fin 145, f (l₁.getD k.val default) (l₂.getD k.val default)) =
      (List.zipWith f l₁ l₂).sum := by
  rw [← sum_fin_eq_zipWith l₁ l₂ h₁ h₂ f]
  apply Finset.sum_congr rfl
  intro k _
  have hk₁ : k.val < l₁.length := by rw [h₁]; exact k.isLt
  have hk₂ : k.val < l₂.length := by rw [h₂]; exact k.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₁, List.getElem?_eq_getElem hk₂,
    Option.getD_some]

/-- The tensor interval of one orientation equals its integer form. -/
theorem tensor_eq_int (X Y : GeneratorCoordinateData) (i j : Fin 4) :
    sparseGeneratorTensorIntervals Finset.univ X.cubic.centered (fun k ↦ (Y.powers k).intervals)
        (i, j) =
      ⟨(intTensorLo X.intCentered Y.intTaylor j i : ℚ) / (X.centeredDen * taylorIntDen),
        (intTensorHi X.intCentered Y.intTaylor j i : ℚ) / (X.centeredDen * taylorIntDen)⟩ := by
  have hterm : ∀ k : Fin 145,
      sparseScaleInterval (X.cubic.centered k j) ((Y.powers k).intervals i) =
        ⟨((intScale ((X.intCentered.getD k.val default).get j) ((Y.intTaylor.getD k.val default).lo i)
            ((Y.intTaylor.getD k.val default).hi i)).1 : ℚ) / (X.centeredDen * taylorIntDen),
          ((intScale ((X.intCentered.getD k.val default).get j) ((Y.intTaylor.getD k.val default).lo i)
            ((Y.intTaylor.getD k.val default).hi i)).2 : ℚ) / (X.centeredDen * taylorIntDen)⟩ := by
    intro k
    rw [X.cubic_centered_eq k j, (Y.powers_spec k).1 i]
    exact sparseScaleInterval_int X.centeredDen_pos taylorIntDen_pos _ _ _
  have hlenC : X.intCentered.length = 145 := by
    simp only [GeneratorCoordinateData.intCentered, List.length_map, X.intCells_length]
  have hlenT := Y.intTaylor_length
  unfold sparseGeneratorTensorIntervals RationalInterval.sum
  simp only [hterm]
  congr 1
  · rw [← Finset.sum_div, intTensorLo, cast_zipWith_sum,
      sum_getD_eq_zipWith _ _ hlenC hlenT (fun c h ↦ ((intScale (c.get j) (h.lo i) (h.hi i)).1 : ℚ))]
  · rw [← Finset.sum_div, intTensorHi, cast_zipWith_sum,
      sum_getD_eq_zipWith _ _ hlenC hlenT (fun c h ↦ ((intScale (c.get j) (h.lo i) (h.hi i)).2 : ℚ))]

/-- One half of the approximation error equals its integer form. -/
theorem error_eq_int (X Y : GeneratorCoordinateData) :
    (∑ k, sparseProduct (X.cubic.bound k) (Y.powers k).error) =
      (((List.zipWith (fun b h ↦ b * h.e) X.intBounds Y.intTaylor).sum : ℤ) : ℚ) /
        (X.boundDen * errorIntDen) := by
  have hlenB : X.intBounds.length = 145 := by
    simp only [GeneratorCoordinateData.intBounds, List.length_map, X.intCells_length]
  have hlenT := Y.intTaylor_length
  have hterm : ∀ k : Fin 145, sparseProduct (X.cubic.bound k) (Y.powers k).error =
      ((X.intBounds.getD k.val default * (Y.intTaylor.getD k.val default).e : ℤ) : ℚ) /
        (X.boundDen * errorIntDen) := by
    intro k
    rw [sparseProduct_eq, X.cubic_bound_eq k, (Y.powers_spec k).2]
    have h1 := X.boundDen_pos
    have h2 := errorIntDen_pos
    push_cast
    field_simp
  simp only [hterm]
  rw [← Finset.sum_div, cast_zipWith_sum,
    sum_getD_eq_zipWith _ _ hlenB hlenT (fun b h ↦ ((b * h.e : ℤ) : ℚ))]

/-- The approximation intervals of a pair of coordinates from the integer tensor sums. -/
def intApproxOf (U V : GeneratorCoordinateData) (p : RectangleIndex) : RationalInterval :=
  ⟨(intTensorLo V.intCentered U.intTaylor p.2 p.1 : ℚ) / (V.centeredDen * taylorIntDen) +
      (intTensorLo U.intCentered V.intTaylor p.1 p.2 : ℚ) / (U.centeredDen * taylorIntDen),
    (intTensorHi V.intCentered U.intTaylor p.2 p.1 : ℚ) / (V.centeredDen * taylorIntDen) +
      (intTensorHi U.intCentered V.intTaylor p.1 p.2 : ℚ) / (U.centeredDen * taylorIntDen)⟩

/-- The approximation error of a pair of coordinates from the integer sums. -/
def intErrorOf (U V : GeneratorCoordinateData) : ℚ :=
  (((List.zipWith (fun b h ↦ b * h.e) V.intBounds U.intTaylor).sum : ℤ) : ℚ) /
      (V.boundDen * errorIntDen) +
    (((List.zipWith (fun b h ↦ b * h.e) U.intBounds V.intTaylor).sum : ℤ) : ℚ) /
      (U.boundDen * errorIntDen)

theorem intApproxOf_eq (U V : GeneratorCoordinateData) (p : RectangleIndex) :
    sparseGeneratorApproximationIntervals U.cubic V.cubic U.powers V.powers p = intApproxOf U V p := by
  unfold sparseGeneratorApproximationIntervals
  rw [show p = (p.1, p.2) from rfl, tensor_eq_int V U p.1 p.2, tensor_eq_int U V p.2 p.1]
  rfl

theorem intErrorOf_eq (U V : GeneratorCoordinateData) :
    sparseGeneratorApproximationError U.cubic V.cubic U.powers V.powers = intErrorOf U V := by
  unfold sparseGeneratorApproximationError intErrorOf
  rw [error_eq_int V U, error_eq_int U V]

namespace GeneratorLeafData

/-- The leaf lower bound computed with integer tensor sums. -/
def intLowerBound (D : GeneratorLeafData) : ℚ :=
  bernsteinIntervalLower
      (fun p ↦ (splineGeneratorFactorInterval.nonnegMul (intApproxOf D.coordinateU D.coordinateV p)).add
        (D.fastRadialIntervals p)) D.rectangle.radius -
    splineGeneratorFactorInterval.upper * intErrorOf D.coordinateU D.coordinateV

/-- The integer form computes exactly the sparse lower bound. -/
theorem intLowerBound_eq (D : GeneratorLeafData) : D.intLowerBound = D.sparseLowerBound := by
  unfold intLowerBound sparseLowerBound sparseGeneratorCombinedIntervals
  rw [intErrorOf_eq]
  congr 2
  funext p
  rw [intApproxOf_eq]

end GeneratorLeafData

end PartialBalayage.Maximal.Square
