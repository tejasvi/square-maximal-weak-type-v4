/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: a coordinate datum is now a cell and a shared dyadic shape; its cubic
rows, Bernstein bounds and signed Taylor family are computed from the cell table and the shape-indexed cache, and its
validity is proved once for all data (145 signed knots, offset 72). -/
module

public import PartialBalayage.Maximal.Square.GeneratorCubicIntervalData
public import PartialBalayage.Maximal.Square.GeneratorPowerCache
public import PartialBalayage.Maximal.Square.GeneratorPowerReflection
public import PartialBalayage.Maximal.Square.GeneratorFiniteKnots

/-!
# Genuine coordinate data with shared signed power bounds

The cubic rows and interval bounds are computed from the actual spline
coefficient matrix. The signed Taylor centers come from the proved shared
cache, whose recorded centers identify the true coordinate midpoints.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The largest absolute cubic Bernstein coefficient. -/
def bernsteinAbsMax (c : Fin 4 → ℚ) : ℚ :=
  max (max |cubicBernsteinCoefficients c 0| |cubicBernsteinCoefficients c 1|)
    (max |cubicBernsteinCoefficients c 2| |cubicBernsteinCoefficients c 3|)

theorem abs_bernstein_le_bernsteinAbsMax (c : Fin 4 → ℚ) (b : Fin 4) :
    |cubicBernsteinCoefficients c b| ≤ bernsteinAbsMax c := by
  unfold bernsteinAbsMax
  fin_cases b <;> simp

/-- The computed cubic interval datum of a cell and a shape. -/
def shapeCubic (cell : Fin 72) (s : Fin generatorShapeCount) : GeneratorCubicIntervalData where
  cell := cell
  lower := shapeLower s
  width := shapeWidth s
  centered k b := cubicAffineCoefficients (generatorCellCoefficients cell k)
    (shapeLower s + shapeWidth s / 2) 1 b
  bound k := bernsteinAbsMax (cubicAffineCoefficients (generatorCellCoefficients cell k)
    (shapeLower s) (shapeWidth s))

theorem shapeCubic_valid (cell : Fin 72) (s : Fin generatorShapeCount) :
    (shapeCubic cell s).IsValid :=
  ⟨shapeWidth_pos s, fun _ _ ↦ rfl, fun _ b ↦ abs_bernstein_le_bernsteinAbsMax _ b⟩

/-- One actual coordinate interval: a cell and a shared dyadic shape. -/
structure GeneratorCoordinateData where
  cellIndex : Fin 72
  shape : Fin generatorShapeCount
  deriving DecidableEq

namespace GeneratorCoordinateData

/-- The computed cubic rows and Bernstein bounds. -/
def cubic (D : GeneratorCoordinateData) : GeneratorCubicIntervalData := shapeCubic D.cellIndex D.shape

/-- The positive-center Taylor datum for one knot, before the sign. -/
def rootData (D : GeneratorCoordinateData) (k : Fin 145) : GeneratorPowerTaylorData :=
  if h : k.val ≤ D.cellIndex.val + 72 then
    generatorPowerCacheA D.shape ⟨D.cellIndex.val + 72 - k.val, by omega⟩
  else
    generatorPowerCacheB D.shape ⟨k.val - 73 - D.cellIndex.val, by omega⟩

/-- The knots to the right of the cell use reflected data. -/
def negative (D : GeneratorCoordinateData) (k : Fin 145) : Bool := decide (D.cellIndex.val + 72 < k.val)

/-- The actual signed Taylor family selected from the shared cache. -/
def powers (D : GeneratorCoordinateData) : Fin 145 → GeneratorPowerTaylorData :=
  GeneratorPowerTaylorData.signedFamily D.rootData D.negative

/-- The checks that the selected data refer to the actual coordinate interval. -/
def IsValid (D : GeneratorCoordinateData) : Prop :=
  D.cubic.IsValid ∧
    (∀ k, (D.powers k).center =
      (D.cubic.cell.val : ℚ) + D.cubic.midpoint - (generatorKnot k : ℚ)) ∧
    ∀ k, (D.powers k).radius = D.cubic.width / 2

instance (D : GeneratorCoordinateData) : Decidable D.IsValid := by
  unfold IsValid
  infer_instance

theorem rootData_valid (D : GeneratorCoordinateData) (k : Fin 145) : (D.rootData k).IsValid := by
  unfold rootData
  split_ifs
  · exact (generatorPowerCacheA_valid _ _).1
  · exact (generatorPowerCacheB_valid _ _).1

/-- Each selected signed power family satisfies genuine root and error checks. -/
theorem powers_valid (D : GeneratorCoordinateData) (k : Fin 145) :
    (D.powers k).IsValid :=
  GeneratorPowerTaylorData.signedFamily_valid D.rootData_valid D.negative k

/-- Every computed coordinate datum is valid. -/
theorem isValid (D : GeneratorCoordinateData) : D.IsValid := by
  refine ⟨shapeCubic_valid _ _, fun k ↦ ?_, fun k ↦ ?_⟩
  · simp only [powers, GeneratorPowerTaylorData.signedFamily, negative, rootData, cubic,
      shapeCubic, GeneratorCubicIntervalData.midpoint, generatorKnot]
    by_cases h : k.val ≤ D.cellIndex.val + 72
    · have hn : ¬ (D.cellIndex.val + 72 < k.val) := by omega
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, h, ↓reduceDIte]
      rw [(generatorPowerCacheA_valid _ _).2.1]
      unfold shapeMid
      push_cast [Nat.cast_sub h]
      ring
    · have hn : D.cellIndex.val + 72 < k.val := by omega
      simp only [hn, decide_true, ↓reduceIte, h, ↓reduceDIte, GeneratorPowerTaylorData.reflect_center]
      rw [(generatorPowerCacheB_valid _ _).2.1]
      have h₁ : 73 + D.cellIndex.val ≤ k.val := by omega
      have h₂ : ((k.val - 73 - D.cellIndex.val : ℕ) : ℚ) = (k.val : ℚ) - 73 - D.cellIndex.val := by
        rw [Nat.sub_sub, Nat.cast_sub h₁]; push_cast; ring
      rw [h₂]
      unfold shapeMid
      push_cast
      ring
  · simp only [powers, GeneratorPowerTaylorData.signedFamily, negative, rootData, cubic, shapeCubic]
    by_cases h : k.val ≤ D.cellIndex.val + 72
    · have hn : ¬ (D.cellIndex.val + 72 < k.val) := by omega
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, h, ↓reduceDIte]
      exact (generatorPowerCacheA_valid _ _).2.2
    · have hn : D.cellIndex.val + 72 < k.val := by omega
      simp only [hn, decide_true, ↓reduceIte, h, ↓reduceDIte, GeneratorPowerTaylorData.reflect_radius]
      exact (generatorPowerCacheB_valid _ _).2.2

end GeneratorCoordinateData

end PartialBalayage.Maximal.Square
