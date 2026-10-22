/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: 72 partition cells and 145 signed knots (offset 72) for our kernel. -/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix0
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix1
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix2
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix3
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix4
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix5
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix6
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix7
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix8
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix9
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix10
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix11
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix12
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix13
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix14
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix15
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix16
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix17
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix18
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix19
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix20
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix21
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix22
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix23
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix24
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix25
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix26
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix27
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix28
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix29
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix30
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix31
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix32
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix33
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix34
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix35
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix36
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix37
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix38
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix39
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix40
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix41
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix42
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix43
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix44
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix45
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix46
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix47
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix48
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix49
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix50
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix51
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix52
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix53
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix54
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix55
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix56
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix57
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix58
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix59
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix60
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix61
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix62
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix63
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix64
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix65
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix66
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix67
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix68
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix69
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix70
public import PartialBalayage.Maximal.Square.Data.GeneratorCellMatrix71
public import PartialBalayage.Maximal.Square.SplineGeneratorCellPolynomial

/-!
# Genuine signed generator coefficients on all partition cells

Every entry is identified with the actual signed spline generator coefficient by
the already checked finite tables. The combined table supplies the real cubic
evaluation without introducing a further arithmetic or graph hypothesis.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- The proved actual cubic generator rows for all seventy-two partition cells. -/
def generatorCellCoefficients : Fin 72 → Fin 145 → Fin 4 → ℚ := ![
  generatorCellMatrix0,
  generatorCellMatrix1,
  generatorCellMatrix2,
  generatorCellMatrix3,
  generatorCellMatrix4,
  generatorCellMatrix5,
  generatorCellMatrix6,
  generatorCellMatrix7,
  generatorCellMatrix8,
  generatorCellMatrix9,
  generatorCellMatrix10,
  generatorCellMatrix11,
  generatorCellMatrix12,
  generatorCellMatrix13,
  generatorCellMatrix14,
  generatorCellMatrix15,
  generatorCellMatrix16,
  generatorCellMatrix17,
  generatorCellMatrix18,
  generatorCellMatrix19,
  generatorCellMatrix20,
  generatorCellMatrix21,
  generatorCellMatrix22,
  generatorCellMatrix23,
  generatorCellMatrix24,
  generatorCellMatrix25,
  generatorCellMatrix26,
  generatorCellMatrix27,
  generatorCellMatrix28,
  generatorCellMatrix29,
  generatorCellMatrix30,
  generatorCellMatrix31,
  generatorCellMatrix32,
  generatorCellMatrix33,
  generatorCellMatrix34,
  generatorCellMatrix35,
  generatorCellMatrix36,
  generatorCellMatrix37,
  generatorCellMatrix38,
  generatorCellMatrix39,
  generatorCellMatrix40,
  generatorCellMatrix41,
  generatorCellMatrix42,
  generatorCellMatrix43,
  generatorCellMatrix44,
  generatorCellMatrix45,
  generatorCellMatrix46,
  generatorCellMatrix47,
  generatorCellMatrix48,
  generatorCellMatrix49,
  generatorCellMatrix50,
  generatorCellMatrix51,
  generatorCellMatrix52,
  generatorCellMatrix53,
  generatorCellMatrix54,
  generatorCellMatrix55,
  generatorCellMatrix56,
  generatorCellMatrix57,
  generatorCellMatrix58,
  generatorCellMatrix59,
  generatorCellMatrix60,
  generatorCellMatrix61,
  generatorCellMatrix62,
  generatorCellMatrix63,
  generatorCellMatrix64,
  generatorCellMatrix65,
  generatorCellMatrix66,
  generatorCellMatrix67,
  generatorCellMatrix68,
  generatorCellMatrix69,
  generatorCellMatrix70,
  generatorCellMatrix71
]

set_option maxRecDepth 20000 in
/-- Every entry of the combined table is the genuine generator-cell coefficient. -/
theorem generatorCellCoefficients_correct (cell : Fin 72) (k : Fin 145) (b : Fin 4) :
    splineGeneratorCellCoefficient (cell.val : ℤ) ((k.val : ℤ) - 72) b =
      generatorCellCoefficients cell k b := by
  fin_cases cell
  · exact generatorCellMatrix0_correct k b
  · exact generatorCellMatrix1_correct k b
  · exact generatorCellMatrix2_correct k b
  · exact generatorCellMatrix3_correct k b
  · exact generatorCellMatrix4_correct k b
  · exact generatorCellMatrix5_correct k b
  · exact generatorCellMatrix6_correct k b
  · exact generatorCellMatrix7_correct k b
  · exact generatorCellMatrix8_correct k b
  · exact generatorCellMatrix9_correct k b
  · exact generatorCellMatrix10_correct k b
  · exact generatorCellMatrix11_correct k b
  · exact generatorCellMatrix12_correct k b
  · exact generatorCellMatrix13_correct k b
  · exact generatorCellMatrix14_correct k b
  · exact generatorCellMatrix15_correct k b
  · exact generatorCellMatrix16_correct k b
  · exact generatorCellMatrix17_correct k b
  · exact generatorCellMatrix18_correct k b
  · exact generatorCellMatrix19_correct k b
  · exact generatorCellMatrix20_correct k b
  · exact generatorCellMatrix21_correct k b
  · exact generatorCellMatrix22_correct k b
  · exact generatorCellMatrix23_correct k b
  · exact generatorCellMatrix24_correct k b
  · exact generatorCellMatrix25_correct k b
  · exact generatorCellMatrix26_correct k b
  · exact generatorCellMatrix27_correct k b
  · exact generatorCellMatrix28_correct k b
  · exact generatorCellMatrix29_correct k b
  · exact generatorCellMatrix30_correct k b
  · exact generatorCellMatrix31_correct k b
  · exact generatorCellMatrix32_correct k b
  · exact generatorCellMatrix33_correct k b
  · exact generatorCellMatrix34_correct k b
  · exact generatorCellMatrix35_correct k b
  · exact generatorCellMatrix36_correct k b
  · exact generatorCellMatrix37_correct k b
  · exact generatorCellMatrix38_correct k b
  · exact generatorCellMatrix39_correct k b
  · exact generatorCellMatrix40_correct k b
  · exact generatorCellMatrix41_correct k b
  · exact generatorCellMatrix42_correct k b
  · exact generatorCellMatrix43_correct k b
  · exact generatorCellMatrix44_correct k b
  · exact generatorCellMatrix45_correct k b
  · exact generatorCellMatrix46_correct k b
  · exact generatorCellMatrix47_correct k b
  · exact generatorCellMatrix48_correct k b
  · exact generatorCellMatrix49_correct k b
  · exact generatorCellMatrix50_correct k b
  · exact generatorCellMatrix51_correct k b
  · exact generatorCellMatrix52_correct k b
  · exact generatorCellMatrix53_correct k b
  · exact generatorCellMatrix54_correct k b
  · exact generatorCellMatrix55_correct k b
  · exact generatorCellMatrix56_correct k b
  · exact generatorCellMatrix57_correct k b
  · exact generatorCellMatrix58_correct k b
  · exact generatorCellMatrix59_correct k b
  · exact generatorCellMatrix60_correct k b
  · exact generatorCellMatrix61_correct k b
  · exact generatorCellMatrix62_correct k b
  · exact generatorCellMatrix63_correct k b
  · exact generatorCellMatrix64_correct k b
  · exact generatorCellMatrix65_correct k b
  · exact generatorCellMatrix66_correct k b
  · exact generatorCellMatrix67_correct k b
  · exact generatorCellMatrix68_correct k b
  · exact generatorCellMatrix69_correct k b
  · exact generatorCellMatrix70_correct k b
  · exact generatorCellMatrix71_correct k b

/-- The actual closed-cell cubic evaluates to the proved finite coefficient row. -/
theorem splineGeneratorCellPolynomial_eq_generatorCellCoefficients
    (cell : Fin 72) (k : Fin 145) (s : ℝ) :
    splineGeneratorCellPolynomial (cell.val : ℤ) ((k.val : ℤ) - 72) s =
      centeredCubic (fun b ↦ (generatorCellCoefficients cell k b : ℝ)) s := by
  rw [splineGeneratorCellPolynomial_eq_centeredCubic]
  simp_rw [generatorCellCoefficients_correct]

end PartialBalayage.Maximal.Square
