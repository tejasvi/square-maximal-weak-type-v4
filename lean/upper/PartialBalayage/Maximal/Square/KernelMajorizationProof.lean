/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.KernelMajorizationProofAssembly
public import PartialBalayage.Maximal.Square.Data.MajRows0
public import PartialBalayage.Maximal.Square.Data.MajRows1
public import PartialBalayage.Maximal.Square.Data.MajRows2
public import PartialBalayage.Maximal.Square.Data.MajRows3
public import PartialBalayage.Maximal.Square.Data.MajRows4
public import PartialBalayage.Maximal.Square.Data.MajRows5
public import PartialBalayage.Maximal.Square.Data.MajRows6
public import PartialBalayage.Maximal.Square.Data.MajRows7
public import PartialBalayage.Maximal.Square.Data.MajRows8
public import PartialBalayage.Maximal.Square.Data.MajRows9
public import PartialBalayage.Maximal.Square.Data.MajRows10
public import PartialBalayage.Maximal.Square.Data.MajRows11
public import PartialBalayage.Maximal.Square.Data.MajRows12
public import PartialBalayage.Maximal.Square.Data.MajRows13
public import PartialBalayage.Maximal.Square.Data.MajRows14
public import PartialBalayage.Maximal.Square.Data.MajRows15
public import PartialBalayage.Maximal.Square.Data.MajRows16
public import PartialBalayage.Maximal.Square.Data.MajRows17

/-!
# The quarter-plane majorization facts of our kernel

The generated subdivision trees of all 2,628 ordered cells `0 ≤ l ≤ k ≤ 71` are checked cell by
cell by the kernel; the assembly theorem turns them into the instance `KernelMajorizationFacts`.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The generated rows of cell certificates. -/
def majRows (k : ℕ) : List (MajTree × MajTree) :=
  [majRow_0, majRow_1, majRow_2, majRow_3, majRow_4, majRow_5, majRow_6, majRow_7, majRow_8, majRow_9, majRow_10, majRow_11, majRow_12, majRow_13, majRow_14, majRow_15, majRow_16, majRow_17, majRow_18, majRow_19, majRow_20, majRow_21, majRow_22, majRow_23, majRow_24, majRow_25, majRow_26, majRow_27, majRow_28, majRow_29, majRow_30, majRow_31, majRow_32, majRow_33, majRow_34, majRow_35, majRow_36, majRow_37, majRow_38, majRow_39, majRow_40, majRow_41, majRow_42, majRow_43, majRow_44, majRow_45, majRow_46, majRow_47, majRow_48, majRow_49, majRow_50, majRow_51, majRow_52, majRow_53, majRow_54, majRow_55, majRow_56, majRow_57, majRow_58, majRow_59, majRow_60, majRow_61, majRow_62, majRow_63, majRow_64, majRow_65, majRow_66, majRow_67, majRow_68, majRow_69, majRow_70, majRow_71].getD k []

/-- The certificate of the ordered cell `(k, l)`. -/
def majCert (k l : ℕ) : MajTree × MajTree := (majRows k).getD l (.leaf 0, .leaf 0)

theorem majCert_check : ∀ k l : ℕ, l ≤ k → k ≤ 71 → majCellCheck k l (majCert k l) = true := by
  intro k l hlk hk
  interval_cases k
  · exact majRow_0_all l hlk
  · exact majRow_1_all l hlk
  · exact majRow_2_all l hlk
  · exact majRow_3_all l hlk
  · exact majRow_4_all l hlk
  · exact majRow_5_all l hlk
  · exact majRow_6_all l hlk
  · exact majRow_7_all l hlk
  · exact majRow_8_all l hlk
  · exact majRow_9_all l hlk
  · exact majRow_10_all l hlk
  · exact majRow_11_all l hlk
  · exact majRow_12_all l hlk
  · exact majRow_13_all l hlk
  · exact majRow_14_all l hlk
  · exact majRow_15_all l hlk
  · exact majRow_16_all l hlk
  · exact majRow_17_all l hlk
  · exact majRow_18_all l hlk
  · exact majRow_19_all l hlk
  · exact majRow_20_all l hlk
  · exact majRow_21_all l hlk
  · exact majRow_22_all l hlk
  · exact majRow_23_all l hlk
  · exact majRow_24_all l hlk
  · exact majRow_25_all l hlk
  · exact majRow_26_all l hlk
  · exact majRow_27_all l hlk
  · exact majRow_28_all l hlk
  · exact majRow_29_all l hlk
  · exact majRow_30_all l hlk
  · exact majRow_31_all l hlk
  · exact majRow_32_all l hlk
  · exact majRow_33_all l hlk
  · exact majRow_34_all l hlk
  · exact majRow_35_all l hlk
  · exact majRow_36_all l hlk
  · exact majRow_37_all l hlk
  · exact majRow_38_all l hlk
  · exact majRow_39_all l hlk
  · exact majRow_40_all l hlk
  · exact majRow_41_all l hlk
  · exact majRow_42_all l hlk
  · exact majRow_43_all l hlk
  · exact majRow_44_all l hlk
  · exact majRow_45_all l hlk
  · exact majRow_46_all l hlk
  · exact majRow_47_all l hlk
  · exact majRow_48_all l hlk
  · exact majRow_49_all l hlk
  · exact majRow_50_all l hlk
  · exact majRow_51_all l hlk
  · exact majRow_52_all l hlk
  · exact majRow_53_all l hlk
  · exact majRow_54_all l hlk
  · exact majRow_55_all l hlk
  · exact majRow_56_all l hlk
  · exact majRow_57_all l hlk
  · exact majRow_58_all l hlk
  · exact majRow_59_all l hlk
  · exact majRow_60_all l hlk
  · exact majRow_61_all l hlk
  · exact majRow_62_all l hlk
  · exact majRow_63_all l hlk
  · exact majRow_64_all l hlk
  · exact majRow_65_all l hlk
  · exact majRow_66_all l hlk
  · exact majRow_67_all l hlk
  · exact majRow_68_all l hlk
  · exact majRow_69_all l hlk
  · exact majRow_70_all l hlk
  · exact majRow_71_all l hlk

/-- The kernel is nonnegative on the quarter plane and at least one on the unit quarter diamond. -/
instance kernelMajorizationFacts : KernelMajorizationFacts :=
  kernelMajorizationFacts_of_cells majCert majCert_check

end PartialBalayage.Maximal.Square
