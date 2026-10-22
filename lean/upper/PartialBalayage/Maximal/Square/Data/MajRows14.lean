/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module
public import PartialBalayage.Maximal.Square.KernelMajorizationProofCore
@[expose] public section
namespace PartialBalayage.Maximal.Square
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def majRow_64 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_64_cell_0 :
    majCellCheck 64 0 (majRow_64.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_1 :
    majCellCheck 64 1 (majRow_64.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_2 :
    majCellCheck 64 2 (majRow_64.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_3 :
    majCellCheck 64 3 (majRow_64.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_4 :
    majCellCheck 64 4 (majRow_64.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_5 :
    majCellCheck 64 5 (majRow_64.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_6 :
    majCellCheck 64 6 (majRow_64.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_7 :
    majCellCheck 64 7 (majRow_64.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_8 :
    majCellCheck 64 8 (majRow_64.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_9 :
    majCellCheck 64 9 (majRow_64.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_10 :
    majCellCheck 64 10 (majRow_64.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_11 :
    majCellCheck 64 11 (majRow_64.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_12 :
    majCellCheck 64 12 (majRow_64.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_13 :
    majCellCheck 64 13 (majRow_64.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_14 :
    majCellCheck 64 14 (majRow_64.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_15 :
    majCellCheck 64 15 (majRow_64.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_16 :
    majCellCheck 64 16 (majRow_64.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_17 :
    majCellCheck 64 17 (majRow_64.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_18 :
    majCellCheck 64 18 (majRow_64.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_19 :
    majCellCheck 64 19 (majRow_64.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_20 :
    majCellCheck 64 20 (majRow_64.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_21 :
    majCellCheck 64 21 (majRow_64.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_22 :
    majCellCheck 64 22 (majRow_64.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_23 :
    majCellCheck 64 23 (majRow_64.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_24 :
    majCellCheck 64 24 (majRow_64.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_25 :
    majCellCheck 64 25 (majRow_64.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_26 :
    majCellCheck 64 26 (majRow_64.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_27 :
    majCellCheck 64 27 (majRow_64.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_28 :
    majCellCheck 64 28 (majRow_64.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_29 :
    majCellCheck 64 29 (majRow_64.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_30 :
    majCellCheck 64 30 (majRow_64.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_31 :
    majCellCheck 64 31 (majRow_64.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_32 :
    majCellCheck 64 32 (majRow_64.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_33 :
    majCellCheck 64 33 (majRow_64.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_34 :
    majCellCheck 64 34 (majRow_64.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_35 :
    majCellCheck 64 35 (majRow_64.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_36 :
    majCellCheck 64 36 (majRow_64.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_37 :
    majCellCheck 64 37 (majRow_64.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_38 :
    majCellCheck 64 38 (majRow_64.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_39 :
    majCellCheck 64 39 (majRow_64.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_40 :
    majCellCheck 64 40 (majRow_64.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_41 :
    majCellCheck 64 41 (majRow_64.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_42 :
    majCellCheck 64 42 (majRow_64.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_43 :
    majCellCheck 64 43 (majRow_64.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_44 :
    majCellCheck 64 44 (majRow_64.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_45 :
    majCellCheck 64 45 (majRow_64.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_46 :
    majCellCheck 64 46 (majRow_64.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_47 :
    majCellCheck 64 47 (majRow_64.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_48 :
    majCellCheck 64 48 (majRow_64.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_49 :
    majCellCheck 64 49 (majRow_64.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_50 :
    majCellCheck 64 50 (majRow_64.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_51 :
    majCellCheck 64 51 (majRow_64.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_52 :
    majCellCheck 64 52 (majRow_64.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_53 :
    majCellCheck 64 53 (majRow_64.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_54 :
    majCellCheck 64 54 (majRow_64.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_55 :
    majCellCheck 64 55 (majRow_64.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_56 :
    majCellCheck 64 56 (majRow_64.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_57 :
    majCellCheck 64 57 (majRow_64.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_58 :
    majCellCheck 64 58 (majRow_64.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_59 :
    majCellCheck 64 59 (majRow_64.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_60 :
    majCellCheck 64 60 (majRow_64.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_61 :
    majCellCheck 64 61 (majRow_64.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_62 :
    majCellCheck 64 62 (majRow_64.getD 62 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_63 :
    majCellCheck 64 63 (majRow_64.getD 63 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_cell_64 :
    majCellCheck 64 64 (majRow_64.getD 64 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_64_all : ∀ l, l ≤ 64 →
    majCellCheck 64 l (majRow_64.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_64_cell_0, majRow_64_cell_1, majRow_64_cell_2, majRow_64_cell_3, majRow_64_cell_4, majRow_64_cell_5, majRow_64_cell_6, majRow_64_cell_7, majRow_64_cell_8, majRow_64_cell_9, majRow_64_cell_10, majRow_64_cell_11, majRow_64_cell_12, majRow_64_cell_13, majRow_64_cell_14, majRow_64_cell_15, majRow_64_cell_16, majRow_64_cell_17, majRow_64_cell_18, majRow_64_cell_19, majRow_64_cell_20, majRow_64_cell_21, majRow_64_cell_22, majRow_64_cell_23, majRow_64_cell_24, majRow_64_cell_25, majRow_64_cell_26, majRow_64_cell_27, majRow_64_cell_28, majRow_64_cell_29, majRow_64_cell_30, majRow_64_cell_31, majRow_64_cell_32, majRow_64_cell_33, majRow_64_cell_34, majRow_64_cell_35, majRow_64_cell_36, majRow_64_cell_37, majRow_64_cell_38, majRow_64_cell_39, majRow_64_cell_40, majRow_64_cell_41, majRow_64_cell_42, majRow_64_cell_43, majRow_64_cell_44, majRow_64_cell_45, majRow_64_cell_46, majRow_64_cell_47, majRow_64_cell_48, majRow_64_cell_49, majRow_64_cell_50, majRow_64_cell_51, majRow_64_cell_52, majRow_64_cell_53, majRow_64_cell_54, majRow_64_cell_55, majRow_64_cell_56, majRow_64_cell_57, majRow_64_cell_58, majRow_64_cell_59, majRow_64_cell_60, majRow_64_cell_61, majRow_64_cell_62, majRow_64_cell_63, majRow_64_cell_64]

def majRow_65 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_65_cell_0 :
    majCellCheck 65 0 (majRow_65.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_1 :
    majCellCheck 65 1 (majRow_65.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_2 :
    majCellCheck 65 2 (majRow_65.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_3 :
    majCellCheck 65 3 (majRow_65.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_4 :
    majCellCheck 65 4 (majRow_65.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_5 :
    majCellCheck 65 5 (majRow_65.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_6 :
    majCellCheck 65 6 (majRow_65.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_7 :
    majCellCheck 65 7 (majRow_65.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_8 :
    majCellCheck 65 8 (majRow_65.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_9 :
    majCellCheck 65 9 (majRow_65.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_10 :
    majCellCheck 65 10 (majRow_65.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_11 :
    majCellCheck 65 11 (majRow_65.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_12 :
    majCellCheck 65 12 (majRow_65.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_13 :
    majCellCheck 65 13 (majRow_65.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_14 :
    majCellCheck 65 14 (majRow_65.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_15 :
    majCellCheck 65 15 (majRow_65.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_16 :
    majCellCheck 65 16 (majRow_65.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_17 :
    majCellCheck 65 17 (majRow_65.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_18 :
    majCellCheck 65 18 (majRow_65.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_19 :
    majCellCheck 65 19 (majRow_65.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_20 :
    majCellCheck 65 20 (majRow_65.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_21 :
    majCellCheck 65 21 (majRow_65.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_22 :
    majCellCheck 65 22 (majRow_65.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_23 :
    majCellCheck 65 23 (majRow_65.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_24 :
    majCellCheck 65 24 (majRow_65.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_25 :
    majCellCheck 65 25 (majRow_65.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_26 :
    majCellCheck 65 26 (majRow_65.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_27 :
    majCellCheck 65 27 (majRow_65.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_28 :
    majCellCheck 65 28 (majRow_65.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_29 :
    majCellCheck 65 29 (majRow_65.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_30 :
    majCellCheck 65 30 (majRow_65.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_31 :
    majCellCheck 65 31 (majRow_65.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_32 :
    majCellCheck 65 32 (majRow_65.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_33 :
    majCellCheck 65 33 (majRow_65.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_34 :
    majCellCheck 65 34 (majRow_65.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_35 :
    majCellCheck 65 35 (majRow_65.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_36 :
    majCellCheck 65 36 (majRow_65.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_37 :
    majCellCheck 65 37 (majRow_65.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_38 :
    majCellCheck 65 38 (majRow_65.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_39 :
    majCellCheck 65 39 (majRow_65.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_40 :
    majCellCheck 65 40 (majRow_65.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_41 :
    majCellCheck 65 41 (majRow_65.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_42 :
    majCellCheck 65 42 (majRow_65.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_43 :
    majCellCheck 65 43 (majRow_65.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_44 :
    majCellCheck 65 44 (majRow_65.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_45 :
    majCellCheck 65 45 (majRow_65.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_46 :
    majCellCheck 65 46 (majRow_65.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_47 :
    majCellCheck 65 47 (majRow_65.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_48 :
    majCellCheck 65 48 (majRow_65.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_49 :
    majCellCheck 65 49 (majRow_65.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_50 :
    majCellCheck 65 50 (majRow_65.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_51 :
    majCellCheck 65 51 (majRow_65.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_52 :
    majCellCheck 65 52 (majRow_65.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_53 :
    majCellCheck 65 53 (majRow_65.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_54 :
    majCellCheck 65 54 (majRow_65.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_55 :
    majCellCheck 65 55 (majRow_65.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_56 :
    majCellCheck 65 56 (majRow_65.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_57 :
    majCellCheck 65 57 (majRow_65.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_58 :
    majCellCheck 65 58 (majRow_65.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_59 :
    majCellCheck 65 59 (majRow_65.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_60 :
    majCellCheck 65 60 (majRow_65.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_61 :
    majCellCheck 65 61 (majRow_65.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_62 :
    majCellCheck 65 62 (majRow_65.getD 62 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_63 :
    majCellCheck 65 63 (majRow_65.getD 63 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_64 :
    majCellCheck 65 64 (majRow_65.getD 64 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_cell_65 :
    majCellCheck 65 65 (majRow_65.getD 65 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_65_all : ∀ l, l ≤ 65 →
    majCellCheck 65 l (majRow_65.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_65_cell_0, majRow_65_cell_1, majRow_65_cell_2, majRow_65_cell_3, majRow_65_cell_4, majRow_65_cell_5, majRow_65_cell_6, majRow_65_cell_7, majRow_65_cell_8, majRow_65_cell_9, majRow_65_cell_10, majRow_65_cell_11, majRow_65_cell_12, majRow_65_cell_13, majRow_65_cell_14, majRow_65_cell_15, majRow_65_cell_16, majRow_65_cell_17, majRow_65_cell_18, majRow_65_cell_19, majRow_65_cell_20, majRow_65_cell_21, majRow_65_cell_22, majRow_65_cell_23, majRow_65_cell_24, majRow_65_cell_25, majRow_65_cell_26, majRow_65_cell_27, majRow_65_cell_28, majRow_65_cell_29, majRow_65_cell_30, majRow_65_cell_31, majRow_65_cell_32, majRow_65_cell_33, majRow_65_cell_34, majRow_65_cell_35, majRow_65_cell_36, majRow_65_cell_37, majRow_65_cell_38, majRow_65_cell_39, majRow_65_cell_40, majRow_65_cell_41, majRow_65_cell_42, majRow_65_cell_43, majRow_65_cell_44, majRow_65_cell_45, majRow_65_cell_46, majRow_65_cell_47, majRow_65_cell_48, majRow_65_cell_49, majRow_65_cell_50, majRow_65_cell_51, majRow_65_cell_52, majRow_65_cell_53, majRow_65_cell_54, majRow_65_cell_55, majRow_65_cell_56, majRow_65_cell_57, majRow_65_cell_58, majRow_65_cell_59, majRow_65_cell_60, majRow_65_cell_61, majRow_65_cell_62, majRow_65_cell_63, majRow_65_cell_64, majRow_65_cell_65]

def majRow_66 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_66_cell_0 :
    majCellCheck 66 0 (majRow_66.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_1 :
    majCellCheck 66 1 (majRow_66.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_2 :
    majCellCheck 66 2 (majRow_66.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_3 :
    majCellCheck 66 3 (majRow_66.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_4 :
    majCellCheck 66 4 (majRow_66.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_5 :
    majCellCheck 66 5 (majRow_66.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_6 :
    majCellCheck 66 6 (majRow_66.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_7 :
    majCellCheck 66 7 (majRow_66.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_8 :
    majCellCheck 66 8 (majRow_66.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_9 :
    majCellCheck 66 9 (majRow_66.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_10 :
    majCellCheck 66 10 (majRow_66.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_11 :
    majCellCheck 66 11 (majRow_66.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_12 :
    majCellCheck 66 12 (majRow_66.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_13 :
    majCellCheck 66 13 (majRow_66.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_14 :
    majCellCheck 66 14 (majRow_66.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_15 :
    majCellCheck 66 15 (majRow_66.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_16 :
    majCellCheck 66 16 (majRow_66.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_17 :
    majCellCheck 66 17 (majRow_66.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_18 :
    majCellCheck 66 18 (majRow_66.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_19 :
    majCellCheck 66 19 (majRow_66.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_20 :
    majCellCheck 66 20 (majRow_66.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_21 :
    majCellCheck 66 21 (majRow_66.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_22 :
    majCellCheck 66 22 (majRow_66.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_23 :
    majCellCheck 66 23 (majRow_66.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_24 :
    majCellCheck 66 24 (majRow_66.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_25 :
    majCellCheck 66 25 (majRow_66.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_26 :
    majCellCheck 66 26 (majRow_66.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_27 :
    majCellCheck 66 27 (majRow_66.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_28 :
    majCellCheck 66 28 (majRow_66.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_29 :
    majCellCheck 66 29 (majRow_66.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_30 :
    majCellCheck 66 30 (majRow_66.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_31 :
    majCellCheck 66 31 (majRow_66.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_32 :
    majCellCheck 66 32 (majRow_66.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_33 :
    majCellCheck 66 33 (majRow_66.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_34 :
    majCellCheck 66 34 (majRow_66.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_35 :
    majCellCheck 66 35 (majRow_66.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_36 :
    majCellCheck 66 36 (majRow_66.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_37 :
    majCellCheck 66 37 (majRow_66.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_38 :
    majCellCheck 66 38 (majRow_66.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_39 :
    majCellCheck 66 39 (majRow_66.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_40 :
    majCellCheck 66 40 (majRow_66.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_41 :
    majCellCheck 66 41 (majRow_66.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_42 :
    majCellCheck 66 42 (majRow_66.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_43 :
    majCellCheck 66 43 (majRow_66.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_44 :
    majCellCheck 66 44 (majRow_66.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_45 :
    majCellCheck 66 45 (majRow_66.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_46 :
    majCellCheck 66 46 (majRow_66.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_47 :
    majCellCheck 66 47 (majRow_66.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_48 :
    majCellCheck 66 48 (majRow_66.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_49 :
    majCellCheck 66 49 (majRow_66.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_50 :
    majCellCheck 66 50 (majRow_66.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_51 :
    majCellCheck 66 51 (majRow_66.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_52 :
    majCellCheck 66 52 (majRow_66.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_53 :
    majCellCheck 66 53 (majRow_66.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_54 :
    majCellCheck 66 54 (majRow_66.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_55 :
    majCellCheck 66 55 (majRow_66.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_56 :
    majCellCheck 66 56 (majRow_66.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_57 :
    majCellCheck 66 57 (majRow_66.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_58 :
    majCellCheck 66 58 (majRow_66.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_59 :
    majCellCheck 66 59 (majRow_66.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_60 :
    majCellCheck 66 60 (majRow_66.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_61 :
    majCellCheck 66 61 (majRow_66.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_62 :
    majCellCheck 66 62 (majRow_66.getD 62 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_63 :
    majCellCheck 66 63 (majRow_66.getD 63 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_64 :
    majCellCheck 66 64 (majRow_66.getD 64 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_65 :
    majCellCheck 66 65 (majRow_66.getD 65 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_cell_66 :
    majCellCheck 66 66 (majRow_66.getD 66 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_66_all : ∀ l, l ≤ 66 →
    majCellCheck 66 l (majRow_66.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_66_cell_0, majRow_66_cell_1, majRow_66_cell_2, majRow_66_cell_3, majRow_66_cell_4, majRow_66_cell_5, majRow_66_cell_6, majRow_66_cell_7, majRow_66_cell_8, majRow_66_cell_9, majRow_66_cell_10, majRow_66_cell_11, majRow_66_cell_12, majRow_66_cell_13, majRow_66_cell_14, majRow_66_cell_15, majRow_66_cell_16, majRow_66_cell_17, majRow_66_cell_18, majRow_66_cell_19, majRow_66_cell_20, majRow_66_cell_21, majRow_66_cell_22, majRow_66_cell_23, majRow_66_cell_24, majRow_66_cell_25, majRow_66_cell_26, majRow_66_cell_27, majRow_66_cell_28, majRow_66_cell_29, majRow_66_cell_30, majRow_66_cell_31, majRow_66_cell_32, majRow_66_cell_33, majRow_66_cell_34, majRow_66_cell_35, majRow_66_cell_36, majRow_66_cell_37, majRow_66_cell_38, majRow_66_cell_39, majRow_66_cell_40, majRow_66_cell_41, majRow_66_cell_42, majRow_66_cell_43, majRow_66_cell_44, majRow_66_cell_45, majRow_66_cell_46, majRow_66_cell_47, majRow_66_cell_48, majRow_66_cell_49, majRow_66_cell_50, majRow_66_cell_51, majRow_66_cell_52, majRow_66_cell_53, majRow_66_cell_54, majRow_66_cell_55, majRow_66_cell_56, majRow_66_cell_57, majRow_66_cell_58, majRow_66_cell_59, majRow_66_cell_60, majRow_66_cell_61, majRow_66_cell_62, majRow_66_cell_63, majRow_66_cell_64, majRow_66_cell_65, majRow_66_cell_66]

end PartialBalayage.Maximal.Square
