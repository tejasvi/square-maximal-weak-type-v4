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

def majRow_61 : List (MajTree × MajTree) := [
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

theorem majRow_61_cell_0 :
    majCellCheck 61 0 (majRow_61.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_1 :
    majCellCheck 61 1 (majRow_61.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_2 :
    majCellCheck 61 2 (majRow_61.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_3 :
    majCellCheck 61 3 (majRow_61.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_4 :
    majCellCheck 61 4 (majRow_61.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_5 :
    majCellCheck 61 5 (majRow_61.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_6 :
    majCellCheck 61 6 (majRow_61.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_7 :
    majCellCheck 61 7 (majRow_61.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_8 :
    majCellCheck 61 8 (majRow_61.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_9 :
    majCellCheck 61 9 (majRow_61.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_10 :
    majCellCheck 61 10 (majRow_61.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_11 :
    majCellCheck 61 11 (majRow_61.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_12 :
    majCellCheck 61 12 (majRow_61.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_13 :
    majCellCheck 61 13 (majRow_61.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_14 :
    majCellCheck 61 14 (majRow_61.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_15 :
    majCellCheck 61 15 (majRow_61.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_16 :
    majCellCheck 61 16 (majRow_61.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_17 :
    majCellCheck 61 17 (majRow_61.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_18 :
    majCellCheck 61 18 (majRow_61.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_19 :
    majCellCheck 61 19 (majRow_61.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_20 :
    majCellCheck 61 20 (majRow_61.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_21 :
    majCellCheck 61 21 (majRow_61.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_22 :
    majCellCheck 61 22 (majRow_61.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_23 :
    majCellCheck 61 23 (majRow_61.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_24 :
    majCellCheck 61 24 (majRow_61.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_25 :
    majCellCheck 61 25 (majRow_61.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_26 :
    majCellCheck 61 26 (majRow_61.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_27 :
    majCellCheck 61 27 (majRow_61.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_28 :
    majCellCheck 61 28 (majRow_61.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_29 :
    majCellCheck 61 29 (majRow_61.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_30 :
    majCellCheck 61 30 (majRow_61.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_31 :
    majCellCheck 61 31 (majRow_61.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_32 :
    majCellCheck 61 32 (majRow_61.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_33 :
    majCellCheck 61 33 (majRow_61.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_34 :
    majCellCheck 61 34 (majRow_61.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_35 :
    majCellCheck 61 35 (majRow_61.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_36 :
    majCellCheck 61 36 (majRow_61.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_37 :
    majCellCheck 61 37 (majRow_61.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_38 :
    majCellCheck 61 38 (majRow_61.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_39 :
    majCellCheck 61 39 (majRow_61.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_40 :
    majCellCheck 61 40 (majRow_61.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_41 :
    majCellCheck 61 41 (majRow_61.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_42 :
    majCellCheck 61 42 (majRow_61.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_43 :
    majCellCheck 61 43 (majRow_61.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_44 :
    majCellCheck 61 44 (majRow_61.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_45 :
    majCellCheck 61 45 (majRow_61.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_46 :
    majCellCheck 61 46 (majRow_61.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_47 :
    majCellCheck 61 47 (majRow_61.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_48 :
    majCellCheck 61 48 (majRow_61.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_49 :
    majCellCheck 61 49 (majRow_61.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_50 :
    majCellCheck 61 50 (majRow_61.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_51 :
    majCellCheck 61 51 (majRow_61.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_52 :
    majCellCheck 61 52 (majRow_61.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_53 :
    majCellCheck 61 53 (majRow_61.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_54 :
    majCellCheck 61 54 (majRow_61.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_55 :
    majCellCheck 61 55 (majRow_61.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_56 :
    majCellCheck 61 56 (majRow_61.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_57 :
    majCellCheck 61 57 (majRow_61.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_58 :
    majCellCheck 61 58 (majRow_61.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_59 :
    majCellCheck 61 59 (majRow_61.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_60 :
    majCellCheck 61 60 (majRow_61.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_cell_61 :
    majCellCheck 61 61 (majRow_61.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_61_all : ∀ l, l ≤ 61 →
    majCellCheck 61 l (majRow_61.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_61_cell_0, majRow_61_cell_1, majRow_61_cell_2, majRow_61_cell_3, majRow_61_cell_4, majRow_61_cell_5, majRow_61_cell_6, majRow_61_cell_7, majRow_61_cell_8, majRow_61_cell_9, majRow_61_cell_10, majRow_61_cell_11, majRow_61_cell_12, majRow_61_cell_13, majRow_61_cell_14, majRow_61_cell_15, majRow_61_cell_16, majRow_61_cell_17, majRow_61_cell_18, majRow_61_cell_19, majRow_61_cell_20, majRow_61_cell_21, majRow_61_cell_22, majRow_61_cell_23, majRow_61_cell_24, majRow_61_cell_25, majRow_61_cell_26, majRow_61_cell_27, majRow_61_cell_28, majRow_61_cell_29, majRow_61_cell_30, majRow_61_cell_31, majRow_61_cell_32, majRow_61_cell_33, majRow_61_cell_34, majRow_61_cell_35, majRow_61_cell_36, majRow_61_cell_37, majRow_61_cell_38, majRow_61_cell_39, majRow_61_cell_40, majRow_61_cell_41, majRow_61_cell_42, majRow_61_cell_43, majRow_61_cell_44, majRow_61_cell_45, majRow_61_cell_46, majRow_61_cell_47, majRow_61_cell_48, majRow_61_cell_49, majRow_61_cell_50, majRow_61_cell_51, majRow_61_cell_52, majRow_61_cell_53, majRow_61_cell_54, majRow_61_cell_55, majRow_61_cell_56, majRow_61_cell_57, majRow_61_cell_58, majRow_61_cell_59, majRow_61_cell_60, majRow_61_cell_61]

def majRow_62 : List (MajTree × MajTree) := [
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

theorem majRow_62_cell_0 :
    majCellCheck 62 0 (majRow_62.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_1 :
    majCellCheck 62 1 (majRow_62.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_2 :
    majCellCheck 62 2 (majRow_62.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_3 :
    majCellCheck 62 3 (majRow_62.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_4 :
    majCellCheck 62 4 (majRow_62.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_5 :
    majCellCheck 62 5 (majRow_62.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_6 :
    majCellCheck 62 6 (majRow_62.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_7 :
    majCellCheck 62 7 (majRow_62.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_8 :
    majCellCheck 62 8 (majRow_62.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_9 :
    majCellCheck 62 9 (majRow_62.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_10 :
    majCellCheck 62 10 (majRow_62.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_11 :
    majCellCheck 62 11 (majRow_62.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_12 :
    majCellCheck 62 12 (majRow_62.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_13 :
    majCellCheck 62 13 (majRow_62.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_14 :
    majCellCheck 62 14 (majRow_62.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_15 :
    majCellCheck 62 15 (majRow_62.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_16 :
    majCellCheck 62 16 (majRow_62.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_17 :
    majCellCheck 62 17 (majRow_62.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_18 :
    majCellCheck 62 18 (majRow_62.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_19 :
    majCellCheck 62 19 (majRow_62.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_20 :
    majCellCheck 62 20 (majRow_62.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_21 :
    majCellCheck 62 21 (majRow_62.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_22 :
    majCellCheck 62 22 (majRow_62.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_23 :
    majCellCheck 62 23 (majRow_62.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_24 :
    majCellCheck 62 24 (majRow_62.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_25 :
    majCellCheck 62 25 (majRow_62.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_26 :
    majCellCheck 62 26 (majRow_62.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_27 :
    majCellCheck 62 27 (majRow_62.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_28 :
    majCellCheck 62 28 (majRow_62.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_29 :
    majCellCheck 62 29 (majRow_62.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_30 :
    majCellCheck 62 30 (majRow_62.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_31 :
    majCellCheck 62 31 (majRow_62.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_32 :
    majCellCheck 62 32 (majRow_62.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_33 :
    majCellCheck 62 33 (majRow_62.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_34 :
    majCellCheck 62 34 (majRow_62.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_35 :
    majCellCheck 62 35 (majRow_62.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_36 :
    majCellCheck 62 36 (majRow_62.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_37 :
    majCellCheck 62 37 (majRow_62.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_38 :
    majCellCheck 62 38 (majRow_62.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_39 :
    majCellCheck 62 39 (majRow_62.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_40 :
    majCellCheck 62 40 (majRow_62.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_41 :
    majCellCheck 62 41 (majRow_62.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_42 :
    majCellCheck 62 42 (majRow_62.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_43 :
    majCellCheck 62 43 (majRow_62.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_44 :
    majCellCheck 62 44 (majRow_62.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_45 :
    majCellCheck 62 45 (majRow_62.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_46 :
    majCellCheck 62 46 (majRow_62.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_47 :
    majCellCheck 62 47 (majRow_62.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_48 :
    majCellCheck 62 48 (majRow_62.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_49 :
    majCellCheck 62 49 (majRow_62.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_50 :
    majCellCheck 62 50 (majRow_62.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_51 :
    majCellCheck 62 51 (majRow_62.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_52 :
    majCellCheck 62 52 (majRow_62.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_53 :
    majCellCheck 62 53 (majRow_62.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_54 :
    majCellCheck 62 54 (majRow_62.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_55 :
    majCellCheck 62 55 (majRow_62.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_56 :
    majCellCheck 62 56 (majRow_62.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_57 :
    majCellCheck 62 57 (majRow_62.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_58 :
    majCellCheck 62 58 (majRow_62.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_59 :
    majCellCheck 62 59 (majRow_62.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_60 :
    majCellCheck 62 60 (majRow_62.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_61 :
    majCellCheck 62 61 (majRow_62.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_cell_62 :
    majCellCheck 62 62 (majRow_62.getD 62 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_62_all : ∀ l, l ≤ 62 →
    majCellCheck 62 l (majRow_62.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_62_cell_0, majRow_62_cell_1, majRow_62_cell_2, majRow_62_cell_3, majRow_62_cell_4, majRow_62_cell_5, majRow_62_cell_6, majRow_62_cell_7, majRow_62_cell_8, majRow_62_cell_9, majRow_62_cell_10, majRow_62_cell_11, majRow_62_cell_12, majRow_62_cell_13, majRow_62_cell_14, majRow_62_cell_15, majRow_62_cell_16, majRow_62_cell_17, majRow_62_cell_18, majRow_62_cell_19, majRow_62_cell_20, majRow_62_cell_21, majRow_62_cell_22, majRow_62_cell_23, majRow_62_cell_24, majRow_62_cell_25, majRow_62_cell_26, majRow_62_cell_27, majRow_62_cell_28, majRow_62_cell_29, majRow_62_cell_30, majRow_62_cell_31, majRow_62_cell_32, majRow_62_cell_33, majRow_62_cell_34, majRow_62_cell_35, majRow_62_cell_36, majRow_62_cell_37, majRow_62_cell_38, majRow_62_cell_39, majRow_62_cell_40, majRow_62_cell_41, majRow_62_cell_42, majRow_62_cell_43, majRow_62_cell_44, majRow_62_cell_45, majRow_62_cell_46, majRow_62_cell_47, majRow_62_cell_48, majRow_62_cell_49, majRow_62_cell_50, majRow_62_cell_51, majRow_62_cell_52, majRow_62_cell_53, majRow_62_cell_54, majRow_62_cell_55, majRow_62_cell_56, majRow_62_cell_57, majRow_62_cell_58, majRow_62_cell_59, majRow_62_cell_60, majRow_62_cell_61, majRow_62_cell_62]

def majRow_63 : List (MajTree × MajTree) := [
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

theorem majRow_63_cell_0 :
    majCellCheck 63 0 (majRow_63.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_1 :
    majCellCheck 63 1 (majRow_63.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_2 :
    majCellCheck 63 2 (majRow_63.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_3 :
    majCellCheck 63 3 (majRow_63.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_4 :
    majCellCheck 63 4 (majRow_63.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_5 :
    majCellCheck 63 5 (majRow_63.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_6 :
    majCellCheck 63 6 (majRow_63.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_7 :
    majCellCheck 63 7 (majRow_63.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_8 :
    majCellCheck 63 8 (majRow_63.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_9 :
    majCellCheck 63 9 (majRow_63.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_10 :
    majCellCheck 63 10 (majRow_63.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_11 :
    majCellCheck 63 11 (majRow_63.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_12 :
    majCellCheck 63 12 (majRow_63.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_13 :
    majCellCheck 63 13 (majRow_63.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_14 :
    majCellCheck 63 14 (majRow_63.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_15 :
    majCellCheck 63 15 (majRow_63.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_16 :
    majCellCheck 63 16 (majRow_63.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_17 :
    majCellCheck 63 17 (majRow_63.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_18 :
    majCellCheck 63 18 (majRow_63.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_19 :
    majCellCheck 63 19 (majRow_63.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_20 :
    majCellCheck 63 20 (majRow_63.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_21 :
    majCellCheck 63 21 (majRow_63.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_22 :
    majCellCheck 63 22 (majRow_63.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_23 :
    majCellCheck 63 23 (majRow_63.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_24 :
    majCellCheck 63 24 (majRow_63.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_25 :
    majCellCheck 63 25 (majRow_63.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_26 :
    majCellCheck 63 26 (majRow_63.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_27 :
    majCellCheck 63 27 (majRow_63.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_28 :
    majCellCheck 63 28 (majRow_63.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_29 :
    majCellCheck 63 29 (majRow_63.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_30 :
    majCellCheck 63 30 (majRow_63.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_31 :
    majCellCheck 63 31 (majRow_63.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_32 :
    majCellCheck 63 32 (majRow_63.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_33 :
    majCellCheck 63 33 (majRow_63.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_34 :
    majCellCheck 63 34 (majRow_63.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_35 :
    majCellCheck 63 35 (majRow_63.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_36 :
    majCellCheck 63 36 (majRow_63.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_37 :
    majCellCheck 63 37 (majRow_63.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_38 :
    majCellCheck 63 38 (majRow_63.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_39 :
    majCellCheck 63 39 (majRow_63.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_40 :
    majCellCheck 63 40 (majRow_63.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_41 :
    majCellCheck 63 41 (majRow_63.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_42 :
    majCellCheck 63 42 (majRow_63.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_43 :
    majCellCheck 63 43 (majRow_63.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_44 :
    majCellCheck 63 44 (majRow_63.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_45 :
    majCellCheck 63 45 (majRow_63.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_46 :
    majCellCheck 63 46 (majRow_63.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_47 :
    majCellCheck 63 47 (majRow_63.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_48 :
    majCellCheck 63 48 (majRow_63.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_49 :
    majCellCheck 63 49 (majRow_63.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_50 :
    majCellCheck 63 50 (majRow_63.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_51 :
    majCellCheck 63 51 (majRow_63.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_52 :
    majCellCheck 63 52 (majRow_63.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_53 :
    majCellCheck 63 53 (majRow_63.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_54 :
    majCellCheck 63 54 (majRow_63.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_55 :
    majCellCheck 63 55 (majRow_63.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_56 :
    majCellCheck 63 56 (majRow_63.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_57 :
    majCellCheck 63 57 (majRow_63.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_58 :
    majCellCheck 63 58 (majRow_63.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_59 :
    majCellCheck 63 59 (majRow_63.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_60 :
    majCellCheck 63 60 (majRow_63.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_61 :
    majCellCheck 63 61 (majRow_63.getD 61 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_62 :
    majCellCheck 63 62 (majRow_63.getD 62 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_cell_63 :
    majCellCheck 63 63 (majRow_63.getD 63 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_63_all : ∀ l, l ≤ 63 →
    majCellCheck 63 l (majRow_63.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_63_cell_0, majRow_63_cell_1, majRow_63_cell_2, majRow_63_cell_3, majRow_63_cell_4, majRow_63_cell_5, majRow_63_cell_6, majRow_63_cell_7, majRow_63_cell_8, majRow_63_cell_9, majRow_63_cell_10, majRow_63_cell_11, majRow_63_cell_12, majRow_63_cell_13, majRow_63_cell_14, majRow_63_cell_15, majRow_63_cell_16, majRow_63_cell_17, majRow_63_cell_18, majRow_63_cell_19, majRow_63_cell_20, majRow_63_cell_21, majRow_63_cell_22, majRow_63_cell_23, majRow_63_cell_24, majRow_63_cell_25, majRow_63_cell_26, majRow_63_cell_27, majRow_63_cell_28, majRow_63_cell_29, majRow_63_cell_30, majRow_63_cell_31, majRow_63_cell_32, majRow_63_cell_33, majRow_63_cell_34, majRow_63_cell_35, majRow_63_cell_36, majRow_63_cell_37, majRow_63_cell_38, majRow_63_cell_39, majRow_63_cell_40, majRow_63_cell_41, majRow_63_cell_42, majRow_63_cell_43, majRow_63_cell_44, majRow_63_cell_45, majRow_63_cell_46, majRow_63_cell_47, majRow_63_cell_48, majRow_63_cell_49, majRow_63_cell_50, majRow_63_cell_51, majRow_63_cell_52, majRow_63_cell_53, majRow_63_cell_54, majRow_63_cell_55, majRow_63_cell_56, majRow_63_cell_57, majRow_63_cell_58, majRow_63_cell_59, majRow_63_cell_60, majRow_63_cell_61, majRow_63_cell_62, majRow_63_cell_63]

end PartialBalayage.Maximal.Square
