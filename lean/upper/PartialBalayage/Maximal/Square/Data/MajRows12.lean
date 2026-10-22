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

def majRow_58 : List (MajTree × MajTree) := [
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_58_cell_0 :
    majCellCheck 58 0 (majRow_58.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_1 :
    majCellCheck 58 1 (majRow_58.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_2 :
    majCellCheck 58 2 (majRow_58.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_3 :
    majCellCheck 58 3 (majRow_58.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_4 :
    majCellCheck 58 4 (majRow_58.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_5 :
    majCellCheck 58 5 (majRow_58.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_6 :
    majCellCheck 58 6 (majRow_58.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_7 :
    majCellCheck 58 7 (majRow_58.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_8 :
    majCellCheck 58 8 (majRow_58.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_9 :
    majCellCheck 58 9 (majRow_58.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_10 :
    majCellCheck 58 10 (majRow_58.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_11 :
    majCellCheck 58 11 (majRow_58.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_12 :
    majCellCheck 58 12 (majRow_58.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_13 :
    majCellCheck 58 13 (majRow_58.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_14 :
    majCellCheck 58 14 (majRow_58.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_15 :
    majCellCheck 58 15 (majRow_58.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_16 :
    majCellCheck 58 16 (majRow_58.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_17 :
    majCellCheck 58 17 (majRow_58.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_18 :
    majCellCheck 58 18 (majRow_58.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_19 :
    majCellCheck 58 19 (majRow_58.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_20 :
    majCellCheck 58 20 (majRow_58.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_21 :
    majCellCheck 58 21 (majRow_58.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_22 :
    majCellCheck 58 22 (majRow_58.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_23 :
    majCellCheck 58 23 (majRow_58.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_24 :
    majCellCheck 58 24 (majRow_58.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_25 :
    majCellCheck 58 25 (majRow_58.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_26 :
    majCellCheck 58 26 (majRow_58.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_27 :
    majCellCheck 58 27 (majRow_58.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_28 :
    majCellCheck 58 28 (majRow_58.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_29 :
    majCellCheck 58 29 (majRow_58.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_30 :
    majCellCheck 58 30 (majRow_58.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_31 :
    majCellCheck 58 31 (majRow_58.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_32 :
    majCellCheck 58 32 (majRow_58.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_33 :
    majCellCheck 58 33 (majRow_58.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_34 :
    majCellCheck 58 34 (majRow_58.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_35 :
    majCellCheck 58 35 (majRow_58.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_36 :
    majCellCheck 58 36 (majRow_58.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_37 :
    majCellCheck 58 37 (majRow_58.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_38 :
    majCellCheck 58 38 (majRow_58.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_39 :
    majCellCheck 58 39 (majRow_58.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_40 :
    majCellCheck 58 40 (majRow_58.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_41 :
    majCellCheck 58 41 (majRow_58.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_42 :
    majCellCheck 58 42 (majRow_58.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_43 :
    majCellCheck 58 43 (majRow_58.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_44 :
    majCellCheck 58 44 (majRow_58.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_45 :
    majCellCheck 58 45 (majRow_58.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_46 :
    majCellCheck 58 46 (majRow_58.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_47 :
    majCellCheck 58 47 (majRow_58.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_48 :
    majCellCheck 58 48 (majRow_58.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_49 :
    majCellCheck 58 49 (majRow_58.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_50 :
    majCellCheck 58 50 (majRow_58.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_51 :
    majCellCheck 58 51 (majRow_58.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_52 :
    majCellCheck 58 52 (majRow_58.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_53 :
    majCellCheck 58 53 (majRow_58.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_54 :
    majCellCheck 58 54 (majRow_58.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_55 :
    majCellCheck 58 55 (majRow_58.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_56 :
    majCellCheck 58 56 (majRow_58.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_57 :
    majCellCheck 58 57 (majRow_58.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_cell_58 :
    majCellCheck 58 58 (majRow_58.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_58_all : ∀ l, l ≤ 58 →
    majCellCheck 58 l (majRow_58.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_58_cell_0, majRow_58_cell_1, majRow_58_cell_2, majRow_58_cell_3, majRow_58_cell_4, majRow_58_cell_5, majRow_58_cell_6, majRow_58_cell_7, majRow_58_cell_8, majRow_58_cell_9, majRow_58_cell_10, majRow_58_cell_11, majRow_58_cell_12, majRow_58_cell_13, majRow_58_cell_14, majRow_58_cell_15, majRow_58_cell_16, majRow_58_cell_17, majRow_58_cell_18, majRow_58_cell_19, majRow_58_cell_20, majRow_58_cell_21, majRow_58_cell_22, majRow_58_cell_23, majRow_58_cell_24, majRow_58_cell_25, majRow_58_cell_26, majRow_58_cell_27, majRow_58_cell_28, majRow_58_cell_29, majRow_58_cell_30, majRow_58_cell_31, majRow_58_cell_32, majRow_58_cell_33, majRow_58_cell_34, majRow_58_cell_35, majRow_58_cell_36, majRow_58_cell_37, majRow_58_cell_38, majRow_58_cell_39, majRow_58_cell_40, majRow_58_cell_41, majRow_58_cell_42, majRow_58_cell_43, majRow_58_cell_44, majRow_58_cell_45, majRow_58_cell_46, majRow_58_cell_47, majRow_58_cell_48, majRow_58_cell_49, majRow_58_cell_50, majRow_58_cell_51, majRow_58_cell_52, majRow_58_cell_53, majRow_58_cell_54, majRow_58_cell_55, majRow_58_cell_56, majRow_58_cell_57, majRow_58_cell_58]

def majRow_59 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_59_cell_0 :
    majCellCheck 59 0 (majRow_59.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_1 :
    majCellCheck 59 1 (majRow_59.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_2 :
    majCellCheck 59 2 (majRow_59.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_3 :
    majCellCheck 59 3 (majRow_59.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_4 :
    majCellCheck 59 4 (majRow_59.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_5 :
    majCellCheck 59 5 (majRow_59.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_6 :
    majCellCheck 59 6 (majRow_59.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_7 :
    majCellCheck 59 7 (majRow_59.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_8 :
    majCellCheck 59 8 (majRow_59.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_9 :
    majCellCheck 59 9 (majRow_59.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_10 :
    majCellCheck 59 10 (majRow_59.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_11 :
    majCellCheck 59 11 (majRow_59.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_12 :
    majCellCheck 59 12 (majRow_59.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_13 :
    majCellCheck 59 13 (majRow_59.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_14 :
    majCellCheck 59 14 (majRow_59.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_15 :
    majCellCheck 59 15 (majRow_59.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_16 :
    majCellCheck 59 16 (majRow_59.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_17 :
    majCellCheck 59 17 (majRow_59.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_18 :
    majCellCheck 59 18 (majRow_59.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_19 :
    majCellCheck 59 19 (majRow_59.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_20 :
    majCellCheck 59 20 (majRow_59.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_21 :
    majCellCheck 59 21 (majRow_59.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_22 :
    majCellCheck 59 22 (majRow_59.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_23 :
    majCellCheck 59 23 (majRow_59.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_24 :
    majCellCheck 59 24 (majRow_59.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_25 :
    majCellCheck 59 25 (majRow_59.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_26 :
    majCellCheck 59 26 (majRow_59.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_27 :
    majCellCheck 59 27 (majRow_59.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_28 :
    majCellCheck 59 28 (majRow_59.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_29 :
    majCellCheck 59 29 (majRow_59.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_30 :
    majCellCheck 59 30 (majRow_59.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_31 :
    majCellCheck 59 31 (majRow_59.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_32 :
    majCellCheck 59 32 (majRow_59.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_33 :
    majCellCheck 59 33 (majRow_59.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_34 :
    majCellCheck 59 34 (majRow_59.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_35 :
    majCellCheck 59 35 (majRow_59.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_36 :
    majCellCheck 59 36 (majRow_59.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_37 :
    majCellCheck 59 37 (majRow_59.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_38 :
    majCellCheck 59 38 (majRow_59.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_39 :
    majCellCheck 59 39 (majRow_59.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_40 :
    majCellCheck 59 40 (majRow_59.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_41 :
    majCellCheck 59 41 (majRow_59.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_42 :
    majCellCheck 59 42 (majRow_59.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_43 :
    majCellCheck 59 43 (majRow_59.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_44 :
    majCellCheck 59 44 (majRow_59.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_45 :
    majCellCheck 59 45 (majRow_59.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_46 :
    majCellCheck 59 46 (majRow_59.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_47 :
    majCellCheck 59 47 (majRow_59.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_48 :
    majCellCheck 59 48 (majRow_59.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_49 :
    majCellCheck 59 49 (majRow_59.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_50 :
    majCellCheck 59 50 (majRow_59.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_51 :
    majCellCheck 59 51 (majRow_59.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_52 :
    majCellCheck 59 52 (majRow_59.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_53 :
    majCellCheck 59 53 (majRow_59.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_54 :
    majCellCheck 59 54 (majRow_59.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_55 :
    majCellCheck 59 55 (majRow_59.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_56 :
    majCellCheck 59 56 (majRow_59.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_57 :
    majCellCheck 59 57 (majRow_59.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_58 :
    majCellCheck 59 58 (majRow_59.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_cell_59 :
    majCellCheck 59 59 (majRow_59.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_59_all : ∀ l, l ≤ 59 →
    majCellCheck 59 l (majRow_59.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_59_cell_0, majRow_59_cell_1, majRow_59_cell_2, majRow_59_cell_3, majRow_59_cell_4, majRow_59_cell_5, majRow_59_cell_6, majRow_59_cell_7, majRow_59_cell_8, majRow_59_cell_9, majRow_59_cell_10, majRow_59_cell_11, majRow_59_cell_12, majRow_59_cell_13, majRow_59_cell_14, majRow_59_cell_15, majRow_59_cell_16, majRow_59_cell_17, majRow_59_cell_18, majRow_59_cell_19, majRow_59_cell_20, majRow_59_cell_21, majRow_59_cell_22, majRow_59_cell_23, majRow_59_cell_24, majRow_59_cell_25, majRow_59_cell_26, majRow_59_cell_27, majRow_59_cell_28, majRow_59_cell_29, majRow_59_cell_30, majRow_59_cell_31, majRow_59_cell_32, majRow_59_cell_33, majRow_59_cell_34, majRow_59_cell_35, majRow_59_cell_36, majRow_59_cell_37, majRow_59_cell_38, majRow_59_cell_39, majRow_59_cell_40, majRow_59_cell_41, majRow_59_cell_42, majRow_59_cell_43, majRow_59_cell_44, majRow_59_cell_45, majRow_59_cell_46, majRow_59_cell_47, majRow_59_cell_48, majRow_59_cell_49, majRow_59_cell_50, majRow_59_cell_51, majRow_59_cell_52, majRow_59_cell_53, majRow_59_cell_54, majRow_59_cell_55, majRow_59_cell_56, majRow_59_cell_57, majRow_59_cell_58, majRow_59_cell_59]

def majRow_60 : List (MajTree × MajTree) := [
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_60_cell_0 :
    majCellCheck 60 0 (majRow_60.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_1 :
    majCellCheck 60 1 (majRow_60.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_2 :
    majCellCheck 60 2 (majRow_60.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_3 :
    majCellCheck 60 3 (majRow_60.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_4 :
    majCellCheck 60 4 (majRow_60.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_5 :
    majCellCheck 60 5 (majRow_60.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_6 :
    majCellCheck 60 6 (majRow_60.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_7 :
    majCellCheck 60 7 (majRow_60.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_8 :
    majCellCheck 60 8 (majRow_60.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_9 :
    majCellCheck 60 9 (majRow_60.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_10 :
    majCellCheck 60 10 (majRow_60.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_11 :
    majCellCheck 60 11 (majRow_60.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_12 :
    majCellCheck 60 12 (majRow_60.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_13 :
    majCellCheck 60 13 (majRow_60.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_14 :
    majCellCheck 60 14 (majRow_60.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_15 :
    majCellCheck 60 15 (majRow_60.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_16 :
    majCellCheck 60 16 (majRow_60.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_17 :
    majCellCheck 60 17 (majRow_60.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_18 :
    majCellCheck 60 18 (majRow_60.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_19 :
    majCellCheck 60 19 (majRow_60.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_20 :
    majCellCheck 60 20 (majRow_60.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_21 :
    majCellCheck 60 21 (majRow_60.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_22 :
    majCellCheck 60 22 (majRow_60.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_23 :
    majCellCheck 60 23 (majRow_60.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_24 :
    majCellCheck 60 24 (majRow_60.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_25 :
    majCellCheck 60 25 (majRow_60.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_26 :
    majCellCheck 60 26 (majRow_60.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_27 :
    majCellCheck 60 27 (majRow_60.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_28 :
    majCellCheck 60 28 (majRow_60.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_29 :
    majCellCheck 60 29 (majRow_60.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_30 :
    majCellCheck 60 30 (majRow_60.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_31 :
    majCellCheck 60 31 (majRow_60.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_32 :
    majCellCheck 60 32 (majRow_60.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_33 :
    majCellCheck 60 33 (majRow_60.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_34 :
    majCellCheck 60 34 (majRow_60.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_35 :
    majCellCheck 60 35 (majRow_60.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_36 :
    majCellCheck 60 36 (majRow_60.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_37 :
    majCellCheck 60 37 (majRow_60.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_38 :
    majCellCheck 60 38 (majRow_60.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_39 :
    majCellCheck 60 39 (majRow_60.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_40 :
    majCellCheck 60 40 (majRow_60.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_41 :
    majCellCheck 60 41 (majRow_60.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_42 :
    majCellCheck 60 42 (majRow_60.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_43 :
    majCellCheck 60 43 (majRow_60.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_44 :
    majCellCheck 60 44 (majRow_60.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_45 :
    majCellCheck 60 45 (majRow_60.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_46 :
    majCellCheck 60 46 (majRow_60.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_47 :
    majCellCheck 60 47 (majRow_60.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_48 :
    majCellCheck 60 48 (majRow_60.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_49 :
    majCellCheck 60 49 (majRow_60.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_50 :
    majCellCheck 60 50 (majRow_60.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_51 :
    majCellCheck 60 51 (majRow_60.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_52 :
    majCellCheck 60 52 (majRow_60.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_53 :
    majCellCheck 60 53 (majRow_60.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_54 :
    majCellCheck 60 54 (majRow_60.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_55 :
    majCellCheck 60 55 (majRow_60.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_56 :
    majCellCheck 60 56 (majRow_60.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_57 :
    majCellCheck 60 57 (majRow_60.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_58 :
    majCellCheck 60 58 (majRow_60.getD 58 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_59 :
    majCellCheck 60 59 (majRow_60.getD 59 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_cell_60 :
    majCellCheck 60 60 (majRow_60.getD 60 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_60_all : ∀ l, l ≤ 60 →
    majCellCheck 60 l (majRow_60.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_60_cell_0, majRow_60_cell_1, majRow_60_cell_2, majRow_60_cell_3, majRow_60_cell_4, majRow_60_cell_5, majRow_60_cell_6, majRow_60_cell_7, majRow_60_cell_8, majRow_60_cell_9, majRow_60_cell_10, majRow_60_cell_11, majRow_60_cell_12, majRow_60_cell_13, majRow_60_cell_14, majRow_60_cell_15, majRow_60_cell_16, majRow_60_cell_17, majRow_60_cell_18, majRow_60_cell_19, majRow_60_cell_20, majRow_60_cell_21, majRow_60_cell_22, majRow_60_cell_23, majRow_60_cell_24, majRow_60_cell_25, majRow_60_cell_26, majRow_60_cell_27, majRow_60_cell_28, majRow_60_cell_29, majRow_60_cell_30, majRow_60_cell_31, majRow_60_cell_32, majRow_60_cell_33, majRow_60_cell_34, majRow_60_cell_35, majRow_60_cell_36, majRow_60_cell_37, majRow_60_cell_38, majRow_60_cell_39, majRow_60_cell_40, majRow_60_cell_41, majRow_60_cell_42, majRow_60_cell_43, majRow_60_cell_44, majRow_60_cell_45, majRow_60_cell_46, majRow_60_cell_47, majRow_60_cell_48, majRow_60_cell_49, majRow_60_cell_50, majRow_60_cell_51, majRow_60_cell_52, majRow_60_cell_53, majRow_60_cell_54, majRow_60_cell_55, majRow_60_cell_56, majRow_60_cell_57, majRow_60_cell_58, majRow_60_cell_59, majRow_60_cell_60]

end PartialBalayage.Maximal.Square
