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

def majRow_55 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_55_cell_0 :
    majCellCheck 55 0 (majRow_55.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_1 :
    majCellCheck 55 1 (majRow_55.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_2 :
    majCellCheck 55 2 (majRow_55.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_3 :
    majCellCheck 55 3 (majRow_55.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_4 :
    majCellCheck 55 4 (majRow_55.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_5 :
    majCellCheck 55 5 (majRow_55.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_6 :
    majCellCheck 55 6 (majRow_55.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_7 :
    majCellCheck 55 7 (majRow_55.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_8 :
    majCellCheck 55 8 (majRow_55.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_9 :
    majCellCheck 55 9 (majRow_55.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_10 :
    majCellCheck 55 10 (majRow_55.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_11 :
    majCellCheck 55 11 (majRow_55.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_12 :
    majCellCheck 55 12 (majRow_55.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_13 :
    majCellCheck 55 13 (majRow_55.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_14 :
    majCellCheck 55 14 (majRow_55.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_15 :
    majCellCheck 55 15 (majRow_55.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_16 :
    majCellCheck 55 16 (majRow_55.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_17 :
    majCellCheck 55 17 (majRow_55.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_18 :
    majCellCheck 55 18 (majRow_55.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_19 :
    majCellCheck 55 19 (majRow_55.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_20 :
    majCellCheck 55 20 (majRow_55.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_21 :
    majCellCheck 55 21 (majRow_55.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_22 :
    majCellCheck 55 22 (majRow_55.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_23 :
    majCellCheck 55 23 (majRow_55.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_24 :
    majCellCheck 55 24 (majRow_55.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_25 :
    majCellCheck 55 25 (majRow_55.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_26 :
    majCellCheck 55 26 (majRow_55.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_27 :
    majCellCheck 55 27 (majRow_55.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_28 :
    majCellCheck 55 28 (majRow_55.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_29 :
    majCellCheck 55 29 (majRow_55.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_30 :
    majCellCheck 55 30 (majRow_55.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_31 :
    majCellCheck 55 31 (majRow_55.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_32 :
    majCellCheck 55 32 (majRow_55.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_33 :
    majCellCheck 55 33 (majRow_55.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_34 :
    majCellCheck 55 34 (majRow_55.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_35 :
    majCellCheck 55 35 (majRow_55.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_36 :
    majCellCheck 55 36 (majRow_55.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_37 :
    majCellCheck 55 37 (majRow_55.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_38 :
    majCellCheck 55 38 (majRow_55.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_39 :
    majCellCheck 55 39 (majRow_55.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_40 :
    majCellCheck 55 40 (majRow_55.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_41 :
    majCellCheck 55 41 (majRow_55.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_42 :
    majCellCheck 55 42 (majRow_55.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_43 :
    majCellCheck 55 43 (majRow_55.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_44 :
    majCellCheck 55 44 (majRow_55.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_45 :
    majCellCheck 55 45 (majRow_55.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_46 :
    majCellCheck 55 46 (majRow_55.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_47 :
    majCellCheck 55 47 (majRow_55.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_48 :
    majCellCheck 55 48 (majRow_55.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_49 :
    majCellCheck 55 49 (majRow_55.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_50 :
    majCellCheck 55 50 (majRow_55.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_51 :
    majCellCheck 55 51 (majRow_55.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_52 :
    majCellCheck 55 52 (majRow_55.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_53 :
    majCellCheck 55 53 (majRow_55.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_54 :
    majCellCheck 55 54 (majRow_55.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_cell_55 :
    majCellCheck 55 55 (majRow_55.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_55_all : ∀ l, l ≤ 55 →
    majCellCheck 55 l (majRow_55.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_55_cell_0, majRow_55_cell_1, majRow_55_cell_2, majRow_55_cell_3, majRow_55_cell_4, majRow_55_cell_5, majRow_55_cell_6, majRow_55_cell_7, majRow_55_cell_8, majRow_55_cell_9, majRow_55_cell_10, majRow_55_cell_11, majRow_55_cell_12, majRow_55_cell_13, majRow_55_cell_14, majRow_55_cell_15, majRow_55_cell_16, majRow_55_cell_17, majRow_55_cell_18, majRow_55_cell_19, majRow_55_cell_20, majRow_55_cell_21, majRow_55_cell_22, majRow_55_cell_23, majRow_55_cell_24, majRow_55_cell_25, majRow_55_cell_26, majRow_55_cell_27, majRow_55_cell_28, majRow_55_cell_29, majRow_55_cell_30, majRow_55_cell_31, majRow_55_cell_32, majRow_55_cell_33, majRow_55_cell_34, majRow_55_cell_35, majRow_55_cell_36, majRow_55_cell_37, majRow_55_cell_38, majRow_55_cell_39, majRow_55_cell_40, majRow_55_cell_41, majRow_55_cell_42, majRow_55_cell_43, majRow_55_cell_44, majRow_55_cell_45, majRow_55_cell_46, majRow_55_cell_47, majRow_55_cell_48, majRow_55_cell_49, majRow_55_cell_50, majRow_55_cell_51, majRow_55_cell_52, majRow_55_cell_53, majRow_55_cell_54, majRow_55_cell_55]

def majRow_56 : List (MajTree × MajTree) := [
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_56_cell_0 :
    majCellCheck 56 0 (majRow_56.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_1 :
    majCellCheck 56 1 (majRow_56.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_2 :
    majCellCheck 56 2 (majRow_56.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_3 :
    majCellCheck 56 3 (majRow_56.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_4 :
    majCellCheck 56 4 (majRow_56.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_5 :
    majCellCheck 56 5 (majRow_56.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_6 :
    majCellCheck 56 6 (majRow_56.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_7 :
    majCellCheck 56 7 (majRow_56.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_8 :
    majCellCheck 56 8 (majRow_56.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_9 :
    majCellCheck 56 9 (majRow_56.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_10 :
    majCellCheck 56 10 (majRow_56.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_11 :
    majCellCheck 56 11 (majRow_56.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_12 :
    majCellCheck 56 12 (majRow_56.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_13 :
    majCellCheck 56 13 (majRow_56.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_14 :
    majCellCheck 56 14 (majRow_56.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_15 :
    majCellCheck 56 15 (majRow_56.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_16 :
    majCellCheck 56 16 (majRow_56.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_17 :
    majCellCheck 56 17 (majRow_56.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_18 :
    majCellCheck 56 18 (majRow_56.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_19 :
    majCellCheck 56 19 (majRow_56.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_20 :
    majCellCheck 56 20 (majRow_56.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_21 :
    majCellCheck 56 21 (majRow_56.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_22 :
    majCellCheck 56 22 (majRow_56.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_23 :
    majCellCheck 56 23 (majRow_56.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_24 :
    majCellCheck 56 24 (majRow_56.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_25 :
    majCellCheck 56 25 (majRow_56.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_26 :
    majCellCheck 56 26 (majRow_56.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_27 :
    majCellCheck 56 27 (majRow_56.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_28 :
    majCellCheck 56 28 (majRow_56.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_29 :
    majCellCheck 56 29 (majRow_56.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_30 :
    majCellCheck 56 30 (majRow_56.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_31 :
    majCellCheck 56 31 (majRow_56.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_32 :
    majCellCheck 56 32 (majRow_56.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_33 :
    majCellCheck 56 33 (majRow_56.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_34 :
    majCellCheck 56 34 (majRow_56.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_35 :
    majCellCheck 56 35 (majRow_56.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_36 :
    majCellCheck 56 36 (majRow_56.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_37 :
    majCellCheck 56 37 (majRow_56.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_38 :
    majCellCheck 56 38 (majRow_56.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_39 :
    majCellCheck 56 39 (majRow_56.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_40 :
    majCellCheck 56 40 (majRow_56.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_41 :
    majCellCheck 56 41 (majRow_56.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_42 :
    majCellCheck 56 42 (majRow_56.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_43 :
    majCellCheck 56 43 (majRow_56.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_44 :
    majCellCheck 56 44 (majRow_56.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_45 :
    majCellCheck 56 45 (majRow_56.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_46 :
    majCellCheck 56 46 (majRow_56.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_47 :
    majCellCheck 56 47 (majRow_56.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_48 :
    majCellCheck 56 48 (majRow_56.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_49 :
    majCellCheck 56 49 (majRow_56.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_50 :
    majCellCheck 56 50 (majRow_56.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_51 :
    majCellCheck 56 51 (majRow_56.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_52 :
    majCellCheck 56 52 (majRow_56.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_53 :
    majCellCheck 56 53 (majRow_56.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_54 :
    majCellCheck 56 54 (majRow_56.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_55 :
    majCellCheck 56 55 (majRow_56.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_cell_56 :
    majCellCheck 56 56 (majRow_56.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_56_all : ∀ l, l ≤ 56 →
    majCellCheck 56 l (majRow_56.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_56_cell_0, majRow_56_cell_1, majRow_56_cell_2, majRow_56_cell_3, majRow_56_cell_4, majRow_56_cell_5, majRow_56_cell_6, majRow_56_cell_7, majRow_56_cell_8, majRow_56_cell_9, majRow_56_cell_10, majRow_56_cell_11, majRow_56_cell_12, majRow_56_cell_13, majRow_56_cell_14, majRow_56_cell_15, majRow_56_cell_16, majRow_56_cell_17, majRow_56_cell_18, majRow_56_cell_19, majRow_56_cell_20, majRow_56_cell_21, majRow_56_cell_22, majRow_56_cell_23, majRow_56_cell_24, majRow_56_cell_25, majRow_56_cell_26, majRow_56_cell_27, majRow_56_cell_28, majRow_56_cell_29, majRow_56_cell_30, majRow_56_cell_31, majRow_56_cell_32, majRow_56_cell_33, majRow_56_cell_34, majRow_56_cell_35, majRow_56_cell_36, majRow_56_cell_37, majRow_56_cell_38, majRow_56_cell_39, majRow_56_cell_40, majRow_56_cell_41, majRow_56_cell_42, majRow_56_cell_43, majRow_56_cell_44, majRow_56_cell_45, majRow_56_cell_46, majRow_56_cell_47, majRow_56_cell_48, majRow_56_cell_49, majRow_56_cell_50, majRow_56_cell_51, majRow_56_cell_52, majRow_56_cell_53, majRow_56_cell_54, majRow_56_cell_55, majRow_56_cell_56]

def majRow_57 : List (MajTree × MajTree) := [
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_57_cell_0 :
    majCellCheck 57 0 (majRow_57.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_1 :
    majCellCheck 57 1 (majRow_57.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_2 :
    majCellCheck 57 2 (majRow_57.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_3 :
    majCellCheck 57 3 (majRow_57.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_4 :
    majCellCheck 57 4 (majRow_57.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_5 :
    majCellCheck 57 5 (majRow_57.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_6 :
    majCellCheck 57 6 (majRow_57.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_7 :
    majCellCheck 57 7 (majRow_57.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_8 :
    majCellCheck 57 8 (majRow_57.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_9 :
    majCellCheck 57 9 (majRow_57.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_10 :
    majCellCheck 57 10 (majRow_57.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_11 :
    majCellCheck 57 11 (majRow_57.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_12 :
    majCellCheck 57 12 (majRow_57.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_13 :
    majCellCheck 57 13 (majRow_57.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_14 :
    majCellCheck 57 14 (majRow_57.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_15 :
    majCellCheck 57 15 (majRow_57.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_16 :
    majCellCheck 57 16 (majRow_57.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_17 :
    majCellCheck 57 17 (majRow_57.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_18 :
    majCellCheck 57 18 (majRow_57.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_19 :
    majCellCheck 57 19 (majRow_57.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_20 :
    majCellCheck 57 20 (majRow_57.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_21 :
    majCellCheck 57 21 (majRow_57.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_22 :
    majCellCheck 57 22 (majRow_57.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_23 :
    majCellCheck 57 23 (majRow_57.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_24 :
    majCellCheck 57 24 (majRow_57.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_25 :
    majCellCheck 57 25 (majRow_57.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_26 :
    majCellCheck 57 26 (majRow_57.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_27 :
    majCellCheck 57 27 (majRow_57.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_28 :
    majCellCheck 57 28 (majRow_57.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_29 :
    majCellCheck 57 29 (majRow_57.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_30 :
    majCellCheck 57 30 (majRow_57.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_31 :
    majCellCheck 57 31 (majRow_57.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_32 :
    majCellCheck 57 32 (majRow_57.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_33 :
    majCellCheck 57 33 (majRow_57.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_34 :
    majCellCheck 57 34 (majRow_57.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_35 :
    majCellCheck 57 35 (majRow_57.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_36 :
    majCellCheck 57 36 (majRow_57.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_37 :
    majCellCheck 57 37 (majRow_57.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_38 :
    majCellCheck 57 38 (majRow_57.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_39 :
    majCellCheck 57 39 (majRow_57.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_40 :
    majCellCheck 57 40 (majRow_57.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_41 :
    majCellCheck 57 41 (majRow_57.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_42 :
    majCellCheck 57 42 (majRow_57.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_43 :
    majCellCheck 57 43 (majRow_57.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_44 :
    majCellCheck 57 44 (majRow_57.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_45 :
    majCellCheck 57 45 (majRow_57.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_46 :
    majCellCheck 57 46 (majRow_57.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_47 :
    majCellCheck 57 47 (majRow_57.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_48 :
    majCellCheck 57 48 (majRow_57.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_49 :
    majCellCheck 57 49 (majRow_57.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_50 :
    majCellCheck 57 50 (majRow_57.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_51 :
    majCellCheck 57 51 (majRow_57.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_52 :
    majCellCheck 57 52 (majRow_57.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_53 :
    majCellCheck 57 53 (majRow_57.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_54 :
    majCellCheck 57 54 (majRow_57.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_55 :
    majCellCheck 57 55 (majRow_57.getD 55 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_56 :
    majCellCheck 57 56 (majRow_57.getD 56 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_cell_57 :
    majCellCheck 57 57 (majRow_57.getD 57 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_57_all : ∀ l, l ≤ 57 →
    majCellCheck 57 l (majRow_57.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_57_cell_0, majRow_57_cell_1, majRow_57_cell_2, majRow_57_cell_3, majRow_57_cell_4, majRow_57_cell_5, majRow_57_cell_6, majRow_57_cell_7, majRow_57_cell_8, majRow_57_cell_9, majRow_57_cell_10, majRow_57_cell_11, majRow_57_cell_12, majRow_57_cell_13, majRow_57_cell_14, majRow_57_cell_15, majRow_57_cell_16, majRow_57_cell_17, majRow_57_cell_18, majRow_57_cell_19, majRow_57_cell_20, majRow_57_cell_21, majRow_57_cell_22, majRow_57_cell_23, majRow_57_cell_24, majRow_57_cell_25, majRow_57_cell_26, majRow_57_cell_27, majRow_57_cell_28, majRow_57_cell_29, majRow_57_cell_30, majRow_57_cell_31, majRow_57_cell_32, majRow_57_cell_33, majRow_57_cell_34, majRow_57_cell_35, majRow_57_cell_36, majRow_57_cell_37, majRow_57_cell_38, majRow_57_cell_39, majRow_57_cell_40, majRow_57_cell_41, majRow_57_cell_42, majRow_57_cell_43, majRow_57_cell_44, majRow_57_cell_45, majRow_57_cell_46, majRow_57_cell_47, majRow_57_cell_48, majRow_57_cell_49, majRow_57_cell_50, majRow_57_cell_51, majRow_57_cell_52, majRow_57_cell_53, majRow_57_cell_54, majRow_57_cell_55, majRow_57_cell_56, majRow_57_cell_57]

end PartialBalayage.Maximal.Square
