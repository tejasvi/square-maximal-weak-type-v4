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

def majRow_50 : List (MajTree × MajTree) := [
  ((.node (.leaf 51) (.leaf 51) (.leaf 51) (.leaf 51)), (.node (.leaf 52) (.leaf 151) (.leaf 151) (.leaf 151))),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_50_cell_0 :
    majCellCheck 50 0 (majRow_50.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_1 :
    majCellCheck 50 1 (majRow_50.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_2 :
    majCellCheck 50 2 (majRow_50.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_3 :
    majCellCheck 50 3 (majRow_50.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_4 :
    majCellCheck 50 4 (majRow_50.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_5 :
    majCellCheck 50 5 (majRow_50.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_6 :
    majCellCheck 50 6 (majRow_50.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_7 :
    majCellCheck 50 7 (majRow_50.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_8 :
    majCellCheck 50 8 (majRow_50.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_9 :
    majCellCheck 50 9 (majRow_50.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_10 :
    majCellCheck 50 10 (majRow_50.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_11 :
    majCellCheck 50 11 (majRow_50.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_12 :
    majCellCheck 50 12 (majRow_50.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_13 :
    majCellCheck 50 13 (majRow_50.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_14 :
    majCellCheck 50 14 (majRow_50.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_15 :
    majCellCheck 50 15 (majRow_50.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_16 :
    majCellCheck 50 16 (majRow_50.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_17 :
    majCellCheck 50 17 (majRow_50.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_18 :
    majCellCheck 50 18 (majRow_50.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_19 :
    majCellCheck 50 19 (majRow_50.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_20 :
    majCellCheck 50 20 (majRow_50.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_21 :
    majCellCheck 50 21 (majRow_50.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_22 :
    majCellCheck 50 22 (majRow_50.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_23 :
    majCellCheck 50 23 (majRow_50.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_24 :
    majCellCheck 50 24 (majRow_50.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_25 :
    majCellCheck 50 25 (majRow_50.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_26 :
    majCellCheck 50 26 (majRow_50.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_27 :
    majCellCheck 50 27 (majRow_50.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_28 :
    majCellCheck 50 28 (majRow_50.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_29 :
    majCellCheck 50 29 (majRow_50.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_30 :
    majCellCheck 50 30 (majRow_50.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_31 :
    majCellCheck 50 31 (majRow_50.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_32 :
    majCellCheck 50 32 (majRow_50.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_33 :
    majCellCheck 50 33 (majRow_50.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_34 :
    majCellCheck 50 34 (majRow_50.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_35 :
    majCellCheck 50 35 (majRow_50.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_36 :
    majCellCheck 50 36 (majRow_50.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_37 :
    majCellCheck 50 37 (majRow_50.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_38 :
    majCellCheck 50 38 (majRow_50.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_39 :
    majCellCheck 50 39 (majRow_50.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_40 :
    majCellCheck 50 40 (majRow_50.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_41 :
    majCellCheck 50 41 (majRow_50.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_42 :
    majCellCheck 50 42 (majRow_50.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_43 :
    majCellCheck 50 43 (majRow_50.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_44 :
    majCellCheck 50 44 (majRow_50.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_45 :
    majCellCheck 50 45 (majRow_50.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_46 :
    majCellCheck 50 46 (majRow_50.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_47 :
    majCellCheck 50 47 (majRow_50.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_48 :
    majCellCheck 50 48 (majRow_50.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_49 :
    majCellCheck 50 49 (majRow_50.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_cell_50 :
    majCellCheck 50 50 (majRow_50.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_50_all : ∀ l, l ≤ 50 →
    majCellCheck 50 l (majRow_50.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_50_cell_0, majRow_50_cell_1, majRow_50_cell_2, majRow_50_cell_3, majRow_50_cell_4, majRow_50_cell_5, majRow_50_cell_6, majRow_50_cell_7, majRow_50_cell_8, majRow_50_cell_9, majRow_50_cell_10, majRow_50_cell_11, majRow_50_cell_12, majRow_50_cell_13, majRow_50_cell_14, majRow_50_cell_15, majRow_50_cell_16, majRow_50_cell_17, majRow_50_cell_18, majRow_50_cell_19, majRow_50_cell_20, majRow_50_cell_21, majRow_50_cell_22, majRow_50_cell_23, majRow_50_cell_24, majRow_50_cell_25, majRow_50_cell_26, majRow_50_cell_27, majRow_50_cell_28, majRow_50_cell_29, majRow_50_cell_30, majRow_50_cell_31, majRow_50_cell_32, majRow_50_cell_33, majRow_50_cell_34, majRow_50_cell_35, majRow_50_cell_36, majRow_50_cell_37, majRow_50_cell_38, majRow_50_cell_39, majRow_50_cell_40, majRow_50_cell_41, majRow_50_cell_42, majRow_50_cell_43, majRow_50_cell_44, majRow_50_cell_45, majRow_50_cell_46, majRow_50_cell_47, majRow_50_cell_48, majRow_50_cell_49, majRow_50_cell_50]

def majRow_51 : List (MajTree × MajTree) := [
  ((.node (.leaf 52) (.leaf 52) (.leaf 52) (.leaf 52)), (.node (.leaf 53) (.leaf 53) (.leaf 53) (.leaf 53))),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_51_cell_0 :
    majCellCheck 51 0 (majRow_51.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_1 :
    majCellCheck 51 1 (majRow_51.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_2 :
    majCellCheck 51 2 (majRow_51.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_3 :
    majCellCheck 51 3 (majRow_51.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_4 :
    majCellCheck 51 4 (majRow_51.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_5 :
    majCellCheck 51 5 (majRow_51.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_6 :
    majCellCheck 51 6 (majRow_51.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_7 :
    majCellCheck 51 7 (majRow_51.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_8 :
    majCellCheck 51 8 (majRow_51.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_9 :
    majCellCheck 51 9 (majRow_51.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_10 :
    majCellCheck 51 10 (majRow_51.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_11 :
    majCellCheck 51 11 (majRow_51.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_12 :
    majCellCheck 51 12 (majRow_51.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_13 :
    majCellCheck 51 13 (majRow_51.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_14 :
    majCellCheck 51 14 (majRow_51.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_15 :
    majCellCheck 51 15 (majRow_51.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_16 :
    majCellCheck 51 16 (majRow_51.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_17 :
    majCellCheck 51 17 (majRow_51.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_18 :
    majCellCheck 51 18 (majRow_51.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_19 :
    majCellCheck 51 19 (majRow_51.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_20 :
    majCellCheck 51 20 (majRow_51.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_21 :
    majCellCheck 51 21 (majRow_51.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_22 :
    majCellCheck 51 22 (majRow_51.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_23 :
    majCellCheck 51 23 (majRow_51.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_24 :
    majCellCheck 51 24 (majRow_51.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_25 :
    majCellCheck 51 25 (majRow_51.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_26 :
    majCellCheck 51 26 (majRow_51.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_27 :
    majCellCheck 51 27 (majRow_51.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_28 :
    majCellCheck 51 28 (majRow_51.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_29 :
    majCellCheck 51 29 (majRow_51.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_30 :
    majCellCheck 51 30 (majRow_51.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_31 :
    majCellCheck 51 31 (majRow_51.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_32 :
    majCellCheck 51 32 (majRow_51.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_33 :
    majCellCheck 51 33 (majRow_51.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_34 :
    majCellCheck 51 34 (majRow_51.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_35 :
    majCellCheck 51 35 (majRow_51.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_36 :
    majCellCheck 51 36 (majRow_51.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_37 :
    majCellCheck 51 37 (majRow_51.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_38 :
    majCellCheck 51 38 (majRow_51.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_39 :
    majCellCheck 51 39 (majRow_51.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_40 :
    majCellCheck 51 40 (majRow_51.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_41 :
    majCellCheck 51 41 (majRow_51.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_42 :
    majCellCheck 51 42 (majRow_51.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_43 :
    majCellCheck 51 43 (majRow_51.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_44 :
    majCellCheck 51 44 (majRow_51.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_45 :
    majCellCheck 51 45 (majRow_51.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_46 :
    majCellCheck 51 46 (majRow_51.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_47 :
    majCellCheck 51 47 (majRow_51.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_48 :
    majCellCheck 51 48 (majRow_51.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_49 :
    majCellCheck 51 49 (majRow_51.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_50 :
    majCellCheck 51 50 (majRow_51.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_cell_51 :
    majCellCheck 51 51 (majRow_51.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_51_all : ∀ l, l ≤ 51 →
    majCellCheck 51 l (majRow_51.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_51_cell_0, majRow_51_cell_1, majRow_51_cell_2, majRow_51_cell_3, majRow_51_cell_4, majRow_51_cell_5, majRow_51_cell_6, majRow_51_cell_7, majRow_51_cell_8, majRow_51_cell_9, majRow_51_cell_10, majRow_51_cell_11, majRow_51_cell_12, majRow_51_cell_13, majRow_51_cell_14, majRow_51_cell_15, majRow_51_cell_16, majRow_51_cell_17, majRow_51_cell_18, majRow_51_cell_19, majRow_51_cell_20, majRow_51_cell_21, majRow_51_cell_22, majRow_51_cell_23, majRow_51_cell_24, majRow_51_cell_25, majRow_51_cell_26, majRow_51_cell_27, majRow_51_cell_28, majRow_51_cell_29, majRow_51_cell_30, majRow_51_cell_31, majRow_51_cell_32, majRow_51_cell_33, majRow_51_cell_34, majRow_51_cell_35, majRow_51_cell_36, majRow_51_cell_37, majRow_51_cell_38, majRow_51_cell_39, majRow_51_cell_40, majRow_51_cell_41, majRow_51_cell_42, majRow_51_cell_43, majRow_51_cell_44, majRow_51_cell_45, majRow_51_cell_46, majRow_51_cell_47, majRow_51_cell_48, majRow_51_cell_49, majRow_51_cell_50, majRow_51_cell_51]

def majRow_52 : List (MajTree × MajTree) := [
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_52_cell_0 :
    majCellCheck 52 0 (majRow_52.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_1 :
    majCellCheck 52 1 (majRow_52.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_2 :
    majCellCheck 52 2 (majRow_52.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_3 :
    majCellCheck 52 3 (majRow_52.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_4 :
    majCellCheck 52 4 (majRow_52.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_5 :
    majCellCheck 52 5 (majRow_52.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_6 :
    majCellCheck 52 6 (majRow_52.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_7 :
    majCellCheck 52 7 (majRow_52.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_8 :
    majCellCheck 52 8 (majRow_52.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_9 :
    majCellCheck 52 9 (majRow_52.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_10 :
    majCellCheck 52 10 (majRow_52.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_11 :
    majCellCheck 52 11 (majRow_52.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_12 :
    majCellCheck 52 12 (majRow_52.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_13 :
    majCellCheck 52 13 (majRow_52.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_14 :
    majCellCheck 52 14 (majRow_52.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_15 :
    majCellCheck 52 15 (majRow_52.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_16 :
    majCellCheck 52 16 (majRow_52.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_17 :
    majCellCheck 52 17 (majRow_52.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_18 :
    majCellCheck 52 18 (majRow_52.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_19 :
    majCellCheck 52 19 (majRow_52.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_20 :
    majCellCheck 52 20 (majRow_52.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_21 :
    majCellCheck 52 21 (majRow_52.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_22 :
    majCellCheck 52 22 (majRow_52.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_23 :
    majCellCheck 52 23 (majRow_52.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_24 :
    majCellCheck 52 24 (majRow_52.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_25 :
    majCellCheck 52 25 (majRow_52.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_26 :
    majCellCheck 52 26 (majRow_52.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_27 :
    majCellCheck 52 27 (majRow_52.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_28 :
    majCellCheck 52 28 (majRow_52.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_29 :
    majCellCheck 52 29 (majRow_52.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_30 :
    majCellCheck 52 30 (majRow_52.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_31 :
    majCellCheck 52 31 (majRow_52.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_32 :
    majCellCheck 52 32 (majRow_52.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_33 :
    majCellCheck 52 33 (majRow_52.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_34 :
    majCellCheck 52 34 (majRow_52.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_35 :
    majCellCheck 52 35 (majRow_52.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_36 :
    majCellCheck 52 36 (majRow_52.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_37 :
    majCellCheck 52 37 (majRow_52.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_38 :
    majCellCheck 52 38 (majRow_52.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_39 :
    majCellCheck 52 39 (majRow_52.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_40 :
    majCellCheck 52 40 (majRow_52.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_41 :
    majCellCheck 52 41 (majRow_52.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_42 :
    majCellCheck 52 42 (majRow_52.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_43 :
    majCellCheck 52 43 (majRow_52.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_44 :
    majCellCheck 52 44 (majRow_52.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_45 :
    majCellCheck 52 45 (majRow_52.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_46 :
    majCellCheck 52 46 (majRow_52.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_47 :
    majCellCheck 52 47 (majRow_52.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_48 :
    majCellCheck 52 48 (majRow_52.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_49 :
    majCellCheck 52 49 (majRow_52.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_50 :
    majCellCheck 52 50 (majRow_52.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_51 :
    majCellCheck 52 51 (majRow_52.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_cell_52 :
    majCellCheck 52 52 (majRow_52.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_52_all : ∀ l, l ≤ 52 →
    majCellCheck 52 l (majRow_52.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_52_cell_0, majRow_52_cell_1, majRow_52_cell_2, majRow_52_cell_3, majRow_52_cell_4, majRow_52_cell_5, majRow_52_cell_6, majRow_52_cell_7, majRow_52_cell_8, majRow_52_cell_9, majRow_52_cell_10, majRow_52_cell_11, majRow_52_cell_12, majRow_52_cell_13, majRow_52_cell_14, majRow_52_cell_15, majRow_52_cell_16, majRow_52_cell_17, majRow_52_cell_18, majRow_52_cell_19, majRow_52_cell_20, majRow_52_cell_21, majRow_52_cell_22, majRow_52_cell_23, majRow_52_cell_24, majRow_52_cell_25, majRow_52_cell_26, majRow_52_cell_27, majRow_52_cell_28, majRow_52_cell_29, majRow_52_cell_30, majRow_52_cell_31, majRow_52_cell_32, majRow_52_cell_33, majRow_52_cell_34, majRow_52_cell_35, majRow_52_cell_36, majRow_52_cell_37, majRow_52_cell_38, majRow_52_cell_39, majRow_52_cell_40, majRow_52_cell_41, majRow_52_cell_42, majRow_52_cell_43, majRow_52_cell_44, majRow_52_cell_45, majRow_52_cell_46, majRow_52_cell_47, majRow_52_cell_48, majRow_52_cell_49, majRow_52_cell_50, majRow_52_cell_51, majRow_52_cell_52]

end PartialBalayage.Maximal.Square
