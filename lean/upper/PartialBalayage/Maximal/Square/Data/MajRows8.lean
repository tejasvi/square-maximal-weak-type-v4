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

def majRow_47 : List (MajTree × MajTree) := [
  ((.leaf 48), (.leaf 49)),
  ((.leaf 49), (.leaf 50)),
  ((.leaf 50), (.leaf 51)),
  ((.leaf 51), (.leaf 52)),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_47_cell_0 :
    majCellCheck 47 0 (majRow_47.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_1 :
    majCellCheck 47 1 (majRow_47.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_2 :
    majCellCheck 47 2 (majRow_47.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_3 :
    majCellCheck 47 3 (majRow_47.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_4 :
    majCellCheck 47 4 (majRow_47.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_5 :
    majCellCheck 47 5 (majRow_47.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_6 :
    majCellCheck 47 6 (majRow_47.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_7 :
    majCellCheck 47 7 (majRow_47.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_8 :
    majCellCheck 47 8 (majRow_47.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_9 :
    majCellCheck 47 9 (majRow_47.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_10 :
    majCellCheck 47 10 (majRow_47.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_11 :
    majCellCheck 47 11 (majRow_47.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_12 :
    majCellCheck 47 12 (majRow_47.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_13 :
    majCellCheck 47 13 (majRow_47.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_14 :
    majCellCheck 47 14 (majRow_47.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_15 :
    majCellCheck 47 15 (majRow_47.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_16 :
    majCellCheck 47 16 (majRow_47.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_17 :
    majCellCheck 47 17 (majRow_47.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_18 :
    majCellCheck 47 18 (majRow_47.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_19 :
    majCellCheck 47 19 (majRow_47.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_20 :
    majCellCheck 47 20 (majRow_47.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_21 :
    majCellCheck 47 21 (majRow_47.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_22 :
    majCellCheck 47 22 (majRow_47.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_23 :
    majCellCheck 47 23 (majRow_47.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_24 :
    majCellCheck 47 24 (majRow_47.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_25 :
    majCellCheck 47 25 (majRow_47.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_26 :
    majCellCheck 47 26 (majRow_47.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_27 :
    majCellCheck 47 27 (majRow_47.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_28 :
    majCellCheck 47 28 (majRow_47.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_29 :
    majCellCheck 47 29 (majRow_47.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_30 :
    majCellCheck 47 30 (majRow_47.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_31 :
    majCellCheck 47 31 (majRow_47.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_32 :
    majCellCheck 47 32 (majRow_47.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_33 :
    majCellCheck 47 33 (majRow_47.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_34 :
    majCellCheck 47 34 (majRow_47.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_35 :
    majCellCheck 47 35 (majRow_47.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_36 :
    majCellCheck 47 36 (majRow_47.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_37 :
    majCellCheck 47 37 (majRow_47.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_38 :
    majCellCheck 47 38 (majRow_47.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_39 :
    majCellCheck 47 39 (majRow_47.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_40 :
    majCellCheck 47 40 (majRow_47.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_41 :
    majCellCheck 47 41 (majRow_47.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_42 :
    majCellCheck 47 42 (majRow_47.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_43 :
    majCellCheck 47 43 (majRow_47.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_44 :
    majCellCheck 47 44 (majRow_47.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_45 :
    majCellCheck 47 45 (majRow_47.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_46 :
    majCellCheck 47 46 (majRow_47.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_cell_47 :
    majCellCheck 47 47 (majRow_47.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_47_all : ∀ l, l ≤ 47 →
    majCellCheck 47 l (majRow_47.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_47_cell_0, majRow_47_cell_1, majRow_47_cell_2, majRow_47_cell_3, majRow_47_cell_4, majRow_47_cell_5, majRow_47_cell_6, majRow_47_cell_7, majRow_47_cell_8, majRow_47_cell_9, majRow_47_cell_10, majRow_47_cell_11, majRow_47_cell_12, majRow_47_cell_13, majRow_47_cell_14, majRow_47_cell_15, majRow_47_cell_16, majRow_47_cell_17, majRow_47_cell_18, majRow_47_cell_19, majRow_47_cell_20, majRow_47_cell_21, majRow_47_cell_22, majRow_47_cell_23, majRow_47_cell_24, majRow_47_cell_25, majRow_47_cell_26, majRow_47_cell_27, majRow_47_cell_28, majRow_47_cell_29, majRow_47_cell_30, majRow_47_cell_31, majRow_47_cell_32, majRow_47_cell_33, majRow_47_cell_34, majRow_47_cell_35, majRow_47_cell_36, majRow_47_cell_37, majRow_47_cell_38, majRow_47_cell_39, majRow_47_cell_40, majRow_47_cell_41, majRow_47_cell_42, majRow_47_cell_43, majRow_47_cell_44, majRow_47_cell_45, majRow_47_cell_46, majRow_47_cell_47]

def majRow_48 : List (MajTree × MajTree) := [
  ((.leaf 49), (.leaf 50)),
  ((.leaf 50), (.leaf 51)),
  ((.leaf 51), (.leaf 52)),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_48_cell_0 :
    majCellCheck 48 0 (majRow_48.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_1 :
    majCellCheck 48 1 (majRow_48.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_2 :
    majCellCheck 48 2 (majRow_48.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_3 :
    majCellCheck 48 3 (majRow_48.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_4 :
    majCellCheck 48 4 (majRow_48.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_5 :
    majCellCheck 48 5 (majRow_48.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_6 :
    majCellCheck 48 6 (majRow_48.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_7 :
    majCellCheck 48 7 (majRow_48.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_8 :
    majCellCheck 48 8 (majRow_48.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_9 :
    majCellCheck 48 9 (majRow_48.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_10 :
    majCellCheck 48 10 (majRow_48.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_11 :
    majCellCheck 48 11 (majRow_48.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_12 :
    majCellCheck 48 12 (majRow_48.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_13 :
    majCellCheck 48 13 (majRow_48.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_14 :
    majCellCheck 48 14 (majRow_48.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_15 :
    majCellCheck 48 15 (majRow_48.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_16 :
    majCellCheck 48 16 (majRow_48.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_17 :
    majCellCheck 48 17 (majRow_48.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_18 :
    majCellCheck 48 18 (majRow_48.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_19 :
    majCellCheck 48 19 (majRow_48.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_20 :
    majCellCheck 48 20 (majRow_48.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_21 :
    majCellCheck 48 21 (majRow_48.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_22 :
    majCellCheck 48 22 (majRow_48.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_23 :
    majCellCheck 48 23 (majRow_48.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_24 :
    majCellCheck 48 24 (majRow_48.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_25 :
    majCellCheck 48 25 (majRow_48.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_26 :
    majCellCheck 48 26 (majRow_48.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_27 :
    majCellCheck 48 27 (majRow_48.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_28 :
    majCellCheck 48 28 (majRow_48.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_29 :
    majCellCheck 48 29 (majRow_48.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_30 :
    majCellCheck 48 30 (majRow_48.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_31 :
    majCellCheck 48 31 (majRow_48.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_32 :
    majCellCheck 48 32 (majRow_48.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_33 :
    majCellCheck 48 33 (majRow_48.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_34 :
    majCellCheck 48 34 (majRow_48.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_35 :
    majCellCheck 48 35 (majRow_48.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_36 :
    majCellCheck 48 36 (majRow_48.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_37 :
    majCellCheck 48 37 (majRow_48.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_38 :
    majCellCheck 48 38 (majRow_48.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_39 :
    majCellCheck 48 39 (majRow_48.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_40 :
    majCellCheck 48 40 (majRow_48.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_41 :
    majCellCheck 48 41 (majRow_48.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_42 :
    majCellCheck 48 42 (majRow_48.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_43 :
    majCellCheck 48 43 (majRow_48.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_44 :
    majCellCheck 48 44 (majRow_48.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_45 :
    majCellCheck 48 45 (majRow_48.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_46 :
    majCellCheck 48 46 (majRow_48.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_47 :
    majCellCheck 48 47 (majRow_48.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_cell_48 :
    majCellCheck 48 48 (majRow_48.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_48_all : ∀ l, l ≤ 48 →
    majCellCheck 48 l (majRow_48.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_48_cell_0, majRow_48_cell_1, majRow_48_cell_2, majRow_48_cell_3, majRow_48_cell_4, majRow_48_cell_5, majRow_48_cell_6, majRow_48_cell_7, majRow_48_cell_8, majRow_48_cell_9, majRow_48_cell_10, majRow_48_cell_11, majRow_48_cell_12, majRow_48_cell_13, majRow_48_cell_14, majRow_48_cell_15, majRow_48_cell_16, majRow_48_cell_17, majRow_48_cell_18, majRow_48_cell_19, majRow_48_cell_20, majRow_48_cell_21, majRow_48_cell_22, majRow_48_cell_23, majRow_48_cell_24, majRow_48_cell_25, majRow_48_cell_26, majRow_48_cell_27, majRow_48_cell_28, majRow_48_cell_29, majRow_48_cell_30, majRow_48_cell_31, majRow_48_cell_32, majRow_48_cell_33, majRow_48_cell_34, majRow_48_cell_35, majRow_48_cell_36, majRow_48_cell_37, majRow_48_cell_38, majRow_48_cell_39, majRow_48_cell_40, majRow_48_cell_41, majRow_48_cell_42, majRow_48_cell_43, majRow_48_cell_44, majRow_48_cell_45, majRow_48_cell_46, majRow_48_cell_47, majRow_48_cell_48]

def majRow_49 : List (MajTree × MajTree) := [
  ((.leaf 50), (.node (.leaf 51) (.leaf 51) (.leaf 51) (.leaf 51))),
  ((.node (.leaf 51) (.leaf 51) (.leaf 51) (.leaf 51)), (.node (.leaf 52) (.leaf 151) (.leaf 151) (.leaf 151))),
  ((.node (.leaf 151) (.leaf 52) (.leaf 52) (.leaf 52)), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_49_cell_0 :
    majCellCheck 49 0 (majRow_49.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_1 :
    majCellCheck 49 1 (majRow_49.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_2 :
    majCellCheck 49 2 (majRow_49.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_3 :
    majCellCheck 49 3 (majRow_49.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_4 :
    majCellCheck 49 4 (majRow_49.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_5 :
    majCellCheck 49 5 (majRow_49.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_6 :
    majCellCheck 49 6 (majRow_49.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_7 :
    majCellCheck 49 7 (majRow_49.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_8 :
    majCellCheck 49 8 (majRow_49.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_9 :
    majCellCheck 49 9 (majRow_49.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_10 :
    majCellCheck 49 10 (majRow_49.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_11 :
    majCellCheck 49 11 (majRow_49.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_12 :
    majCellCheck 49 12 (majRow_49.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_13 :
    majCellCheck 49 13 (majRow_49.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_14 :
    majCellCheck 49 14 (majRow_49.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_15 :
    majCellCheck 49 15 (majRow_49.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_16 :
    majCellCheck 49 16 (majRow_49.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_17 :
    majCellCheck 49 17 (majRow_49.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_18 :
    majCellCheck 49 18 (majRow_49.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_19 :
    majCellCheck 49 19 (majRow_49.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_20 :
    majCellCheck 49 20 (majRow_49.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_21 :
    majCellCheck 49 21 (majRow_49.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_22 :
    majCellCheck 49 22 (majRow_49.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_23 :
    majCellCheck 49 23 (majRow_49.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_24 :
    majCellCheck 49 24 (majRow_49.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_25 :
    majCellCheck 49 25 (majRow_49.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_26 :
    majCellCheck 49 26 (majRow_49.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_27 :
    majCellCheck 49 27 (majRow_49.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_28 :
    majCellCheck 49 28 (majRow_49.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_29 :
    majCellCheck 49 29 (majRow_49.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_30 :
    majCellCheck 49 30 (majRow_49.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_31 :
    majCellCheck 49 31 (majRow_49.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_32 :
    majCellCheck 49 32 (majRow_49.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_33 :
    majCellCheck 49 33 (majRow_49.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_34 :
    majCellCheck 49 34 (majRow_49.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_35 :
    majCellCheck 49 35 (majRow_49.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_36 :
    majCellCheck 49 36 (majRow_49.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_37 :
    majCellCheck 49 37 (majRow_49.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_38 :
    majCellCheck 49 38 (majRow_49.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_39 :
    majCellCheck 49 39 (majRow_49.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_40 :
    majCellCheck 49 40 (majRow_49.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_41 :
    majCellCheck 49 41 (majRow_49.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_42 :
    majCellCheck 49 42 (majRow_49.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_43 :
    majCellCheck 49 43 (majRow_49.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_44 :
    majCellCheck 49 44 (majRow_49.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_45 :
    majCellCheck 49 45 (majRow_49.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_46 :
    majCellCheck 49 46 (majRow_49.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_47 :
    majCellCheck 49 47 (majRow_49.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_48 :
    majCellCheck 49 48 (majRow_49.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_cell_49 :
    majCellCheck 49 49 (majRow_49.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_49_all : ∀ l, l ≤ 49 →
    majCellCheck 49 l (majRow_49.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_49_cell_0, majRow_49_cell_1, majRow_49_cell_2, majRow_49_cell_3, majRow_49_cell_4, majRow_49_cell_5, majRow_49_cell_6, majRow_49_cell_7, majRow_49_cell_8, majRow_49_cell_9, majRow_49_cell_10, majRow_49_cell_11, majRow_49_cell_12, majRow_49_cell_13, majRow_49_cell_14, majRow_49_cell_15, majRow_49_cell_16, majRow_49_cell_17, majRow_49_cell_18, majRow_49_cell_19, majRow_49_cell_20, majRow_49_cell_21, majRow_49_cell_22, majRow_49_cell_23, majRow_49_cell_24, majRow_49_cell_25, majRow_49_cell_26, majRow_49_cell_27, majRow_49_cell_28, majRow_49_cell_29, majRow_49_cell_30, majRow_49_cell_31, majRow_49_cell_32, majRow_49_cell_33, majRow_49_cell_34, majRow_49_cell_35, majRow_49_cell_36, majRow_49_cell_37, majRow_49_cell_38, majRow_49_cell_39, majRow_49_cell_40, majRow_49_cell_41, majRow_49_cell_42, majRow_49_cell_43, majRow_49_cell_44, majRow_49_cell_45, majRow_49_cell_46, majRow_49_cell_47, majRow_49_cell_48, majRow_49_cell_49]

end PartialBalayage.Maximal.Square
