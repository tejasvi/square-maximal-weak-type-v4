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

def majRow_53 : List (MajTree × MajTree) := [
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_53_cell_0 :
    majCellCheck 53 0 (majRow_53.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_1 :
    majCellCheck 53 1 (majRow_53.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_2 :
    majCellCheck 53 2 (majRow_53.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_3 :
    majCellCheck 53 3 (majRow_53.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_4 :
    majCellCheck 53 4 (majRow_53.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_5 :
    majCellCheck 53 5 (majRow_53.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_6 :
    majCellCheck 53 6 (majRow_53.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_7 :
    majCellCheck 53 7 (majRow_53.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_8 :
    majCellCheck 53 8 (majRow_53.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_9 :
    majCellCheck 53 9 (majRow_53.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_10 :
    majCellCheck 53 10 (majRow_53.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_11 :
    majCellCheck 53 11 (majRow_53.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_12 :
    majCellCheck 53 12 (majRow_53.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_13 :
    majCellCheck 53 13 (majRow_53.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_14 :
    majCellCheck 53 14 (majRow_53.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_15 :
    majCellCheck 53 15 (majRow_53.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_16 :
    majCellCheck 53 16 (majRow_53.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_17 :
    majCellCheck 53 17 (majRow_53.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_18 :
    majCellCheck 53 18 (majRow_53.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_19 :
    majCellCheck 53 19 (majRow_53.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_20 :
    majCellCheck 53 20 (majRow_53.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_21 :
    majCellCheck 53 21 (majRow_53.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_22 :
    majCellCheck 53 22 (majRow_53.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_23 :
    majCellCheck 53 23 (majRow_53.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_24 :
    majCellCheck 53 24 (majRow_53.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_25 :
    majCellCheck 53 25 (majRow_53.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_26 :
    majCellCheck 53 26 (majRow_53.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_27 :
    majCellCheck 53 27 (majRow_53.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_28 :
    majCellCheck 53 28 (majRow_53.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_29 :
    majCellCheck 53 29 (majRow_53.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_30 :
    majCellCheck 53 30 (majRow_53.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_31 :
    majCellCheck 53 31 (majRow_53.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_32 :
    majCellCheck 53 32 (majRow_53.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_33 :
    majCellCheck 53 33 (majRow_53.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_34 :
    majCellCheck 53 34 (majRow_53.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_35 :
    majCellCheck 53 35 (majRow_53.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_36 :
    majCellCheck 53 36 (majRow_53.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_37 :
    majCellCheck 53 37 (majRow_53.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_38 :
    majCellCheck 53 38 (majRow_53.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_39 :
    majCellCheck 53 39 (majRow_53.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_40 :
    majCellCheck 53 40 (majRow_53.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_41 :
    majCellCheck 53 41 (majRow_53.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_42 :
    majCellCheck 53 42 (majRow_53.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_43 :
    majCellCheck 53 43 (majRow_53.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_44 :
    majCellCheck 53 44 (majRow_53.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_45 :
    majCellCheck 53 45 (majRow_53.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_46 :
    majCellCheck 53 46 (majRow_53.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_47 :
    majCellCheck 53 47 (majRow_53.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_48 :
    majCellCheck 53 48 (majRow_53.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_49 :
    majCellCheck 53 49 (majRow_53.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_50 :
    majCellCheck 53 50 (majRow_53.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_51 :
    majCellCheck 53 51 (majRow_53.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_52 :
    majCellCheck 53 52 (majRow_53.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_cell_53 :
    majCellCheck 53 53 (majRow_53.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_53_all : ∀ l, l ≤ 53 →
    majCellCheck 53 l (majRow_53.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_53_cell_0, majRow_53_cell_1, majRow_53_cell_2, majRow_53_cell_3, majRow_53_cell_4, majRow_53_cell_5, majRow_53_cell_6, majRow_53_cell_7, majRow_53_cell_8, majRow_53_cell_9, majRow_53_cell_10, majRow_53_cell_11, majRow_53_cell_12, majRow_53_cell_13, majRow_53_cell_14, majRow_53_cell_15, majRow_53_cell_16, majRow_53_cell_17, majRow_53_cell_18, majRow_53_cell_19, majRow_53_cell_20, majRow_53_cell_21, majRow_53_cell_22, majRow_53_cell_23, majRow_53_cell_24, majRow_53_cell_25, majRow_53_cell_26, majRow_53_cell_27, majRow_53_cell_28, majRow_53_cell_29, majRow_53_cell_30, majRow_53_cell_31, majRow_53_cell_32, majRow_53_cell_33, majRow_53_cell_34, majRow_53_cell_35, majRow_53_cell_36, majRow_53_cell_37, majRow_53_cell_38, majRow_53_cell_39, majRow_53_cell_40, majRow_53_cell_41, majRow_53_cell_42, majRow_53_cell_43, majRow_53_cell_44, majRow_53_cell_45, majRow_53_cell_46, majRow_53_cell_47, majRow_53_cell_48, majRow_53_cell_49, majRow_53_cell_50, majRow_53_cell_51, majRow_53_cell_52, majRow_53_cell_53]

def majRow_54 : List (MajTree × MajTree) := [
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_54_cell_0 :
    majCellCheck 54 0 (majRow_54.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_1 :
    majCellCheck 54 1 (majRow_54.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_2 :
    majCellCheck 54 2 (majRow_54.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_3 :
    majCellCheck 54 3 (majRow_54.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_4 :
    majCellCheck 54 4 (majRow_54.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_5 :
    majCellCheck 54 5 (majRow_54.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_6 :
    majCellCheck 54 6 (majRow_54.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_7 :
    majCellCheck 54 7 (majRow_54.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_8 :
    majCellCheck 54 8 (majRow_54.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_9 :
    majCellCheck 54 9 (majRow_54.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_10 :
    majCellCheck 54 10 (majRow_54.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_11 :
    majCellCheck 54 11 (majRow_54.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_12 :
    majCellCheck 54 12 (majRow_54.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_13 :
    majCellCheck 54 13 (majRow_54.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_14 :
    majCellCheck 54 14 (majRow_54.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_15 :
    majCellCheck 54 15 (majRow_54.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_16 :
    majCellCheck 54 16 (majRow_54.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_17 :
    majCellCheck 54 17 (majRow_54.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_18 :
    majCellCheck 54 18 (majRow_54.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_19 :
    majCellCheck 54 19 (majRow_54.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_20 :
    majCellCheck 54 20 (majRow_54.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_21 :
    majCellCheck 54 21 (majRow_54.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_22 :
    majCellCheck 54 22 (majRow_54.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_23 :
    majCellCheck 54 23 (majRow_54.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_24 :
    majCellCheck 54 24 (majRow_54.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_25 :
    majCellCheck 54 25 (majRow_54.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_26 :
    majCellCheck 54 26 (majRow_54.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_27 :
    majCellCheck 54 27 (majRow_54.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_28 :
    majCellCheck 54 28 (majRow_54.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_29 :
    majCellCheck 54 29 (majRow_54.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_30 :
    majCellCheck 54 30 (majRow_54.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_31 :
    majCellCheck 54 31 (majRow_54.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_32 :
    majCellCheck 54 32 (majRow_54.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_33 :
    majCellCheck 54 33 (majRow_54.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_34 :
    majCellCheck 54 34 (majRow_54.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_35 :
    majCellCheck 54 35 (majRow_54.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_36 :
    majCellCheck 54 36 (majRow_54.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_37 :
    majCellCheck 54 37 (majRow_54.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_38 :
    majCellCheck 54 38 (majRow_54.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_39 :
    majCellCheck 54 39 (majRow_54.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_40 :
    majCellCheck 54 40 (majRow_54.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_41 :
    majCellCheck 54 41 (majRow_54.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_42 :
    majCellCheck 54 42 (majRow_54.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_43 :
    majCellCheck 54 43 (majRow_54.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_44 :
    majCellCheck 54 44 (majRow_54.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_45 :
    majCellCheck 54 45 (majRow_54.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_46 :
    majCellCheck 54 46 (majRow_54.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_47 :
    majCellCheck 54 47 (majRow_54.getD 47 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_48 :
    majCellCheck 54 48 (majRow_54.getD 48 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_49 :
    majCellCheck 54 49 (majRow_54.getD 49 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_50 :
    majCellCheck 54 50 (majRow_54.getD 50 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_51 :
    majCellCheck 54 51 (majRow_54.getD 51 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_52 :
    majCellCheck 54 52 (majRow_54.getD 52 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_53 :
    majCellCheck 54 53 (majRow_54.getD 53 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_cell_54 :
    majCellCheck 54 54 (majRow_54.getD 54 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_54_all : ∀ l, l ≤ 54 →
    majCellCheck 54 l (majRow_54.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_54_cell_0, majRow_54_cell_1, majRow_54_cell_2, majRow_54_cell_3, majRow_54_cell_4, majRow_54_cell_5, majRow_54_cell_6, majRow_54_cell_7, majRow_54_cell_8, majRow_54_cell_9, majRow_54_cell_10, majRow_54_cell_11, majRow_54_cell_12, majRow_54_cell_13, majRow_54_cell_14, majRow_54_cell_15, majRow_54_cell_16, majRow_54_cell_17, majRow_54_cell_18, majRow_54_cell_19, majRow_54_cell_20, majRow_54_cell_21, majRow_54_cell_22, majRow_54_cell_23, majRow_54_cell_24, majRow_54_cell_25, majRow_54_cell_26, majRow_54_cell_27, majRow_54_cell_28, majRow_54_cell_29, majRow_54_cell_30, majRow_54_cell_31, majRow_54_cell_32, majRow_54_cell_33, majRow_54_cell_34, majRow_54_cell_35, majRow_54_cell_36, majRow_54_cell_37, majRow_54_cell_38, majRow_54_cell_39, majRow_54_cell_40, majRow_54_cell_41, majRow_54_cell_42, majRow_54_cell_43, majRow_54_cell_44, majRow_54_cell_45, majRow_54_cell_46, majRow_54_cell_47, majRow_54_cell_48, majRow_54_cell_49, majRow_54_cell_50, majRow_54_cell_51, majRow_54_cell_52, majRow_54_cell_53, majRow_54_cell_54]

end PartialBalayage.Maximal.Square
