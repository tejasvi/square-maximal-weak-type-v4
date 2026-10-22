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

def majRow_44 : List (MajTree × MajTree) := [
  ((.leaf 45), (.leaf 46)),
  ((.leaf 46), (.leaf 47)),
  ((.leaf 47), (.leaf 48)),
  ((.leaf 48), (.leaf 49)),
  ((.leaf 49), (.leaf 50)),
  ((.leaf 50), (.leaf 51)),
  ((.leaf 51), (.leaf 52)),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_44_cell_0 :
    majCellCheck 44 0 (majRow_44.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_1 :
    majCellCheck 44 1 (majRow_44.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_2 :
    majCellCheck 44 2 (majRow_44.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_3 :
    majCellCheck 44 3 (majRow_44.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_4 :
    majCellCheck 44 4 (majRow_44.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_5 :
    majCellCheck 44 5 (majRow_44.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_6 :
    majCellCheck 44 6 (majRow_44.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_7 :
    majCellCheck 44 7 (majRow_44.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_8 :
    majCellCheck 44 8 (majRow_44.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_9 :
    majCellCheck 44 9 (majRow_44.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_10 :
    majCellCheck 44 10 (majRow_44.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_11 :
    majCellCheck 44 11 (majRow_44.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_12 :
    majCellCheck 44 12 (majRow_44.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_13 :
    majCellCheck 44 13 (majRow_44.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_14 :
    majCellCheck 44 14 (majRow_44.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_15 :
    majCellCheck 44 15 (majRow_44.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_16 :
    majCellCheck 44 16 (majRow_44.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_17 :
    majCellCheck 44 17 (majRow_44.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_18 :
    majCellCheck 44 18 (majRow_44.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_19 :
    majCellCheck 44 19 (majRow_44.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_20 :
    majCellCheck 44 20 (majRow_44.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_21 :
    majCellCheck 44 21 (majRow_44.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_22 :
    majCellCheck 44 22 (majRow_44.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_23 :
    majCellCheck 44 23 (majRow_44.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_24 :
    majCellCheck 44 24 (majRow_44.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_25 :
    majCellCheck 44 25 (majRow_44.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_26 :
    majCellCheck 44 26 (majRow_44.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_27 :
    majCellCheck 44 27 (majRow_44.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_28 :
    majCellCheck 44 28 (majRow_44.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_29 :
    majCellCheck 44 29 (majRow_44.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_30 :
    majCellCheck 44 30 (majRow_44.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_31 :
    majCellCheck 44 31 (majRow_44.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_32 :
    majCellCheck 44 32 (majRow_44.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_33 :
    majCellCheck 44 33 (majRow_44.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_34 :
    majCellCheck 44 34 (majRow_44.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_35 :
    majCellCheck 44 35 (majRow_44.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_36 :
    majCellCheck 44 36 (majRow_44.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_37 :
    majCellCheck 44 37 (majRow_44.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_38 :
    majCellCheck 44 38 (majRow_44.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_39 :
    majCellCheck 44 39 (majRow_44.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_40 :
    majCellCheck 44 40 (majRow_44.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_41 :
    majCellCheck 44 41 (majRow_44.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_42 :
    majCellCheck 44 42 (majRow_44.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_43 :
    majCellCheck 44 43 (majRow_44.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_cell_44 :
    majCellCheck 44 44 (majRow_44.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_44_all : ∀ l, l ≤ 44 →
    majCellCheck 44 l (majRow_44.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_44_cell_0, majRow_44_cell_1, majRow_44_cell_2, majRow_44_cell_3, majRow_44_cell_4, majRow_44_cell_5, majRow_44_cell_6, majRow_44_cell_7, majRow_44_cell_8, majRow_44_cell_9, majRow_44_cell_10, majRow_44_cell_11, majRow_44_cell_12, majRow_44_cell_13, majRow_44_cell_14, majRow_44_cell_15, majRow_44_cell_16, majRow_44_cell_17, majRow_44_cell_18, majRow_44_cell_19, majRow_44_cell_20, majRow_44_cell_21, majRow_44_cell_22, majRow_44_cell_23, majRow_44_cell_24, majRow_44_cell_25, majRow_44_cell_26, majRow_44_cell_27, majRow_44_cell_28, majRow_44_cell_29, majRow_44_cell_30, majRow_44_cell_31, majRow_44_cell_32, majRow_44_cell_33, majRow_44_cell_34, majRow_44_cell_35, majRow_44_cell_36, majRow_44_cell_37, majRow_44_cell_38, majRow_44_cell_39, majRow_44_cell_40, majRow_44_cell_41, majRow_44_cell_42, majRow_44_cell_43, majRow_44_cell_44]

def majRow_45 : List (MajTree × MajTree) := [
  ((.leaf 46), (.leaf 47)),
  ((.leaf 47), (.leaf 48)),
  ((.leaf 48), (.leaf 49)),
  ((.leaf 49), (.leaf 50)),
  ((.leaf 50), (.leaf 51)),
  ((.leaf 51), (.leaf 52)),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_45_cell_0 :
    majCellCheck 45 0 (majRow_45.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_1 :
    majCellCheck 45 1 (majRow_45.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_2 :
    majCellCheck 45 2 (majRow_45.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_3 :
    majCellCheck 45 3 (majRow_45.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_4 :
    majCellCheck 45 4 (majRow_45.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_5 :
    majCellCheck 45 5 (majRow_45.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_6 :
    majCellCheck 45 6 (majRow_45.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_7 :
    majCellCheck 45 7 (majRow_45.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_8 :
    majCellCheck 45 8 (majRow_45.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_9 :
    majCellCheck 45 9 (majRow_45.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_10 :
    majCellCheck 45 10 (majRow_45.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_11 :
    majCellCheck 45 11 (majRow_45.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_12 :
    majCellCheck 45 12 (majRow_45.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_13 :
    majCellCheck 45 13 (majRow_45.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_14 :
    majCellCheck 45 14 (majRow_45.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_15 :
    majCellCheck 45 15 (majRow_45.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_16 :
    majCellCheck 45 16 (majRow_45.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_17 :
    majCellCheck 45 17 (majRow_45.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_18 :
    majCellCheck 45 18 (majRow_45.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_19 :
    majCellCheck 45 19 (majRow_45.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_20 :
    majCellCheck 45 20 (majRow_45.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_21 :
    majCellCheck 45 21 (majRow_45.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_22 :
    majCellCheck 45 22 (majRow_45.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_23 :
    majCellCheck 45 23 (majRow_45.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_24 :
    majCellCheck 45 24 (majRow_45.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_25 :
    majCellCheck 45 25 (majRow_45.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_26 :
    majCellCheck 45 26 (majRow_45.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_27 :
    majCellCheck 45 27 (majRow_45.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_28 :
    majCellCheck 45 28 (majRow_45.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_29 :
    majCellCheck 45 29 (majRow_45.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_30 :
    majCellCheck 45 30 (majRow_45.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_31 :
    majCellCheck 45 31 (majRow_45.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_32 :
    majCellCheck 45 32 (majRow_45.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_33 :
    majCellCheck 45 33 (majRow_45.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_34 :
    majCellCheck 45 34 (majRow_45.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_35 :
    majCellCheck 45 35 (majRow_45.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_36 :
    majCellCheck 45 36 (majRow_45.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_37 :
    majCellCheck 45 37 (majRow_45.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_38 :
    majCellCheck 45 38 (majRow_45.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_39 :
    majCellCheck 45 39 (majRow_45.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_40 :
    majCellCheck 45 40 (majRow_45.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_41 :
    majCellCheck 45 41 (majRow_45.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_42 :
    majCellCheck 45 42 (majRow_45.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_43 :
    majCellCheck 45 43 (majRow_45.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_44 :
    majCellCheck 45 44 (majRow_45.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_cell_45 :
    majCellCheck 45 45 (majRow_45.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_45_all : ∀ l, l ≤ 45 →
    majCellCheck 45 l (majRow_45.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_45_cell_0, majRow_45_cell_1, majRow_45_cell_2, majRow_45_cell_3, majRow_45_cell_4, majRow_45_cell_5, majRow_45_cell_6, majRow_45_cell_7, majRow_45_cell_8, majRow_45_cell_9, majRow_45_cell_10, majRow_45_cell_11, majRow_45_cell_12, majRow_45_cell_13, majRow_45_cell_14, majRow_45_cell_15, majRow_45_cell_16, majRow_45_cell_17, majRow_45_cell_18, majRow_45_cell_19, majRow_45_cell_20, majRow_45_cell_21, majRow_45_cell_22, majRow_45_cell_23, majRow_45_cell_24, majRow_45_cell_25, majRow_45_cell_26, majRow_45_cell_27, majRow_45_cell_28, majRow_45_cell_29, majRow_45_cell_30, majRow_45_cell_31, majRow_45_cell_32, majRow_45_cell_33, majRow_45_cell_34, majRow_45_cell_35, majRow_45_cell_36, majRow_45_cell_37, majRow_45_cell_38, majRow_45_cell_39, majRow_45_cell_40, majRow_45_cell_41, majRow_45_cell_42, majRow_45_cell_43, majRow_45_cell_44, majRow_45_cell_45]

def majRow_46 : List (MajTree × MajTree) := [
  ((.leaf 47), (.leaf 48)),
  ((.leaf 48), (.leaf 49)),
  ((.leaf 49), (.leaf 50)),
  ((.leaf 50), (.leaf 51)),
  ((.leaf 51), (.leaf 52)),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_46_cell_0 :
    majCellCheck 46 0 (majRow_46.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_1 :
    majCellCheck 46 1 (majRow_46.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_2 :
    majCellCheck 46 2 (majRow_46.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_3 :
    majCellCheck 46 3 (majRow_46.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_4 :
    majCellCheck 46 4 (majRow_46.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_5 :
    majCellCheck 46 5 (majRow_46.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_6 :
    majCellCheck 46 6 (majRow_46.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_7 :
    majCellCheck 46 7 (majRow_46.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_8 :
    majCellCheck 46 8 (majRow_46.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_9 :
    majCellCheck 46 9 (majRow_46.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_10 :
    majCellCheck 46 10 (majRow_46.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_11 :
    majCellCheck 46 11 (majRow_46.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_12 :
    majCellCheck 46 12 (majRow_46.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_13 :
    majCellCheck 46 13 (majRow_46.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_14 :
    majCellCheck 46 14 (majRow_46.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_15 :
    majCellCheck 46 15 (majRow_46.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_16 :
    majCellCheck 46 16 (majRow_46.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_17 :
    majCellCheck 46 17 (majRow_46.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_18 :
    majCellCheck 46 18 (majRow_46.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_19 :
    majCellCheck 46 19 (majRow_46.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_20 :
    majCellCheck 46 20 (majRow_46.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_21 :
    majCellCheck 46 21 (majRow_46.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_22 :
    majCellCheck 46 22 (majRow_46.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_23 :
    majCellCheck 46 23 (majRow_46.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_24 :
    majCellCheck 46 24 (majRow_46.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_25 :
    majCellCheck 46 25 (majRow_46.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_26 :
    majCellCheck 46 26 (majRow_46.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_27 :
    majCellCheck 46 27 (majRow_46.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_28 :
    majCellCheck 46 28 (majRow_46.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_29 :
    majCellCheck 46 29 (majRow_46.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_30 :
    majCellCheck 46 30 (majRow_46.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_31 :
    majCellCheck 46 31 (majRow_46.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_32 :
    majCellCheck 46 32 (majRow_46.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_33 :
    majCellCheck 46 33 (majRow_46.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_34 :
    majCellCheck 46 34 (majRow_46.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_35 :
    majCellCheck 46 35 (majRow_46.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_36 :
    majCellCheck 46 36 (majRow_46.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_37 :
    majCellCheck 46 37 (majRow_46.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_38 :
    majCellCheck 46 38 (majRow_46.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_39 :
    majCellCheck 46 39 (majRow_46.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_40 :
    majCellCheck 46 40 (majRow_46.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_41 :
    majCellCheck 46 41 (majRow_46.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_42 :
    majCellCheck 46 42 (majRow_46.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_43 :
    majCellCheck 46 43 (majRow_46.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_44 :
    majCellCheck 46 44 (majRow_46.getD 44 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_45 :
    majCellCheck 46 45 (majRow_46.getD 45 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_cell_46 :
    majCellCheck 46 46 (majRow_46.getD 46 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_46_all : ∀ l, l ≤ 46 →
    majCellCheck 46 l (majRow_46.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_46_cell_0, majRow_46_cell_1, majRow_46_cell_2, majRow_46_cell_3, majRow_46_cell_4, majRow_46_cell_5, majRow_46_cell_6, majRow_46_cell_7, majRow_46_cell_8, majRow_46_cell_9, majRow_46_cell_10, majRow_46_cell_11, majRow_46_cell_12, majRow_46_cell_13, majRow_46_cell_14, majRow_46_cell_15, majRow_46_cell_16, majRow_46_cell_17, majRow_46_cell_18, majRow_46_cell_19, majRow_46_cell_20, majRow_46_cell_21, majRow_46_cell_22, majRow_46_cell_23, majRow_46_cell_24, majRow_46_cell_25, majRow_46_cell_26, majRow_46_cell_27, majRow_46_cell_28, majRow_46_cell_29, majRow_46_cell_30, majRow_46_cell_31, majRow_46_cell_32, majRow_46_cell_33, majRow_46_cell_34, majRow_46_cell_35, majRow_46_cell_36, majRow_46_cell_37, majRow_46_cell_38, majRow_46_cell_39, majRow_46_cell_40, majRow_46_cell_41, majRow_46_cell_42, majRow_46_cell_43, majRow_46_cell_44, majRow_46_cell_45, majRow_46_cell_46]

end PartialBalayage.Maximal.Square
