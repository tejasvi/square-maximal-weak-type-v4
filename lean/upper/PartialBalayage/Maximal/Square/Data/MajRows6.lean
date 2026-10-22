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

def majRow_41 : List (MajTree × MajTree) := [
  ((.leaf 42), (.leaf 43)),
  ((.leaf 43), (.leaf 44)),
  ((.leaf 44), (.leaf 45)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_41_cell_0 :
    majCellCheck 41 0 (majRow_41.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_1 :
    majCellCheck 41 1 (majRow_41.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_2 :
    majCellCheck 41 2 (majRow_41.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_3 :
    majCellCheck 41 3 (majRow_41.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_4 :
    majCellCheck 41 4 (majRow_41.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_5 :
    majCellCheck 41 5 (majRow_41.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_6 :
    majCellCheck 41 6 (majRow_41.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_7 :
    majCellCheck 41 7 (majRow_41.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_8 :
    majCellCheck 41 8 (majRow_41.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_9 :
    majCellCheck 41 9 (majRow_41.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_10 :
    majCellCheck 41 10 (majRow_41.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_11 :
    majCellCheck 41 11 (majRow_41.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_12 :
    majCellCheck 41 12 (majRow_41.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_13 :
    majCellCheck 41 13 (majRow_41.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_14 :
    majCellCheck 41 14 (majRow_41.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_15 :
    majCellCheck 41 15 (majRow_41.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_16 :
    majCellCheck 41 16 (majRow_41.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_17 :
    majCellCheck 41 17 (majRow_41.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_18 :
    majCellCheck 41 18 (majRow_41.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_19 :
    majCellCheck 41 19 (majRow_41.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_20 :
    majCellCheck 41 20 (majRow_41.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_21 :
    majCellCheck 41 21 (majRow_41.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_22 :
    majCellCheck 41 22 (majRow_41.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_23 :
    majCellCheck 41 23 (majRow_41.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_24 :
    majCellCheck 41 24 (majRow_41.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_25 :
    majCellCheck 41 25 (majRow_41.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_26 :
    majCellCheck 41 26 (majRow_41.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_27 :
    majCellCheck 41 27 (majRow_41.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_28 :
    majCellCheck 41 28 (majRow_41.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_29 :
    majCellCheck 41 29 (majRow_41.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_30 :
    majCellCheck 41 30 (majRow_41.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_31 :
    majCellCheck 41 31 (majRow_41.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_32 :
    majCellCheck 41 32 (majRow_41.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_33 :
    majCellCheck 41 33 (majRow_41.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_34 :
    majCellCheck 41 34 (majRow_41.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_35 :
    majCellCheck 41 35 (majRow_41.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_36 :
    majCellCheck 41 36 (majRow_41.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_37 :
    majCellCheck 41 37 (majRow_41.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_38 :
    majCellCheck 41 38 (majRow_41.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_39 :
    majCellCheck 41 39 (majRow_41.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_40 :
    majCellCheck 41 40 (majRow_41.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_cell_41 :
    majCellCheck 41 41 (majRow_41.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_41_all : ∀ l, l ≤ 41 →
    majCellCheck 41 l (majRow_41.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_41_cell_0, majRow_41_cell_1, majRow_41_cell_2, majRow_41_cell_3, majRow_41_cell_4, majRow_41_cell_5, majRow_41_cell_6, majRow_41_cell_7, majRow_41_cell_8, majRow_41_cell_9, majRow_41_cell_10, majRow_41_cell_11, majRow_41_cell_12, majRow_41_cell_13, majRow_41_cell_14, majRow_41_cell_15, majRow_41_cell_16, majRow_41_cell_17, majRow_41_cell_18, majRow_41_cell_19, majRow_41_cell_20, majRow_41_cell_21, majRow_41_cell_22, majRow_41_cell_23, majRow_41_cell_24, majRow_41_cell_25, majRow_41_cell_26, majRow_41_cell_27, majRow_41_cell_28, majRow_41_cell_29, majRow_41_cell_30, majRow_41_cell_31, majRow_41_cell_32, majRow_41_cell_33, majRow_41_cell_34, majRow_41_cell_35, majRow_41_cell_36, majRow_41_cell_37, majRow_41_cell_38, majRow_41_cell_39, majRow_41_cell_40, majRow_41_cell_41]

def majRow_42 : List (MajTree × MajTree) := [
  ((.leaf 43), (.leaf 44)),
  ((.leaf 44), (.leaf 45)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_42_cell_0 :
    majCellCheck 42 0 (majRow_42.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_1 :
    majCellCheck 42 1 (majRow_42.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_2 :
    majCellCheck 42 2 (majRow_42.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_3 :
    majCellCheck 42 3 (majRow_42.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_4 :
    majCellCheck 42 4 (majRow_42.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_5 :
    majCellCheck 42 5 (majRow_42.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_6 :
    majCellCheck 42 6 (majRow_42.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_7 :
    majCellCheck 42 7 (majRow_42.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_8 :
    majCellCheck 42 8 (majRow_42.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_9 :
    majCellCheck 42 9 (majRow_42.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_10 :
    majCellCheck 42 10 (majRow_42.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_11 :
    majCellCheck 42 11 (majRow_42.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_12 :
    majCellCheck 42 12 (majRow_42.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_13 :
    majCellCheck 42 13 (majRow_42.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_14 :
    majCellCheck 42 14 (majRow_42.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_15 :
    majCellCheck 42 15 (majRow_42.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_16 :
    majCellCheck 42 16 (majRow_42.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_17 :
    majCellCheck 42 17 (majRow_42.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_18 :
    majCellCheck 42 18 (majRow_42.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_19 :
    majCellCheck 42 19 (majRow_42.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_20 :
    majCellCheck 42 20 (majRow_42.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_21 :
    majCellCheck 42 21 (majRow_42.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_22 :
    majCellCheck 42 22 (majRow_42.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_23 :
    majCellCheck 42 23 (majRow_42.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_24 :
    majCellCheck 42 24 (majRow_42.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_25 :
    majCellCheck 42 25 (majRow_42.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_26 :
    majCellCheck 42 26 (majRow_42.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_27 :
    majCellCheck 42 27 (majRow_42.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_28 :
    majCellCheck 42 28 (majRow_42.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_29 :
    majCellCheck 42 29 (majRow_42.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_30 :
    majCellCheck 42 30 (majRow_42.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_31 :
    majCellCheck 42 31 (majRow_42.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_32 :
    majCellCheck 42 32 (majRow_42.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_33 :
    majCellCheck 42 33 (majRow_42.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_34 :
    majCellCheck 42 34 (majRow_42.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_35 :
    majCellCheck 42 35 (majRow_42.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_36 :
    majCellCheck 42 36 (majRow_42.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_37 :
    majCellCheck 42 37 (majRow_42.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_38 :
    majCellCheck 42 38 (majRow_42.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_39 :
    majCellCheck 42 39 (majRow_42.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_40 :
    majCellCheck 42 40 (majRow_42.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_41 :
    majCellCheck 42 41 (majRow_42.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_cell_42 :
    majCellCheck 42 42 (majRow_42.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_42_all : ∀ l, l ≤ 42 →
    majCellCheck 42 l (majRow_42.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_42_cell_0, majRow_42_cell_1, majRow_42_cell_2, majRow_42_cell_3, majRow_42_cell_4, majRow_42_cell_5, majRow_42_cell_6, majRow_42_cell_7, majRow_42_cell_8, majRow_42_cell_9, majRow_42_cell_10, majRow_42_cell_11, majRow_42_cell_12, majRow_42_cell_13, majRow_42_cell_14, majRow_42_cell_15, majRow_42_cell_16, majRow_42_cell_17, majRow_42_cell_18, majRow_42_cell_19, majRow_42_cell_20, majRow_42_cell_21, majRow_42_cell_22, majRow_42_cell_23, majRow_42_cell_24, majRow_42_cell_25, majRow_42_cell_26, majRow_42_cell_27, majRow_42_cell_28, majRow_42_cell_29, majRow_42_cell_30, majRow_42_cell_31, majRow_42_cell_32, majRow_42_cell_33, majRow_42_cell_34, majRow_42_cell_35, majRow_42_cell_36, majRow_42_cell_37, majRow_42_cell_38, majRow_42_cell_39, majRow_42_cell_40, majRow_42_cell_41, majRow_42_cell_42]

def majRow_43 : List (MajTree × MajTree) := [
  ((.leaf 44), (.leaf 45)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_43_cell_0 :
    majCellCheck 43 0 (majRow_43.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_1 :
    majCellCheck 43 1 (majRow_43.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_2 :
    majCellCheck 43 2 (majRow_43.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_3 :
    majCellCheck 43 3 (majRow_43.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_4 :
    majCellCheck 43 4 (majRow_43.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_5 :
    majCellCheck 43 5 (majRow_43.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_6 :
    majCellCheck 43 6 (majRow_43.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_7 :
    majCellCheck 43 7 (majRow_43.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_8 :
    majCellCheck 43 8 (majRow_43.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_9 :
    majCellCheck 43 9 (majRow_43.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_10 :
    majCellCheck 43 10 (majRow_43.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_11 :
    majCellCheck 43 11 (majRow_43.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_12 :
    majCellCheck 43 12 (majRow_43.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_13 :
    majCellCheck 43 13 (majRow_43.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_14 :
    majCellCheck 43 14 (majRow_43.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_15 :
    majCellCheck 43 15 (majRow_43.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_16 :
    majCellCheck 43 16 (majRow_43.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_17 :
    majCellCheck 43 17 (majRow_43.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_18 :
    majCellCheck 43 18 (majRow_43.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_19 :
    majCellCheck 43 19 (majRow_43.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_20 :
    majCellCheck 43 20 (majRow_43.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_21 :
    majCellCheck 43 21 (majRow_43.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_22 :
    majCellCheck 43 22 (majRow_43.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_23 :
    majCellCheck 43 23 (majRow_43.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_24 :
    majCellCheck 43 24 (majRow_43.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_25 :
    majCellCheck 43 25 (majRow_43.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_26 :
    majCellCheck 43 26 (majRow_43.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_27 :
    majCellCheck 43 27 (majRow_43.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_28 :
    majCellCheck 43 28 (majRow_43.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_29 :
    majCellCheck 43 29 (majRow_43.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_30 :
    majCellCheck 43 30 (majRow_43.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_31 :
    majCellCheck 43 31 (majRow_43.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_32 :
    majCellCheck 43 32 (majRow_43.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_33 :
    majCellCheck 43 33 (majRow_43.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_34 :
    majCellCheck 43 34 (majRow_43.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_35 :
    majCellCheck 43 35 (majRow_43.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_36 :
    majCellCheck 43 36 (majRow_43.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_37 :
    majCellCheck 43 37 (majRow_43.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_38 :
    majCellCheck 43 38 (majRow_43.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_39 :
    majCellCheck 43 39 (majRow_43.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_40 :
    majCellCheck 43 40 (majRow_43.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_41 :
    majCellCheck 43 41 (majRow_43.getD 41 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_42 :
    majCellCheck 43 42 (majRow_43.getD 42 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_cell_43 :
    majCellCheck 43 43 (majRow_43.getD 43 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_43_all : ∀ l, l ≤ 43 →
    majCellCheck 43 l (majRow_43.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_43_cell_0, majRow_43_cell_1, majRow_43_cell_2, majRow_43_cell_3, majRow_43_cell_4, majRow_43_cell_5, majRow_43_cell_6, majRow_43_cell_7, majRow_43_cell_8, majRow_43_cell_9, majRow_43_cell_10, majRow_43_cell_11, majRow_43_cell_12, majRow_43_cell_13, majRow_43_cell_14, majRow_43_cell_15, majRow_43_cell_16, majRow_43_cell_17, majRow_43_cell_18, majRow_43_cell_19, majRow_43_cell_20, majRow_43_cell_21, majRow_43_cell_22, majRow_43_cell_23, majRow_43_cell_24, majRow_43_cell_25, majRow_43_cell_26, majRow_43_cell_27, majRow_43_cell_28, majRow_43_cell_29, majRow_43_cell_30, majRow_43_cell_31, majRow_43_cell_32, majRow_43_cell_33, majRow_43_cell_34, majRow_43_cell_35, majRow_43_cell_36, majRow_43_cell_37, majRow_43_cell_38, majRow_43_cell_39, majRow_43_cell_40, majRow_43_cell_41, majRow_43_cell_42, majRow_43_cell_43]

end PartialBalayage.Maximal.Square
