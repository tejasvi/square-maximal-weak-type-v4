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

def majRow_38 : List (MajTree × MajTree) := [
  ((.leaf 39), (.leaf 40)),
  ((.leaf 40), (.leaf 41)),
  ((.leaf 41), (.leaf 42)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_38_cell_0 :
    majCellCheck 38 0 (majRow_38.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_1 :
    majCellCheck 38 1 (majRow_38.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_2 :
    majCellCheck 38 2 (majRow_38.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_3 :
    majCellCheck 38 3 (majRow_38.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_4 :
    majCellCheck 38 4 (majRow_38.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_5 :
    majCellCheck 38 5 (majRow_38.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_6 :
    majCellCheck 38 6 (majRow_38.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_7 :
    majCellCheck 38 7 (majRow_38.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_8 :
    majCellCheck 38 8 (majRow_38.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_9 :
    majCellCheck 38 9 (majRow_38.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_10 :
    majCellCheck 38 10 (majRow_38.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_11 :
    majCellCheck 38 11 (majRow_38.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_12 :
    majCellCheck 38 12 (majRow_38.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_13 :
    majCellCheck 38 13 (majRow_38.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_14 :
    majCellCheck 38 14 (majRow_38.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_15 :
    majCellCheck 38 15 (majRow_38.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_16 :
    majCellCheck 38 16 (majRow_38.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_17 :
    majCellCheck 38 17 (majRow_38.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_18 :
    majCellCheck 38 18 (majRow_38.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_19 :
    majCellCheck 38 19 (majRow_38.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_20 :
    majCellCheck 38 20 (majRow_38.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_21 :
    majCellCheck 38 21 (majRow_38.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_22 :
    majCellCheck 38 22 (majRow_38.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_23 :
    majCellCheck 38 23 (majRow_38.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_24 :
    majCellCheck 38 24 (majRow_38.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_25 :
    majCellCheck 38 25 (majRow_38.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_26 :
    majCellCheck 38 26 (majRow_38.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_27 :
    majCellCheck 38 27 (majRow_38.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_28 :
    majCellCheck 38 28 (majRow_38.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_29 :
    majCellCheck 38 29 (majRow_38.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_30 :
    majCellCheck 38 30 (majRow_38.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_31 :
    majCellCheck 38 31 (majRow_38.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_32 :
    majCellCheck 38 32 (majRow_38.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_33 :
    majCellCheck 38 33 (majRow_38.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_34 :
    majCellCheck 38 34 (majRow_38.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_35 :
    majCellCheck 38 35 (majRow_38.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_36 :
    majCellCheck 38 36 (majRow_38.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_37 :
    majCellCheck 38 37 (majRow_38.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_cell_38 :
    majCellCheck 38 38 (majRow_38.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_38_all : ∀ l, l ≤ 38 →
    majCellCheck 38 l (majRow_38.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_38_cell_0, majRow_38_cell_1, majRow_38_cell_2, majRow_38_cell_3, majRow_38_cell_4, majRow_38_cell_5, majRow_38_cell_6, majRow_38_cell_7, majRow_38_cell_8, majRow_38_cell_9, majRow_38_cell_10, majRow_38_cell_11, majRow_38_cell_12, majRow_38_cell_13, majRow_38_cell_14, majRow_38_cell_15, majRow_38_cell_16, majRow_38_cell_17, majRow_38_cell_18, majRow_38_cell_19, majRow_38_cell_20, majRow_38_cell_21, majRow_38_cell_22, majRow_38_cell_23, majRow_38_cell_24, majRow_38_cell_25, majRow_38_cell_26, majRow_38_cell_27, majRow_38_cell_28, majRow_38_cell_29, majRow_38_cell_30, majRow_38_cell_31, majRow_38_cell_32, majRow_38_cell_33, majRow_38_cell_34, majRow_38_cell_35, majRow_38_cell_36, majRow_38_cell_37, majRow_38_cell_38]

def majRow_39 : List (MajTree × MajTree) := [
  ((.leaf 40), (.leaf 41)),
  ((.leaf 41), (.leaf 42)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_39_cell_0 :
    majCellCheck 39 0 (majRow_39.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_1 :
    majCellCheck 39 1 (majRow_39.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_2 :
    majCellCheck 39 2 (majRow_39.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_3 :
    majCellCheck 39 3 (majRow_39.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_4 :
    majCellCheck 39 4 (majRow_39.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_5 :
    majCellCheck 39 5 (majRow_39.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_6 :
    majCellCheck 39 6 (majRow_39.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_7 :
    majCellCheck 39 7 (majRow_39.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_8 :
    majCellCheck 39 8 (majRow_39.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_9 :
    majCellCheck 39 9 (majRow_39.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_10 :
    majCellCheck 39 10 (majRow_39.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_11 :
    majCellCheck 39 11 (majRow_39.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_12 :
    majCellCheck 39 12 (majRow_39.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_13 :
    majCellCheck 39 13 (majRow_39.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_14 :
    majCellCheck 39 14 (majRow_39.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_15 :
    majCellCheck 39 15 (majRow_39.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_16 :
    majCellCheck 39 16 (majRow_39.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_17 :
    majCellCheck 39 17 (majRow_39.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_18 :
    majCellCheck 39 18 (majRow_39.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_19 :
    majCellCheck 39 19 (majRow_39.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_20 :
    majCellCheck 39 20 (majRow_39.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_21 :
    majCellCheck 39 21 (majRow_39.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_22 :
    majCellCheck 39 22 (majRow_39.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_23 :
    majCellCheck 39 23 (majRow_39.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_24 :
    majCellCheck 39 24 (majRow_39.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_25 :
    majCellCheck 39 25 (majRow_39.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_26 :
    majCellCheck 39 26 (majRow_39.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_27 :
    majCellCheck 39 27 (majRow_39.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_28 :
    majCellCheck 39 28 (majRow_39.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_29 :
    majCellCheck 39 29 (majRow_39.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_30 :
    majCellCheck 39 30 (majRow_39.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_31 :
    majCellCheck 39 31 (majRow_39.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_32 :
    majCellCheck 39 32 (majRow_39.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_33 :
    majCellCheck 39 33 (majRow_39.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_34 :
    majCellCheck 39 34 (majRow_39.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_35 :
    majCellCheck 39 35 (majRow_39.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_36 :
    majCellCheck 39 36 (majRow_39.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_37 :
    majCellCheck 39 37 (majRow_39.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_38 :
    majCellCheck 39 38 (majRow_39.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_cell_39 :
    majCellCheck 39 39 (majRow_39.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_39_all : ∀ l, l ≤ 39 →
    majCellCheck 39 l (majRow_39.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_39_cell_0, majRow_39_cell_1, majRow_39_cell_2, majRow_39_cell_3, majRow_39_cell_4, majRow_39_cell_5, majRow_39_cell_6, majRow_39_cell_7, majRow_39_cell_8, majRow_39_cell_9, majRow_39_cell_10, majRow_39_cell_11, majRow_39_cell_12, majRow_39_cell_13, majRow_39_cell_14, majRow_39_cell_15, majRow_39_cell_16, majRow_39_cell_17, majRow_39_cell_18, majRow_39_cell_19, majRow_39_cell_20, majRow_39_cell_21, majRow_39_cell_22, majRow_39_cell_23, majRow_39_cell_24, majRow_39_cell_25, majRow_39_cell_26, majRow_39_cell_27, majRow_39_cell_28, majRow_39_cell_29, majRow_39_cell_30, majRow_39_cell_31, majRow_39_cell_32, majRow_39_cell_33, majRow_39_cell_34, majRow_39_cell_35, majRow_39_cell_36, majRow_39_cell_37, majRow_39_cell_38, majRow_39_cell_39]

def majRow_40 : List (MajTree × MajTree) := [
  ((.leaf 41), (.leaf 42)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
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

theorem majRow_40_cell_0 :
    majCellCheck 40 0 (majRow_40.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_1 :
    majCellCheck 40 1 (majRow_40.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_2 :
    majCellCheck 40 2 (majRow_40.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_3 :
    majCellCheck 40 3 (majRow_40.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_4 :
    majCellCheck 40 4 (majRow_40.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_5 :
    majCellCheck 40 5 (majRow_40.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_6 :
    majCellCheck 40 6 (majRow_40.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_7 :
    majCellCheck 40 7 (majRow_40.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_8 :
    majCellCheck 40 8 (majRow_40.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_9 :
    majCellCheck 40 9 (majRow_40.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_10 :
    majCellCheck 40 10 (majRow_40.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_11 :
    majCellCheck 40 11 (majRow_40.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_12 :
    majCellCheck 40 12 (majRow_40.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_13 :
    majCellCheck 40 13 (majRow_40.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_14 :
    majCellCheck 40 14 (majRow_40.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_15 :
    majCellCheck 40 15 (majRow_40.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_16 :
    majCellCheck 40 16 (majRow_40.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_17 :
    majCellCheck 40 17 (majRow_40.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_18 :
    majCellCheck 40 18 (majRow_40.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_19 :
    majCellCheck 40 19 (majRow_40.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_20 :
    majCellCheck 40 20 (majRow_40.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_21 :
    majCellCheck 40 21 (majRow_40.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_22 :
    majCellCheck 40 22 (majRow_40.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_23 :
    majCellCheck 40 23 (majRow_40.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_24 :
    majCellCheck 40 24 (majRow_40.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_25 :
    majCellCheck 40 25 (majRow_40.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_26 :
    majCellCheck 40 26 (majRow_40.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_27 :
    majCellCheck 40 27 (majRow_40.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_28 :
    majCellCheck 40 28 (majRow_40.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_29 :
    majCellCheck 40 29 (majRow_40.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_30 :
    majCellCheck 40 30 (majRow_40.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_31 :
    majCellCheck 40 31 (majRow_40.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_32 :
    majCellCheck 40 32 (majRow_40.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_33 :
    majCellCheck 40 33 (majRow_40.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_34 :
    majCellCheck 40 34 (majRow_40.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_35 :
    majCellCheck 40 35 (majRow_40.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_36 :
    majCellCheck 40 36 (majRow_40.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_37 :
    majCellCheck 40 37 (majRow_40.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_38 :
    majCellCheck 40 38 (majRow_40.getD 38 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_39 :
    majCellCheck 40 39 (majRow_40.getD 39 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_cell_40 :
    majCellCheck 40 40 (majRow_40.getD 40 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_40_all : ∀ l, l ≤ 40 →
    majCellCheck 40 l (majRow_40.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_40_cell_0, majRow_40_cell_1, majRow_40_cell_2, majRow_40_cell_3, majRow_40_cell_4, majRow_40_cell_5, majRow_40_cell_6, majRow_40_cell_7, majRow_40_cell_8, majRow_40_cell_9, majRow_40_cell_10, majRow_40_cell_11, majRow_40_cell_12, majRow_40_cell_13, majRow_40_cell_14, majRow_40_cell_15, majRow_40_cell_16, majRow_40_cell_17, majRow_40_cell_18, majRow_40_cell_19, majRow_40_cell_20, majRow_40_cell_21, majRow_40_cell_22, majRow_40_cell_23, majRow_40_cell_24, majRow_40_cell_25, majRow_40_cell_26, majRow_40_cell_27, majRow_40_cell_28, majRow_40_cell_29, majRow_40_cell_30, majRow_40_cell_31, majRow_40_cell_32, majRow_40_cell_33, majRow_40_cell_34, majRow_40_cell_35, majRow_40_cell_36, majRow_40_cell_37, majRow_40_cell_38, majRow_40_cell_39, majRow_40_cell_40]

end PartialBalayage.Maximal.Square
