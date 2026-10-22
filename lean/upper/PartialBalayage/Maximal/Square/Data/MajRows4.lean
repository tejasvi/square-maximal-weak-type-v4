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

def majRow_35 : List (MajTree × MajTree) := [
  ((.leaf 36), (.leaf 37)),
  ((.leaf 37), (.leaf 38)),
  ((.leaf 38), (.leaf 39)),
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
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_35_cell_0 :
    majCellCheck 35 0 (majRow_35.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_1 :
    majCellCheck 35 1 (majRow_35.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_2 :
    majCellCheck 35 2 (majRow_35.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_3 :
    majCellCheck 35 3 (majRow_35.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_4 :
    majCellCheck 35 4 (majRow_35.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_5 :
    majCellCheck 35 5 (majRow_35.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_6 :
    majCellCheck 35 6 (majRow_35.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_7 :
    majCellCheck 35 7 (majRow_35.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_8 :
    majCellCheck 35 8 (majRow_35.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_9 :
    majCellCheck 35 9 (majRow_35.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_10 :
    majCellCheck 35 10 (majRow_35.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_11 :
    majCellCheck 35 11 (majRow_35.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_12 :
    majCellCheck 35 12 (majRow_35.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_13 :
    majCellCheck 35 13 (majRow_35.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_14 :
    majCellCheck 35 14 (majRow_35.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_15 :
    majCellCheck 35 15 (majRow_35.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_16 :
    majCellCheck 35 16 (majRow_35.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_17 :
    majCellCheck 35 17 (majRow_35.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_18 :
    majCellCheck 35 18 (majRow_35.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_19 :
    majCellCheck 35 19 (majRow_35.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_20 :
    majCellCheck 35 20 (majRow_35.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_21 :
    majCellCheck 35 21 (majRow_35.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_22 :
    majCellCheck 35 22 (majRow_35.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_23 :
    majCellCheck 35 23 (majRow_35.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_24 :
    majCellCheck 35 24 (majRow_35.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_25 :
    majCellCheck 35 25 (majRow_35.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_26 :
    majCellCheck 35 26 (majRow_35.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_27 :
    majCellCheck 35 27 (majRow_35.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_28 :
    majCellCheck 35 28 (majRow_35.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_29 :
    majCellCheck 35 29 (majRow_35.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_30 :
    majCellCheck 35 30 (majRow_35.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_31 :
    majCellCheck 35 31 (majRow_35.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_32 :
    majCellCheck 35 32 (majRow_35.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_33 :
    majCellCheck 35 33 (majRow_35.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_34 :
    majCellCheck 35 34 (majRow_35.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_cell_35 :
    majCellCheck 35 35 (majRow_35.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_35_all : ∀ l, l ≤ 35 →
    majCellCheck 35 l (majRow_35.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_35_cell_0, majRow_35_cell_1, majRow_35_cell_2, majRow_35_cell_3, majRow_35_cell_4, majRow_35_cell_5, majRow_35_cell_6, majRow_35_cell_7, majRow_35_cell_8, majRow_35_cell_9, majRow_35_cell_10, majRow_35_cell_11, majRow_35_cell_12, majRow_35_cell_13, majRow_35_cell_14, majRow_35_cell_15, majRow_35_cell_16, majRow_35_cell_17, majRow_35_cell_18, majRow_35_cell_19, majRow_35_cell_20, majRow_35_cell_21, majRow_35_cell_22, majRow_35_cell_23, majRow_35_cell_24, majRow_35_cell_25, majRow_35_cell_26, majRow_35_cell_27, majRow_35_cell_28, majRow_35_cell_29, majRow_35_cell_30, majRow_35_cell_31, majRow_35_cell_32, majRow_35_cell_33, majRow_35_cell_34, majRow_35_cell_35]

def majRow_36 : List (MajTree × MajTree) := [
  ((.leaf 37), (.leaf 38)),
  ((.leaf 38), (.leaf 39)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_36_cell_0 :
    majCellCheck 36 0 (majRow_36.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_1 :
    majCellCheck 36 1 (majRow_36.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_2 :
    majCellCheck 36 2 (majRow_36.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_3 :
    majCellCheck 36 3 (majRow_36.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_4 :
    majCellCheck 36 4 (majRow_36.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_5 :
    majCellCheck 36 5 (majRow_36.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_6 :
    majCellCheck 36 6 (majRow_36.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_7 :
    majCellCheck 36 7 (majRow_36.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_8 :
    majCellCheck 36 8 (majRow_36.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_9 :
    majCellCheck 36 9 (majRow_36.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_10 :
    majCellCheck 36 10 (majRow_36.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_11 :
    majCellCheck 36 11 (majRow_36.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_12 :
    majCellCheck 36 12 (majRow_36.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_13 :
    majCellCheck 36 13 (majRow_36.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_14 :
    majCellCheck 36 14 (majRow_36.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_15 :
    majCellCheck 36 15 (majRow_36.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_16 :
    majCellCheck 36 16 (majRow_36.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_17 :
    majCellCheck 36 17 (majRow_36.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_18 :
    majCellCheck 36 18 (majRow_36.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_19 :
    majCellCheck 36 19 (majRow_36.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_20 :
    majCellCheck 36 20 (majRow_36.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_21 :
    majCellCheck 36 21 (majRow_36.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_22 :
    majCellCheck 36 22 (majRow_36.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_23 :
    majCellCheck 36 23 (majRow_36.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_24 :
    majCellCheck 36 24 (majRow_36.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_25 :
    majCellCheck 36 25 (majRow_36.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_26 :
    majCellCheck 36 26 (majRow_36.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_27 :
    majCellCheck 36 27 (majRow_36.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_28 :
    majCellCheck 36 28 (majRow_36.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_29 :
    majCellCheck 36 29 (majRow_36.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_30 :
    majCellCheck 36 30 (majRow_36.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_31 :
    majCellCheck 36 31 (majRow_36.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_32 :
    majCellCheck 36 32 (majRow_36.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_33 :
    majCellCheck 36 33 (majRow_36.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_34 :
    majCellCheck 36 34 (majRow_36.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_35 :
    majCellCheck 36 35 (majRow_36.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_cell_36 :
    majCellCheck 36 36 (majRow_36.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_36_all : ∀ l, l ≤ 36 →
    majCellCheck 36 l (majRow_36.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_36_cell_0, majRow_36_cell_1, majRow_36_cell_2, majRow_36_cell_3, majRow_36_cell_4, majRow_36_cell_5, majRow_36_cell_6, majRow_36_cell_7, majRow_36_cell_8, majRow_36_cell_9, majRow_36_cell_10, majRow_36_cell_11, majRow_36_cell_12, majRow_36_cell_13, majRow_36_cell_14, majRow_36_cell_15, majRow_36_cell_16, majRow_36_cell_17, majRow_36_cell_18, majRow_36_cell_19, majRow_36_cell_20, majRow_36_cell_21, majRow_36_cell_22, majRow_36_cell_23, majRow_36_cell_24, majRow_36_cell_25, majRow_36_cell_26, majRow_36_cell_27, majRow_36_cell_28, majRow_36_cell_29, majRow_36_cell_30, majRow_36_cell_31, majRow_36_cell_32, majRow_36_cell_33, majRow_36_cell_34, majRow_36_cell_35, majRow_36_cell_36]

def majRow_37 : List (MajTree × MajTree) := [
  ((.leaf 38), (.leaf 39)),
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
  ((.leaf 0), (.leaf 0))
]

theorem majRow_37_cell_0 :
    majCellCheck 37 0 (majRow_37.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_1 :
    majCellCheck 37 1 (majRow_37.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_2 :
    majCellCheck 37 2 (majRow_37.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_3 :
    majCellCheck 37 3 (majRow_37.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_4 :
    majCellCheck 37 4 (majRow_37.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_5 :
    majCellCheck 37 5 (majRow_37.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_6 :
    majCellCheck 37 6 (majRow_37.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_7 :
    majCellCheck 37 7 (majRow_37.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_8 :
    majCellCheck 37 8 (majRow_37.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_9 :
    majCellCheck 37 9 (majRow_37.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_10 :
    majCellCheck 37 10 (majRow_37.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_11 :
    majCellCheck 37 11 (majRow_37.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_12 :
    majCellCheck 37 12 (majRow_37.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_13 :
    majCellCheck 37 13 (majRow_37.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_14 :
    majCellCheck 37 14 (majRow_37.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_15 :
    majCellCheck 37 15 (majRow_37.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_16 :
    majCellCheck 37 16 (majRow_37.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_17 :
    majCellCheck 37 17 (majRow_37.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_18 :
    majCellCheck 37 18 (majRow_37.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_19 :
    majCellCheck 37 19 (majRow_37.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_20 :
    majCellCheck 37 20 (majRow_37.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_21 :
    majCellCheck 37 21 (majRow_37.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_22 :
    majCellCheck 37 22 (majRow_37.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_23 :
    majCellCheck 37 23 (majRow_37.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_24 :
    majCellCheck 37 24 (majRow_37.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_25 :
    majCellCheck 37 25 (majRow_37.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_26 :
    majCellCheck 37 26 (majRow_37.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_27 :
    majCellCheck 37 27 (majRow_37.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_28 :
    majCellCheck 37 28 (majRow_37.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_29 :
    majCellCheck 37 29 (majRow_37.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_30 :
    majCellCheck 37 30 (majRow_37.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_31 :
    majCellCheck 37 31 (majRow_37.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_32 :
    majCellCheck 37 32 (majRow_37.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_33 :
    majCellCheck 37 33 (majRow_37.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_34 :
    majCellCheck 37 34 (majRow_37.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_35 :
    majCellCheck 37 35 (majRow_37.getD 35 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_36 :
    majCellCheck 37 36 (majRow_37.getD 36 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_cell_37 :
    majCellCheck 37 37 (majRow_37.getD 37 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_37_all : ∀ l, l ≤ 37 →
    majCellCheck 37 l (majRow_37.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_37_cell_0, majRow_37_cell_1, majRow_37_cell_2, majRow_37_cell_3, majRow_37_cell_4, majRow_37_cell_5, majRow_37_cell_6, majRow_37_cell_7, majRow_37_cell_8, majRow_37_cell_9, majRow_37_cell_10, majRow_37_cell_11, majRow_37_cell_12, majRow_37_cell_13, majRow_37_cell_14, majRow_37_cell_15, majRow_37_cell_16, majRow_37_cell_17, majRow_37_cell_18, majRow_37_cell_19, majRow_37_cell_20, majRow_37_cell_21, majRow_37_cell_22, majRow_37_cell_23, majRow_37_cell_24, majRow_37_cell_25, majRow_37_cell_26, majRow_37_cell_27, majRow_37_cell_28, majRow_37_cell_29, majRow_37_cell_30, majRow_37_cell_31, majRow_37_cell_32, majRow_37_cell_33, majRow_37_cell_34, majRow_37_cell_35, majRow_37_cell_36, majRow_37_cell_37]

end PartialBalayage.Maximal.Square
