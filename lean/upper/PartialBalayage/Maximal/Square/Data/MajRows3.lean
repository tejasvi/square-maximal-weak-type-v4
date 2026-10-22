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

def majRow_31 : List (MajTree × MajTree) := [
  ((.leaf 32), (.leaf 33)),
  ((.leaf 33), (.leaf 34)),
  ((.leaf 34), (.leaf 35)),
  ((.leaf 35), (.leaf 36)),
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
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_31_cell_0 :
    majCellCheck 31 0 (majRow_31.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_1 :
    majCellCheck 31 1 (majRow_31.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_2 :
    majCellCheck 31 2 (majRow_31.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_3 :
    majCellCheck 31 3 (majRow_31.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_4 :
    majCellCheck 31 4 (majRow_31.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_5 :
    majCellCheck 31 5 (majRow_31.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_6 :
    majCellCheck 31 6 (majRow_31.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_7 :
    majCellCheck 31 7 (majRow_31.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_8 :
    majCellCheck 31 8 (majRow_31.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_9 :
    majCellCheck 31 9 (majRow_31.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_10 :
    majCellCheck 31 10 (majRow_31.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_11 :
    majCellCheck 31 11 (majRow_31.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_12 :
    majCellCheck 31 12 (majRow_31.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_13 :
    majCellCheck 31 13 (majRow_31.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_14 :
    majCellCheck 31 14 (majRow_31.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_15 :
    majCellCheck 31 15 (majRow_31.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_16 :
    majCellCheck 31 16 (majRow_31.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_17 :
    majCellCheck 31 17 (majRow_31.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_18 :
    majCellCheck 31 18 (majRow_31.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_19 :
    majCellCheck 31 19 (majRow_31.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_20 :
    majCellCheck 31 20 (majRow_31.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_21 :
    majCellCheck 31 21 (majRow_31.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_22 :
    majCellCheck 31 22 (majRow_31.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_23 :
    majCellCheck 31 23 (majRow_31.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_24 :
    majCellCheck 31 24 (majRow_31.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_25 :
    majCellCheck 31 25 (majRow_31.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_26 :
    majCellCheck 31 26 (majRow_31.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_27 :
    majCellCheck 31 27 (majRow_31.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_28 :
    majCellCheck 31 28 (majRow_31.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_29 :
    majCellCheck 31 29 (majRow_31.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_30 :
    majCellCheck 31 30 (majRow_31.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_cell_31 :
    majCellCheck 31 31 (majRow_31.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_31_all : ∀ l, l ≤ 31 →
    majCellCheck 31 l (majRow_31.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_31_cell_0, majRow_31_cell_1, majRow_31_cell_2, majRow_31_cell_3, majRow_31_cell_4, majRow_31_cell_5, majRow_31_cell_6, majRow_31_cell_7, majRow_31_cell_8, majRow_31_cell_9, majRow_31_cell_10, majRow_31_cell_11, majRow_31_cell_12, majRow_31_cell_13, majRow_31_cell_14, majRow_31_cell_15, majRow_31_cell_16, majRow_31_cell_17, majRow_31_cell_18, majRow_31_cell_19, majRow_31_cell_20, majRow_31_cell_21, majRow_31_cell_22, majRow_31_cell_23, majRow_31_cell_24, majRow_31_cell_25, majRow_31_cell_26, majRow_31_cell_27, majRow_31_cell_28, majRow_31_cell_29, majRow_31_cell_30, majRow_31_cell_31]

def majRow_32 : List (MajTree × MajTree) := [
  ((.leaf 33), (.leaf 34)),
  ((.leaf 34), (.leaf 35)),
  ((.leaf 35), (.leaf 36)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_32_cell_0 :
    majCellCheck 32 0 (majRow_32.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_1 :
    majCellCheck 32 1 (majRow_32.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_2 :
    majCellCheck 32 2 (majRow_32.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_3 :
    majCellCheck 32 3 (majRow_32.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_4 :
    majCellCheck 32 4 (majRow_32.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_5 :
    majCellCheck 32 5 (majRow_32.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_6 :
    majCellCheck 32 6 (majRow_32.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_7 :
    majCellCheck 32 7 (majRow_32.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_8 :
    majCellCheck 32 8 (majRow_32.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_9 :
    majCellCheck 32 9 (majRow_32.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_10 :
    majCellCheck 32 10 (majRow_32.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_11 :
    majCellCheck 32 11 (majRow_32.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_12 :
    majCellCheck 32 12 (majRow_32.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_13 :
    majCellCheck 32 13 (majRow_32.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_14 :
    majCellCheck 32 14 (majRow_32.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_15 :
    majCellCheck 32 15 (majRow_32.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_16 :
    majCellCheck 32 16 (majRow_32.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_17 :
    majCellCheck 32 17 (majRow_32.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_18 :
    majCellCheck 32 18 (majRow_32.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_19 :
    majCellCheck 32 19 (majRow_32.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_20 :
    majCellCheck 32 20 (majRow_32.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_21 :
    majCellCheck 32 21 (majRow_32.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_22 :
    majCellCheck 32 22 (majRow_32.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_23 :
    majCellCheck 32 23 (majRow_32.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_24 :
    majCellCheck 32 24 (majRow_32.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_25 :
    majCellCheck 32 25 (majRow_32.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_26 :
    majCellCheck 32 26 (majRow_32.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_27 :
    majCellCheck 32 27 (majRow_32.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_28 :
    majCellCheck 32 28 (majRow_32.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_29 :
    majCellCheck 32 29 (majRow_32.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_30 :
    majCellCheck 32 30 (majRow_32.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_31 :
    majCellCheck 32 31 (majRow_32.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_cell_32 :
    majCellCheck 32 32 (majRow_32.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_32_all : ∀ l, l ≤ 32 →
    majCellCheck 32 l (majRow_32.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_32_cell_0, majRow_32_cell_1, majRow_32_cell_2, majRow_32_cell_3, majRow_32_cell_4, majRow_32_cell_5, majRow_32_cell_6, majRow_32_cell_7, majRow_32_cell_8, majRow_32_cell_9, majRow_32_cell_10, majRow_32_cell_11, majRow_32_cell_12, majRow_32_cell_13, majRow_32_cell_14, majRow_32_cell_15, majRow_32_cell_16, majRow_32_cell_17, majRow_32_cell_18, majRow_32_cell_19, majRow_32_cell_20, majRow_32_cell_21, majRow_32_cell_22, majRow_32_cell_23, majRow_32_cell_24, majRow_32_cell_25, majRow_32_cell_26, majRow_32_cell_27, majRow_32_cell_28, majRow_32_cell_29, majRow_32_cell_30, majRow_32_cell_31, majRow_32_cell_32]

def majRow_33 : List (MajTree × MajTree) := [
  ((.leaf 34), (.leaf 35)),
  ((.leaf 35), (.leaf 36)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_33_cell_0 :
    majCellCheck 33 0 (majRow_33.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_1 :
    majCellCheck 33 1 (majRow_33.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_2 :
    majCellCheck 33 2 (majRow_33.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_3 :
    majCellCheck 33 3 (majRow_33.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_4 :
    majCellCheck 33 4 (majRow_33.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_5 :
    majCellCheck 33 5 (majRow_33.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_6 :
    majCellCheck 33 6 (majRow_33.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_7 :
    majCellCheck 33 7 (majRow_33.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_8 :
    majCellCheck 33 8 (majRow_33.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_9 :
    majCellCheck 33 9 (majRow_33.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_10 :
    majCellCheck 33 10 (majRow_33.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_11 :
    majCellCheck 33 11 (majRow_33.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_12 :
    majCellCheck 33 12 (majRow_33.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_13 :
    majCellCheck 33 13 (majRow_33.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_14 :
    majCellCheck 33 14 (majRow_33.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_15 :
    majCellCheck 33 15 (majRow_33.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_16 :
    majCellCheck 33 16 (majRow_33.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_17 :
    majCellCheck 33 17 (majRow_33.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_18 :
    majCellCheck 33 18 (majRow_33.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_19 :
    majCellCheck 33 19 (majRow_33.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_20 :
    majCellCheck 33 20 (majRow_33.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_21 :
    majCellCheck 33 21 (majRow_33.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_22 :
    majCellCheck 33 22 (majRow_33.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_23 :
    majCellCheck 33 23 (majRow_33.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_24 :
    majCellCheck 33 24 (majRow_33.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_25 :
    majCellCheck 33 25 (majRow_33.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_26 :
    majCellCheck 33 26 (majRow_33.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_27 :
    majCellCheck 33 27 (majRow_33.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_28 :
    majCellCheck 33 28 (majRow_33.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_29 :
    majCellCheck 33 29 (majRow_33.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_30 :
    majCellCheck 33 30 (majRow_33.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_31 :
    majCellCheck 33 31 (majRow_33.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_32 :
    majCellCheck 33 32 (majRow_33.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_cell_33 :
    majCellCheck 33 33 (majRow_33.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_33_all : ∀ l, l ≤ 33 →
    majCellCheck 33 l (majRow_33.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_33_cell_0, majRow_33_cell_1, majRow_33_cell_2, majRow_33_cell_3, majRow_33_cell_4, majRow_33_cell_5, majRow_33_cell_6, majRow_33_cell_7, majRow_33_cell_8, majRow_33_cell_9, majRow_33_cell_10, majRow_33_cell_11, majRow_33_cell_12, majRow_33_cell_13, majRow_33_cell_14, majRow_33_cell_15, majRow_33_cell_16, majRow_33_cell_17, majRow_33_cell_18, majRow_33_cell_19, majRow_33_cell_20, majRow_33_cell_21, majRow_33_cell_22, majRow_33_cell_23, majRow_33_cell_24, majRow_33_cell_25, majRow_33_cell_26, majRow_33_cell_27, majRow_33_cell_28, majRow_33_cell_29, majRow_33_cell_30, majRow_33_cell_31, majRow_33_cell_32, majRow_33_cell_33]

def majRow_34 : List (MajTree × MajTree) := [
  ((.leaf 35), (.leaf 36)),
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
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_34_cell_0 :
    majCellCheck 34 0 (majRow_34.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_1 :
    majCellCheck 34 1 (majRow_34.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_2 :
    majCellCheck 34 2 (majRow_34.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_3 :
    majCellCheck 34 3 (majRow_34.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_4 :
    majCellCheck 34 4 (majRow_34.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_5 :
    majCellCheck 34 5 (majRow_34.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_6 :
    majCellCheck 34 6 (majRow_34.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_7 :
    majCellCheck 34 7 (majRow_34.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_8 :
    majCellCheck 34 8 (majRow_34.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_9 :
    majCellCheck 34 9 (majRow_34.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_10 :
    majCellCheck 34 10 (majRow_34.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_11 :
    majCellCheck 34 11 (majRow_34.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_12 :
    majCellCheck 34 12 (majRow_34.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_13 :
    majCellCheck 34 13 (majRow_34.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_14 :
    majCellCheck 34 14 (majRow_34.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_15 :
    majCellCheck 34 15 (majRow_34.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_16 :
    majCellCheck 34 16 (majRow_34.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_17 :
    majCellCheck 34 17 (majRow_34.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_18 :
    majCellCheck 34 18 (majRow_34.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_19 :
    majCellCheck 34 19 (majRow_34.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_20 :
    majCellCheck 34 20 (majRow_34.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_21 :
    majCellCheck 34 21 (majRow_34.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_22 :
    majCellCheck 34 22 (majRow_34.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_23 :
    majCellCheck 34 23 (majRow_34.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_24 :
    majCellCheck 34 24 (majRow_34.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_25 :
    majCellCheck 34 25 (majRow_34.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_26 :
    majCellCheck 34 26 (majRow_34.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_27 :
    majCellCheck 34 27 (majRow_34.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_28 :
    majCellCheck 34 28 (majRow_34.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_29 :
    majCellCheck 34 29 (majRow_34.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_30 :
    majCellCheck 34 30 (majRow_34.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_31 :
    majCellCheck 34 31 (majRow_34.getD 31 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_32 :
    majCellCheck 34 32 (majRow_34.getD 32 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_33 :
    majCellCheck 34 33 (majRow_34.getD 33 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_cell_34 :
    majCellCheck 34 34 (majRow_34.getD 34 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_34_all : ∀ l, l ≤ 34 →
    majCellCheck 34 l (majRow_34.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_34_cell_0, majRow_34_cell_1, majRow_34_cell_2, majRow_34_cell_3, majRow_34_cell_4, majRow_34_cell_5, majRow_34_cell_6, majRow_34_cell_7, majRow_34_cell_8, majRow_34_cell_9, majRow_34_cell_10, majRow_34_cell_11, majRow_34_cell_12, majRow_34_cell_13, majRow_34_cell_14, majRow_34_cell_15, majRow_34_cell_16, majRow_34_cell_17, majRow_34_cell_18, majRow_34_cell_19, majRow_34_cell_20, majRow_34_cell_21, majRow_34_cell_22, majRow_34_cell_23, majRow_34_cell_24, majRow_34_cell_25, majRow_34_cell_26, majRow_34_cell_27, majRow_34_cell_28, majRow_34_cell_29, majRow_34_cell_30, majRow_34_cell_31, majRow_34_cell_32, majRow_34_cell_33, majRow_34_cell_34]

end PartialBalayage.Maximal.Square
