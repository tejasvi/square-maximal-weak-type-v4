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

def majRow_26 : List (MajTree × MajTree) := [
  ((.leaf 27), (.leaf 28)),
  ((.leaf 28), (.leaf 29)),
  ((.leaf 29), (.leaf 30)),
  ((.leaf 30), (.leaf 31)),
  ((.leaf 31), (.leaf 32)),
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
  ((.node (.leaf 51) (.leaf 51) (.leaf 51) (.leaf 51)), (.node (.leaf 52) (.leaf 151) (.leaf 151) (.leaf 151))),
  ((.leaf 52), (.leaf 53)),
  ((.leaf 53), (.leaf 0))
]

theorem majRow_26_cell_0 :
    majCellCheck 26 0 (majRow_26.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_1 :
    majCellCheck 26 1 (majRow_26.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_2 :
    majCellCheck 26 2 (majRow_26.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_3 :
    majCellCheck 26 3 (majRow_26.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_4 :
    majCellCheck 26 4 (majRow_26.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_5 :
    majCellCheck 26 5 (majRow_26.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_6 :
    majCellCheck 26 6 (majRow_26.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_7 :
    majCellCheck 26 7 (majRow_26.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_8 :
    majCellCheck 26 8 (majRow_26.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_9 :
    majCellCheck 26 9 (majRow_26.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_10 :
    majCellCheck 26 10 (majRow_26.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_11 :
    majCellCheck 26 11 (majRow_26.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_12 :
    majCellCheck 26 12 (majRow_26.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_13 :
    majCellCheck 26 13 (majRow_26.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_14 :
    majCellCheck 26 14 (majRow_26.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_15 :
    majCellCheck 26 15 (majRow_26.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_16 :
    majCellCheck 26 16 (majRow_26.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_17 :
    majCellCheck 26 17 (majRow_26.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_18 :
    majCellCheck 26 18 (majRow_26.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_19 :
    majCellCheck 26 19 (majRow_26.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_20 :
    majCellCheck 26 20 (majRow_26.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_21 :
    majCellCheck 26 21 (majRow_26.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_22 :
    majCellCheck 26 22 (majRow_26.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_23 :
    majCellCheck 26 23 (majRow_26.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_24 :
    majCellCheck 26 24 (majRow_26.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_25 :
    majCellCheck 26 25 (majRow_26.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_cell_26 :
    majCellCheck 26 26 (majRow_26.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_26_all : ∀ l, l ≤ 26 →
    majCellCheck 26 l (majRow_26.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_26_cell_0, majRow_26_cell_1, majRow_26_cell_2, majRow_26_cell_3, majRow_26_cell_4, majRow_26_cell_5, majRow_26_cell_6, majRow_26_cell_7, majRow_26_cell_8, majRow_26_cell_9, majRow_26_cell_10, majRow_26_cell_11, majRow_26_cell_12, majRow_26_cell_13, majRow_26_cell_14, majRow_26_cell_15, majRow_26_cell_16, majRow_26_cell_17, majRow_26_cell_18, majRow_26_cell_19, majRow_26_cell_20, majRow_26_cell_21, majRow_26_cell_22, majRow_26_cell_23, majRow_26_cell_24, majRow_26_cell_25, majRow_26_cell_26]

def majRow_27 : List (MajTree × MajTree) := [
  ((.leaf 28), (.leaf 29)),
  ((.leaf 29), (.leaf 30)),
  ((.leaf 30), (.leaf 31)),
  ((.leaf 31), (.leaf 32)),
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
  ((.node (.leaf 52) (.leaf 52) (.leaf 52) (.leaf 52)), (.leaf 152)),
  ((.leaf 53), (.leaf 0)),
  ((.leaf 0), (.leaf 0)),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_27_cell_0 :
    majCellCheck 27 0 (majRow_27.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_1 :
    majCellCheck 27 1 (majRow_27.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_2 :
    majCellCheck 27 2 (majRow_27.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_3 :
    majCellCheck 27 3 (majRow_27.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_4 :
    majCellCheck 27 4 (majRow_27.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_5 :
    majCellCheck 27 5 (majRow_27.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_6 :
    majCellCheck 27 6 (majRow_27.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_7 :
    majCellCheck 27 7 (majRow_27.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_8 :
    majCellCheck 27 8 (majRow_27.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_9 :
    majCellCheck 27 9 (majRow_27.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_10 :
    majCellCheck 27 10 (majRow_27.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_11 :
    majCellCheck 27 11 (majRow_27.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_12 :
    majCellCheck 27 12 (majRow_27.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_13 :
    majCellCheck 27 13 (majRow_27.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_14 :
    majCellCheck 27 14 (majRow_27.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_15 :
    majCellCheck 27 15 (majRow_27.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_16 :
    majCellCheck 27 16 (majRow_27.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_17 :
    majCellCheck 27 17 (majRow_27.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_18 :
    majCellCheck 27 18 (majRow_27.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_19 :
    majCellCheck 27 19 (majRow_27.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_20 :
    majCellCheck 27 20 (majRow_27.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_21 :
    majCellCheck 27 21 (majRow_27.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_22 :
    majCellCheck 27 22 (majRow_27.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_23 :
    majCellCheck 27 23 (majRow_27.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_24 :
    majCellCheck 27 24 (majRow_27.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_25 :
    majCellCheck 27 25 (majRow_27.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_26 :
    majCellCheck 27 26 (majRow_27.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_cell_27 :
    majCellCheck 27 27 (majRow_27.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_27_all : ∀ l, l ≤ 27 →
    majCellCheck 27 l (majRow_27.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_27_cell_0, majRow_27_cell_1, majRow_27_cell_2, majRow_27_cell_3, majRow_27_cell_4, majRow_27_cell_5, majRow_27_cell_6, majRow_27_cell_7, majRow_27_cell_8, majRow_27_cell_9, majRow_27_cell_10, majRow_27_cell_11, majRow_27_cell_12, majRow_27_cell_13, majRow_27_cell_14, majRow_27_cell_15, majRow_27_cell_16, majRow_27_cell_17, majRow_27_cell_18, majRow_27_cell_19, majRow_27_cell_20, majRow_27_cell_21, majRow_27_cell_22, majRow_27_cell_23, majRow_27_cell_24, majRow_27_cell_25, majRow_27_cell_26, majRow_27_cell_27]

def majRow_28 : List (MajTree × MajTree) := [
  ((.leaf 29), (.leaf 30)),
  ((.leaf 30), (.leaf 31)),
  ((.leaf 31), (.leaf 32)),
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
  ((.leaf 0), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_28_cell_0 :
    majCellCheck 28 0 (majRow_28.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_1 :
    majCellCheck 28 1 (majRow_28.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_2 :
    majCellCheck 28 2 (majRow_28.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_3 :
    majCellCheck 28 3 (majRow_28.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_4 :
    majCellCheck 28 4 (majRow_28.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_5 :
    majCellCheck 28 5 (majRow_28.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_6 :
    majCellCheck 28 6 (majRow_28.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_7 :
    majCellCheck 28 7 (majRow_28.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_8 :
    majCellCheck 28 8 (majRow_28.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_9 :
    majCellCheck 28 9 (majRow_28.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_10 :
    majCellCheck 28 10 (majRow_28.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_11 :
    majCellCheck 28 11 (majRow_28.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_12 :
    majCellCheck 28 12 (majRow_28.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_13 :
    majCellCheck 28 13 (majRow_28.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_14 :
    majCellCheck 28 14 (majRow_28.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_15 :
    majCellCheck 28 15 (majRow_28.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_16 :
    majCellCheck 28 16 (majRow_28.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_17 :
    majCellCheck 28 17 (majRow_28.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_18 :
    majCellCheck 28 18 (majRow_28.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_19 :
    majCellCheck 28 19 (majRow_28.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_20 :
    majCellCheck 28 20 (majRow_28.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_21 :
    majCellCheck 28 21 (majRow_28.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_22 :
    majCellCheck 28 22 (majRow_28.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_23 :
    majCellCheck 28 23 (majRow_28.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_24 :
    majCellCheck 28 24 (majRow_28.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_25 :
    majCellCheck 28 25 (majRow_28.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_26 :
    majCellCheck 28 26 (majRow_28.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_27 :
    majCellCheck 28 27 (majRow_28.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_cell_28 :
    majCellCheck 28 28 (majRow_28.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_28_all : ∀ l, l ≤ 28 →
    majCellCheck 28 l (majRow_28.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_28_cell_0, majRow_28_cell_1, majRow_28_cell_2, majRow_28_cell_3, majRow_28_cell_4, majRow_28_cell_5, majRow_28_cell_6, majRow_28_cell_7, majRow_28_cell_8, majRow_28_cell_9, majRow_28_cell_10, majRow_28_cell_11, majRow_28_cell_12, majRow_28_cell_13, majRow_28_cell_14, majRow_28_cell_15, majRow_28_cell_16, majRow_28_cell_17, majRow_28_cell_18, majRow_28_cell_19, majRow_28_cell_20, majRow_28_cell_21, majRow_28_cell_22, majRow_28_cell_23, majRow_28_cell_24, majRow_28_cell_25, majRow_28_cell_26, majRow_28_cell_27, majRow_28_cell_28]

def majRow_29 : List (MajTree × MajTree) := [
  ((.leaf 30), (.leaf 31)),
  ((.leaf 31), (.leaf 32)),
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
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_29_cell_0 :
    majCellCheck 29 0 (majRow_29.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_1 :
    majCellCheck 29 1 (majRow_29.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_2 :
    majCellCheck 29 2 (majRow_29.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_3 :
    majCellCheck 29 3 (majRow_29.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_4 :
    majCellCheck 29 4 (majRow_29.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_5 :
    majCellCheck 29 5 (majRow_29.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_6 :
    majCellCheck 29 6 (majRow_29.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_7 :
    majCellCheck 29 7 (majRow_29.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_8 :
    majCellCheck 29 8 (majRow_29.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_9 :
    majCellCheck 29 9 (majRow_29.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_10 :
    majCellCheck 29 10 (majRow_29.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_11 :
    majCellCheck 29 11 (majRow_29.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_12 :
    majCellCheck 29 12 (majRow_29.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_13 :
    majCellCheck 29 13 (majRow_29.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_14 :
    majCellCheck 29 14 (majRow_29.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_15 :
    majCellCheck 29 15 (majRow_29.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_16 :
    majCellCheck 29 16 (majRow_29.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_17 :
    majCellCheck 29 17 (majRow_29.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_18 :
    majCellCheck 29 18 (majRow_29.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_19 :
    majCellCheck 29 19 (majRow_29.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_20 :
    majCellCheck 29 20 (majRow_29.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_21 :
    majCellCheck 29 21 (majRow_29.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_22 :
    majCellCheck 29 22 (majRow_29.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_23 :
    majCellCheck 29 23 (majRow_29.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_24 :
    majCellCheck 29 24 (majRow_29.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_25 :
    majCellCheck 29 25 (majRow_29.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_26 :
    majCellCheck 29 26 (majRow_29.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_27 :
    majCellCheck 29 27 (majRow_29.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_28 :
    majCellCheck 29 28 (majRow_29.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_cell_29 :
    majCellCheck 29 29 (majRow_29.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_29_all : ∀ l, l ≤ 29 →
    majCellCheck 29 l (majRow_29.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_29_cell_0, majRow_29_cell_1, majRow_29_cell_2, majRow_29_cell_3, majRow_29_cell_4, majRow_29_cell_5, majRow_29_cell_6, majRow_29_cell_7, majRow_29_cell_8, majRow_29_cell_9, majRow_29_cell_10, majRow_29_cell_11, majRow_29_cell_12, majRow_29_cell_13, majRow_29_cell_14, majRow_29_cell_15, majRow_29_cell_16, majRow_29_cell_17, majRow_29_cell_18, majRow_29_cell_19, majRow_29_cell_20, majRow_29_cell_21, majRow_29_cell_22, majRow_29_cell_23, majRow_29_cell_24, majRow_29_cell_25, majRow_29_cell_26, majRow_29_cell_27, majRow_29_cell_28, majRow_29_cell_29]

def majRow_30 : List (MajTree × MajTree) := [
  ((.leaf 31), (.leaf 32)),
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
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0)),
  ((.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)), (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))),
  ((.leaf 0), (.leaf 0))
]

theorem majRow_30_cell_0 :
    majCellCheck 30 0 (majRow_30.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_1 :
    majCellCheck 30 1 (majRow_30.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_2 :
    majCellCheck 30 2 (majRow_30.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_3 :
    majCellCheck 30 3 (majRow_30.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_4 :
    majCellCheck 30 4 (majRow_30.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_5 :
    majCellCheck 30 5 (majRow_30.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_6 :
    majCellCheck 30 6 (majRow_30.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_7 :
    majCellCheck 30 7 (majRow_30.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_8 :
    majCellCheck 30 8 (majRow_30.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_9 :
    majCellCheck 30 9 (majRow_30.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_10 :
    majCellCheck 30 10 (majRow_30.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_11 :
    majCellCheck 30 11 (majRow_30.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_12 :
    majCellCheck 30 12 (majRow_30.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_13 :
    majCellCheck 30 13 (majRow_30.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_14 :
    majCellCheck 30 14 (majRow_30.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_15 :
    majCellCheck 30 15 (majRow_30.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_16 :
    majCellCheck 30 16 (majRow_30.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_17 :
    majCellCheck 30 17 (majRow_30.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_18 :
    majCellCheck 30 18 (majRow_30.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_19 :
    majCellCheck 30 19 (majRow_30.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_20 :
    majCellCheck 30 20 (majRow_30.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_21 :
    majCellCheck 30 21 (majRow_30.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_22 :
    majCellCheck 30 22 (majRow_30.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_23 :
    majCellCheck 30 23 (majRow_30.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_24 :
    majCellCheck 30 24 (majRow_30.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_25 :
    majCellCheck 30 25 (majRow_30.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_26 :
    majCellCheck 30 26 (majRow_30.getD 26 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_27 :
    majCellCheck 30 27 (majRow_30.getD 27 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_28 :
    majCellCheck 30 28 (majRow_30.getD 28 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_29 :
    majCellCheck 30 29 (majRow_30.getD 29 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_cell_30 :
    majCellCheck 30 30 (majRow_30.getD 30 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_30_all : ∀ l, l ≤ 30 →
    majCellCheck 30 l (majRow_30.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_30_cell_0, majRow_30_cell_1, majRow_30_cell_2, majRow_30_cell_3, majRow_30_cell_4, majRow_30_cell_5, majRow_30_cell_6, majRow_30_cell_7, majRow_30_cell_8, majRow_30_cell_9, majRow_30_cell_10, majRow_30_cell_11, majRow_30_cell_12, majRow_30_cell_13, majRow_30_cell_14, majRow_30_cell_15, majRow_30_cell_16, majRow_30_cell_17, majRow_30_cell_18, majRow_30_cell_19, majRow_30_cell_20, majRow_30_cell_21, majRow_30_cell_22, majRow_30_cell_23, majRow_30_cell_24, majRow_30_cell_25, majRow_30_cell_26, majRow_30_cell_27, majRow_30_cell_28, majRow_30_cell_29, majRow_30_cell_30]

end PartialBalayage.Maximal.Square
