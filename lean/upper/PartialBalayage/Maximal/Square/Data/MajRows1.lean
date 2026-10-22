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

def majRow_19 : List (MajTree × MajTree) := [
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.leaf 39), (.leaf 40))
]

theorem majRow_19_cell_0 :
    majCellCheck 19 0 (majRow_19.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_1 :
    majCellCheck 19 1 (majRow_19.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_2 :
    majCellCheck 19 2 (majRow_19.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_3 :
    majCellCheck 19 3 (majRow_19.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_4 :
    majCellCheck 19 4 (majRow_19.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_5 :
    majCellCheck 19 5 (majRow_19.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_6 :
    majCellCheck 19 6 (majRow_19.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_7 :
    majCellCheck 19 7 (majRow_19.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_8 :
    majCellCheck 19 8 (majRow_19.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_9 :
    majCellCheck 19 9 (majRow_19.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_10 :
    majCellCheck 19 10 (majRow_19.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_11 :
    majCellCheck 19 11 (majRow_19.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_12 :
    majCellCheck 19 12 (majRow_19.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_13 :
    majCellCheck 19 13 (majRow_19.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_14 :
    majCellCheck 19 14 (majRow_19.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_15 :
    majCellCheck 19 15 (majRow_19.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_16 :
    majCellCheck 19 16 (majRow_19.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_17 :
    majCellCheck 19 17 (majRow_19.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_18 :
    majCellCheck 19 18 (majRow_19.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_cell_19 :
    majCellCheck 19 19 (majRow_19.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_19_all : ∀ l, l ≤ 19 →
    majCellCheck 19 l (majRow_19.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_19_cell_0, majRow_19_cell_1, majRow_19_cell_2, majRow_19_cell_3, majRow_19_cell_4, majRow_19_cell_5, majRow_19_cell_6, majRow_19_cell_7, majRow_19_cell_8, majRow_19_cell_9, majRow_19_cell_10, majRow_19_cell_11, majRow_19_cell_12, majRow_19_cell_13, majRow_19_cell_14, majRow_19_cell_15, majRow_19_cell_16, majRow_19_cell_17, majRow_19_cell_18, majRow_19_cell_19]

def majRow_20 : List (MajTree × MajTree) := [
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.leaf 41), (.leaf 42))
]

theorem majRow_20_cell_0 :
    majCellCheck 20 0 (majRow_20.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_1 :
    majCellCheck 20 1 (majRow_20.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_2 :
    majCellCheck 20 2 (majRow_20.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_3 :
    majCellCheck 20 3 (majRow_20.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_4 :
    majCellCheck 20 4 (majRow_20.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_5 :
    majCellCheck 20 5 (majRow_20.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_6 :
    majCellCheck 20 6 (majRow_20.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_7 :
    majCellCheck 20 7 (majRow_20.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_8 :
    majCellCheck 20 8 (majRow_20.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_9 :
    majCellCheck 20 9 (majRow_20.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_10 :
    majCellCheck 20 10 (majRow_20.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_11 :
    majCellCheck 20 11 (majRow_20.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_12 :
    majCellCheck 20 12 (majRow_20.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_13 :
    majCellCheck 20 13 (majRow_20.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_14 :
    majCellCheck 20 14 (majRow_20.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_15 :
    majCellCheck 20 15 (majRow_20.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_16 :
    majCellCheck 20 16 (majRow_20.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_17 :
    majCellCheck 20 17 (majRow_20.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_18 :
    majCellCheck 20 18 (majRow_20.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_19 :
    majCellCheck 20 19 (majRow_20.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_cell_20 :
    majCellCheck 20 20 (majRow_20.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_20_all : ∀ l, l ≤ 20 →
    majCellCheck 20 l (majRow_20.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_20_cell_0, majRow_20_cell_1, majRow_20_cell_2, majRow_20_cell_3, majRow_20_cell_4, majRow_20_cell_5, majRow_20_cell_6, majRow_20_cell_7, majRow_20_cell_8, majRow_20_cell_9, majRow_20_cell_10, majRow_20_cell_11, majRow_20_cell_12, majRow_20_cell_13, majRow_20_cell_14, majRow_20_cell_15, majRow_20_cell_16, majRow_20_cell_17, majRow_20_cell_18, majRow_20_cell_19, majRow_20_cell_20]

def majRow_21 : List (MajTree × MajTree) := [
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.leaf 43), (.leaf 44))
]

theorem majRow_21_cell_0 :
    majCellCheck 21 0 (majRow_21.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_1 :
    majCellCheck 21 1 (majRow_21.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_2 :
    majCellCheck 21 2 (majRow_21.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_3 :
    majCellCheck 21 3 (majRow_21.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_4 :
    majCellCheck 21 4 (majRow_21.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_5 :
    majCellCheck 21 5 (majRow_21.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_6 :
    majCellCheck 21 6 (majRow_21.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_7 :
    majCellCheck 21 7 (majRow_21.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_8 :
    majCellCheck 21 8 (majRow_21.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_9 :
    majCellCheck 21 9 (majRow_21.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_10 :
    majCellCheck 21 10 (majRow_21.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_11 :
    majCellCheck 21 11 (majRow_21.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_12 :
    majCellCheck 21 12 (majRow_21.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_13 :
    majCellCheck 21 13 (majRow_21.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_14 :
    majCellCheck 21 14 (majRow_21.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_15 :
    majCellCheck 21 15 (majRow_21.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_16 :
    majCellCheck 21 16 (majRow_21.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_17 :
    majCellCheck 21 17 (majRow_21.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_18 :
    majCellCheck 21 18 (majRow_21.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_19 :
    majCellCheck 21 19 (majRow_21.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_20 :
    majCellCheck 21 20 (majRow_21.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_cell_21 :
    majCellCheck 21 21 (majRow_21.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_21_all : ∀ l, l ≤ 21 →
    majCellCheck 21 l (majRow_21.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_21_cell_0, majRow_21_cell_1, majRow_21_cell_2, majRow_21_cell_3, majRow_21_cell_4, majRow_21_cell_5, majRow_21_cell_6, majRow_21_cell_7, majRow_21_cell_8, majRow_21_cell_9, majRow_21_cell_10, majRow_21_cell_11, majRow_21_cell_12, majRow_21_cell_13, majRow_21_cell_14, majRow_21_cell_15, majRow_21_cell_16, majRow_21_cell_17, majRow_21_cell_18, majRow_21_cell_19, majRow_21_cell_20, majRow_21_cell_21]

def majRow_22 : List (MajTree × MajTree) := [
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.node (.leaf 45) (.leaf 45) (.leaf 45) (.leaf 45)), (.node (.leaf 46) (.leaf 46) (.leaf 46) (.leaf 46)))
]

theorem majRow_22_cell_0 :
    majCellCheck 22 0 (majRow_22.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_1 :
    majCellCheck 22 1 (majRow_22.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_2 :
    majCellCheck 22 2 (majRow_22.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_3 :
    majCellCheck 22 3 (majRow_22.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_4 :
    majCellCheck 22 4 (majRow_22.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_5 :
    majCellCheck 22 5 (majRow_22.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_6 :
    majCellCheck 22 6 (majRow_22.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_7 :
    majCellCheck 22 7 (majRow_22.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_8 :
    majCellCheck 22 8 (majRow_22.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_9 :
    majCellCheck 22 9 (majRow_22.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_10 :
    majCellCheck 22 10 (majRow_22.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_11 :
    majCellCheck 22 11 (majRow_22.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_12 :
    majCellCheck 22 12 (majRow_22.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_13 :
    majCellCheck 22 13 (majRow_22.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_14 :
    majCellCheck 22 14 (majRow_22.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_15 :
    majCellCheck 22 15 (majRow_22.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_16 :
    majCellCheck 22 16 (majRow_22.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_17 :
    majCellCheck 22 17 (majRow_22.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_18 :
    majCellCheck 22 18 (majRow_22.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_19 :
    majCellCheck 22 19 (majRow_22.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_20 :
    majCellCheck 22 20 (majRow_22.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_21 :
    majCellCheck 22 21 (majRow_22.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_cell_22 :
    majCellCheck 22 22 (majRow_22.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_22_all : ∀ l, l ≤ 22 →
    majCellCheck 22 l (majRow_22.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_22_cell_0, majRow_22_cell_1, majRow_22_cell_2, majRow_22_cell_3, majRow_22_cell_4, majRow_22_cell_5, majRow_22_cell_6, majRow_22_cell_7, majRow_22_cell_8, majRow_22_cell_9, majRow_22_cell_10, majRow_22_cell_11, majRow_22_cell_12, majRow_22_cell_13, majRow_22_cell_14, majRow_22_cell_15, majRow_22_cell_16, majRow_22_cell_17, majRow_22_cell_18, majRow_22_cell_19, majRow_22_cell_20, majRow_22_cell_21, majRow_22_cell_22]

def majRow_23 : List (MajTree × MajTree) := [
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.node (.leaf 47) (.leaf 47) (.leaf 47) (.node (.leaf 47) (.node (.leaf 47) (.node (.leaf 47) (.node (.leaf 47) (.leaf 47) (.leaf 47) (.leaf 47)) (.leaf 47) (.leaf 47)) (.leaf 47) (.leaf 47)) (.leaf 47) (.leaf 47))), (.node (.leaf 48) (.leaf 147) (.leaf 147) (.node (.leaf 48) (.node (.leaf 147) (.node (.leaf 147) (.node (.leaf 147) (.leaf 147) (.leaf 147) (.leaf 147)) (.leaf 147) (.leaf 147)) (.leaf 147) (.leaf 147)) (.leaf 48) (.leaf 48))))
]

theorem majRow_23_cell_0 :
    majCellCheck 23 0 (majRow_23.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_1 :
    majCellCheck 23 1 (majRow_23.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_2 :
    majCellCheck 23 2 (majRow_23.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_3 :
    majCellCheck 23 3 (majRow_23.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_4 :
    majCellCheck 23 4 (majRow_23.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_5 :
    majCellCheck 23 5 (majRow_23.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_6 :
    majCellCheck 23 6 (majRow_23.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_7 :
    majCellCheck 23 7 (majRow_23.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_8 :
    majCellCheck 23 8 (majRow_23.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_9 :
    majCellCheck 23 9 (majRow_23.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_10 :
    majCellCheck 23 10 (majRow_23.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_11 :
    majCellCheck 23 11 (majRow_23.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_12 :
    majCellCheck 23 12 (majRow_23.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_13 :
    majCellCheck 23 13 (majRow_23.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_14 :
    majCellCheck 23 14 (majRow_23.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_15 :
    majCellCheck 23 15 (majRow_23.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_16 :
    majCellCheck 23 16 (majRow_23.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_17 :
    majCellCheck 23 17 (majRow_23.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_18 :
    majCellCheck 23 18 (majRow_23.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_19 :
    majCellCheck 23 19 (majRow_23.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_20 :
    majCellCheck 23 20 (majRow_23.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_21 :
    majCellCheck 23 21 (majRow_23.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_22 :
    majCellCheck 23 22 (majRow_23.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_cell_23 :
    majCellCheck 23 23 (majRow_23.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_23_all : ∀ l, l ≤ 23 →
    majCellCheck 23 l (majRow_23.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_23_cell_0, majRow_23_cell_1, majRow_23_cell_2, majRow_23_cell_3, majRow_23_cell_4, majRow_23_cell_5, majRow_23_cell_6, majRow_23_cell_7, majRow_23_cell_8, majRow_23_cell_9, majRow_23_cell_10, majRow_23_cell_11, majRow_23_cell_12, majRow_23_cell_13, majRow_23_cell_14, majRow_23_cell_15, majRow_23_cell_16, majRow_23_cell_17, majRow_23_cell_18, majRow_23_cell_19, majRow_23_cell_20, majRow_23_cell_21, majRow_23_cell_22, majRow_23_cell_23]

def majRow_24 : List (MajTree × MajTree) := [
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
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
  ((.node (.leaf 48) (.leaf 48) (.leaf 48) (.leaf 48)), (.node (.leaf 49) (.leaf 49) (.leaf 49) (.leaf 49))),
  ((.leaf 49), (.leaf 50))
]

theorem majRow_24_cell_0 :
    majCellCheck 24 0 (majRow_24.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_1 :
    majCellCheck 24 1 (majRow_24.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_2 :
    majCellCheck 24 2 (majRow_24.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_3 :
    majCellCheck 24 3 (majRow_24.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_4 :
    majCellCheck 24 4 (majRow_24.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_5 :
    majCellCheck 24 5 (majRow_24.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_6 :
    majCellCheck 24 6 (majRow_24.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_7 :
    majCellCheck 24 7 (majRow_24.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_8 :
    majCellCheck 24 8 (majRow_24.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_9 :
    majCellCheck 24 9 (majRow_24.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_10 :
    majCellCheck 24 10 (majRow_24.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_11 :
    majCellCheck 24 11 (majRow_24.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_12 :
    majCellCheck 24 12 (majRow_24.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_13 :
    majCellCheck 24 13 (majRow_24.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_14 :
    majCellCheck 24 14 (majRow_24.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_15 :
    majCellCheck 24 15 (majRow_24.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_16 :
    majCellCheck 24 16 (majRow_24.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_17 :
    majCellCheck 24 17 (majRow_24.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_18 :
    majCellCheck 24 18 (majRow_24.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_19 :
    majCellCheck 24 19 (majRow_24.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_20 :
    majCellCheck 24 20 (majRow_24.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_21 :
    majCellCheck 24 21 (majRow_24.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_22 :
    majCellCheck 24 22 (majRow_24.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_23 :
    majCellCheck 24 23 (majRow_24.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_cell_24 :
    majCellCheck 24 24 (majRow_24.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_24_all : ∀ l, l ≤ 24 →
    majCellCheck 24 l (majRow_24.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_24_cell_0, majRow_24_cell_1, majRow_24_cell_2, majRow_24_cell_3, majRow_24_cell_4, majRow_24_cell_5, majRow_24_cell_6, majRow_24_cell_7, majRow_24_cell_8, majRow_24_cell_9, majRow_24_cell_10, majRow_24_cell_11, majRow_24_cell_12, majRow_24_cell_13, majRow_24_cell_14, majRow_24_cell_15, majRow_24_cell_16, majRow_24_cell_17, majRow_24_cell_18, majRow_24_cell_19, majRow_24_cell_20, majRow_24_cell_21, majRow_24_cell_22, majRow_24_cell_23, majRow_24_cell_24]

def majRow_25 : List (MajTree × MajTree) := [
  ((.leaf 26), (.leaf 27)),
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
  ((.node (.leaf 50) (.leaf 50) (.leaf 50) (.leaf 50)), (.node (.leaf 51) (.leaf 150) (.leaf 150) (.leaf 150))),
  ((.leaf 51), (.node (.leaf 52) (.leaf 52) (.leaf 52) (.leaf 52)))
]

theorem majRow_25_cell_0 :
    majCellCheck 25 0 (majRow_25.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_1 :
    majCellCheck 25 1 (majRow_25.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_2 :
    majCellCheck 25 2 (majRow_25.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_3 :
    majCellCheck 25 3 (majRow_25.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_4 :
    majCellCheck 25 4 (majRow_25.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_5 :
    majCellCheck 25 5 (majRow_25.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_6 :
    majCellCheck 25 6 (majRow_25.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_7 :
    majCellCheck 25 7 (majRow_25.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_8 :
    majCellCheck 25 8 (majRow_25.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_9 :
    majCellCheck 25 9 (majRow_25.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_10 :
    majCellCheck 25 10 (majRow_25.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_11 :
    majCellCheck 25 11 (majRow_25.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_12 :
    majCellCheck 25 12 (majRow_25.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_13 :
    majCellCheck 25 13 (majRow_25.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_14 :
    majCellCheck 25 14 (majRow_25.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_15 :
    majCellCheck 25 15 (majRow_25.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_16 :
    majCellCheck 25 16 (majRow_25.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_17 :
    majCellCheck 25 17 (majRow_25.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_18 :
    majCellCheck 25 18 (majRow_25.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_19 :
    majCellCheck 25 19 (majRow_25.getD 19 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_20 :
    majCellCheck 25 20 (majRow_25.getD 20 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_21 :
    majCellCheck 25 21 (majRow_25.getD 21 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_22 :
    majCellCheck 25 22 (majRow_25.getD 22 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_23 :
    majCellCheck 25 23 (majRow_25.getD 23 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_24 :
    majCellCheck 25 24 (majRow_25.getD 24 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_cell_25 :
    majCellCheck 25 25 (majRow_25.getD 25 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_25_all : ∀ l, l ≤ 25 →
    majCellCheck 25 l (majRow_25.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_25_cell_0, majRow_25_cell_1, majRow_25_cell_2, majRow_25_cell_3, majRow_25_cell_4, majRow_25_cell_5, majRow_25_cell_6, majRow_25_cell_7, majRow_25_cell_8, majRow_25_cell_9, majRow_25_cell_10, majRow_25_cell_11, majRow_25_cell_12, majRow_25_cell_13, majRow_25_cell_14, majRow_25_cell_15, majRow_25_cell_16, majRow_25_cell_17, majRow_25_cell_18, majRow_25_cell_19, majRow_25_cell_20, majRow_25_cell_21, majRow_25_cell_22, majRow_25_cell_23, majRow_25_cell_24, majRow_25_cell_25]

end PartialBalayage.Maximal.Square
