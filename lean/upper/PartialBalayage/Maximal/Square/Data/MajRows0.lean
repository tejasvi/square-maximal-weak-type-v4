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

def majRow_0 : List (MajTree × MajTree) := [
  ((.leaf 1), (.leaf 2))
]

theorem majRow_0_cell_0 :
    majCellCheck 0 0 (majRow_0.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_0_all : ∀ l, l ≤ 0 →
    majCellCheck 0 l (majRow_0.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_0_cell_0]

def majRow_1 : List (MajTree × MajTree) := [
  ((.leaf 2), (.leaf 3)),
  ((.leaf 3), (.leaf 4))
]

theorem majRow_1_cell_0 :
    majCellCheck 1 0 (majRow_1.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_1_cell_1 :
    majCellCheck 1 1 (majRow_1.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_1_all : ∀ l, l ≤ 1 →
    majCellCheck 1 l (majRow_1.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_1_cell_0, majRow_1_cell_1]

def majRow_2 : List (MajTree × MajTree) := [
  ((.leaf 3), (.leaf 4)),
  ((.leaf 4), (.leaf 5)),
  ((.leaf 5), (.leaf 6))
]

theorem majRow_2_cell_0 :
    majCellCheck 2 0 (majRow_2.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_2_cell_1 :
    majCellCheck 2 1 (majRow_2.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_2_cell_2 :
    majCellCheck 2 2 (majRow_2.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_2_all : ∀ l, l ≤ 2 →
    majCellCheck 2 l (majRow_2.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_2_cell_0, majRow_2_cell_1, majRow_2_cell_2]

def majRow_3 : List (MajTree × MajTree) := [
  ((.leaf 4), (.leaf 5)),
  ((.leaf 5), (.leaf 6)),
  ((.leaf 6), (.leaf 7)),
  ((.leaf 7), (.leaf 8))
]

theorem majRow_3_cell_0 :
    majCellCheck 3 0 (majRow_3.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_3_cell_1 :
    majCellCheck 3 1 (majRow_3.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_3_cell_2 :
    majCellCheck 3 2 (majRow_3.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_3_cell_3 :
    majCellCheck 3 3 (majRow_3.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_3_all : ∀ l, l ≤ 3 →
    majCellCheck 3 l (majRow_3.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_3_cell_0, majRow_3_cell_1, majRow_3_cell_2, majRow_3_cell_3]

def majRow_4 : List (MajTree × MajTree) := [
  ((.leaf 5), (.leaf 6)),
  ((.leaf 6), (.leaf 7)),
  ((.leaf 7), (.leaf 8)),
  ((.leaf 8), (.leaf 9)),
  ((.leaf 9), (.leaf 10))
]

theorem majRow_4_cell_0 :
    majCellCheck 4 0 (majRow_4.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_4_cell_1 :
    majCellCheck 4 1 (majRow_4.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_4_cell_2 :
    majCellCheck 4 2 (majRow_4.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_4_cell_3 :
    majCellCheck 4 3 (majRow_4.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_4_cell_4 :
    majCellCheck 4 4 (majRow_4.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_4_all : ∀ l, l ≤ 4 →
    majCellCheck 4 l (majRow_4.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_4_cell_0, majRow_4_cell_1, majRow_4_cell_2, majRow_4_cell_3, majRow_4_cell_4]

def majRow_5 : List (MajTree × MajTree) := [
  ((.leaf 6), (.leaf 7)),
  ((.leaf 7), (.leaf 8)),
  ((.leaf 8), (.leaf 9)),
  ((.leaf 9), (.leaf 10)),
  ((.leaf 10), (.leaf 11)),
  ((.leaf 11), (.leaf 12))
]

theorem majRow_5_cell_0 :
    majCellCheck 5 0 (majRow_5.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_cell_1 :
    majCellCheck 5 1 (majRow_5.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_cell_2 :
    majCellCheck 5 2 (majRow_5.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_cell_3 :
    majCellCheck 5 3 (majRow_5.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_cell_4 :
    majCellCheck 5 4 (majRow_5.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_cell_5 :
    majCellCheck 5 5 (majRow_5.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_5_all : ∀ l, l ≤ 5 →
    majCellCheck 5 l (majRow_5.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_5_cell_0, majRow_5_cell_1, majRow_5_cell_2, majRow_5_cell_3, majRow_5_cell_4, majRow_5_cell_5]

def majRow_6 : List (MajTree × MajTree) := [
  ((.leaf 7), (.leaf 8)),
  ((.leaf 8), (.leaf 9)),
  ((.leaf 9), (.leaf 10)),
  ((.leaf 10), (.leaf 11)),
  ((.leaf 11), (.leaf 12)),
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14))
]

theorem majRow_6_cell_0 :
    majCellCheck 6 0 (majRow_6.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_1 :
    majCellCheck 6 1 (majRow_6.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_2 :
    majCellCheck 6 2 (majRow_6.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_3 :
    majCellCheck 6 3 (majRow_6.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_4 :
    majCellCheck 6 4 (majRow_6.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_5 :
    majCellCheck 6 5 (majRow_6.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_cell_6 :
    majCellCheck 6 6 (majRow_6.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_6_all : ∀ l, l ≤ 6 →
    majCellCheck 6 l (majRow_6.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_6_cell_0, majRow_6_cell_1, majRow_6_cell_2, majRow_6_cell_3, majRow_6_cell_4, majRow_6_cell_5, majRow_6_cell_6]

def majRow_7 : List (MajTree × MajTree) := [
  ((.leaf 8), (.leaf 9)),
  ((.leaf 9), (.leaf 10)),
  ((.leaf 10), (.leaf 11)),
  ((.leaf 11), (.leaf 12)),
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16))
]

theorem majRow_7_cell_0 :
    majCellCheck 7 0 (majRow_7.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_1 :
    majCellCheck 7 1 (majRow_7.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_2 :
    majCellCheck 7 2 (majRow_7.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_3 :
    majCellCheck 7 3 (majRow_7.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_4 :
    majCellCheck 7 4 (majRow_7.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_5 :
    majCellCheck 7 5 (majRow_7.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_6 :
    majCellCheck 7 6 (majRow_7.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_cell_7 :
    majCellCheck 7 7 (majRow_7.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_7_all : ∀ l, l ≤ 7 →
    majCellCheck 7 l (majRow_7.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_7_cell_0, majRow_7_cell_1, majRow_7_cell_2, majRow_7_cell_3, majRow_7_cell_4, majRow_7_cell_5, majRow_7_cell_6, majRow_7_cell_7]

def majRow_8 : List (MajTree × MajTree) := [
  ((.leaf 9), (.leaf 10)),
  ((.leaf 10), (.leaf 11)),
  ((.leaf 11), (.leaf 12)),
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18))
]

theorem majRow_8_cell_0 :
    majCellCheck 8 0 (majRow_8.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_1 :
    majCellCheck 8 1 (majRow_8.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_2 :
    majCellCheck 8 2 (majRow_8.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_3 :
    majCellCheck 8 3 (majRow_8.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_4 :
    majCellCheck 8 4 (majRow_8.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_5 :
    majCellCheck 8 5 (majRow_8.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_6 :
    majCellCheck 8 6 (majRow_8.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_7 :
    majCellCheck 8 7 (majRow_8.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_cell_8 :
    majCellCheck 8 8 (majRow_8.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_8_all : ∀ l, l ≤ 8 →
    majCellCheck 8 l (majRow_8.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_8_cell_0, majRow_8_cell_1, majRow_8_cell_2, majRow_8_cell_3, majRow_8_cell_4, majRow_8_cell_5, majRow_8_cell_6, majRow_8_cell_7, majRow_8_cell_8]

def majRow_9 : List (MajTree × MajTree) := [
  ((.leaf 10), (.leaf 11)),
  ((.leaf 11), (.leaf 12)),
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20))
]

theorem majRow_9_cell_0 :
    majCellCheck 9 0 (majRow_9.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_1 :
    majCellCheck 9 1 (majRow_9.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_2 :
    majCellCheck 9 2 (majRow_9.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_3 :
    majCellCheck 9 3 (majRow_9.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_4 :
    majCellCheck 9 4 (majRow_9.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_5 :
    majCellCheck 9 5 (majRow_9.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_6 :
    majCellCheck 9 6 (majRow_9.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_7 :
    majCellCheck 9 7 (majRow_9.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_8 :
    majCellCheck 9 8 (majRow_9.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_cell_9 :
    majCellCheck 9 9 (majRow_9.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_9_all : ∀ l, l ≤ 9 →
    majCellCheck 9 l (majRow_9.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_9_cell_0, majRow_9_cell_1, majRow_9_cell_2, majRow_9_cell_3, majRow_9_cell_4, majRow_9_cell_5, majRow_9_cell_6, majRow_9_cell_7, majRow_9_cell_8, majRow_9_cell_9]

def majRow_10 : List (MajTree × MajTree) := [
  ((.leaf 11), (.leaf 12)),
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22))
]

theorem majRow_10_cell_0 :
    majCellCheck 10 0 (majRow_10.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_1 :
    majCellCheck 10 1 (majRow_10.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_2 :
    majCellCheck 10 2 (majRow_10.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_3 :
    majCellCheck 10 3 (majRow_10.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_4 :
    majCellCheck 10 4 (majRow_10.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_5 :
    majCellCheck 10 5 (majRow_10.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_6 :
    majCellCheck 10 6 (majRow_10.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_7 :
    majCellCheck 10 7 (majRow_10.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_8 :
    majCellCheck 10 8 (majRow_10.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_9 :
    majCellCheck 10 9 (majRow_10.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_cell_10 :
    majCellCheck 10 10 (majRow_10.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_10_all : ∀ l, l ≤ 10 →
    majCellCheck 10 l (majRow_10.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_10_cell_0, majRow_10_cell_1, majRow_10_cell_2, majRow_10_cell_3, majRow_10_cell_4, majRow_10_cell_5, majRow_10_cell_6, majRow_10_cell_7, majRow_10_cell_8, majRow_10_cell_9, majRow_10_cell_10]

def majRow_11 : List (MajTree × MajTree) := [
  ((.leaf 12), (.leaf 13)),
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24))
]

theorem majRow_11_cell_0 :
    majCellCheck 11 0 (majRow_11.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_1 :
    majCellCheck 11 1 (majRow_11.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_2 :
    majCellCheck 11 2 (majRow_11.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_3 :
    majCellCheck 11 3 (majRow_11.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_4 :
    majCellCheck 11 4 (majRow_11.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_5 :
    majCellCheck 11 5 (majRow_11.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_6 :
    majCellCheck 11 6 (majRow_11.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_7 :
    majCellCheck 11 7 (majRow_11.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_8 :
    majCellCheck 11 8 (majRow_11.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_9 :
    majCellCheck 11 9 (majRow_11.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_10 :
    majCellCheck 11 10 (majRow_11.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_cell_11 :
    majCellCheck 11 11 (majRow_11.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_11_all : ∀ l, l ≤ 11 →
    majCellCheck 11 l (majRow_11.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_11_cell_0, majRow_11_cell_1, majRow_11_cell_2, majRow_11_cell_3, majRow_11_cell_4, majRow_11_cell_5, majRow_11_cell_6, majRow_11_cell_7, majRow_11_cell_8, majRow_11_cell_9, majRow_11_cell_10, majRow_11_cell_11]

def majRow_12 : List (MajTree × MajTree) := [
  ((.leaf 13), (.leaf 14)),
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26))
]

theorem majRow_12_cell_0 :
    majCellCheck 12 0 (majRow_12.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_1 :
    majCellCheck 12 1 (majRow_12.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_2 :
    majCellCheck 12 2 (majRow_12.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_3 :
    majCellCheck 12 3 (majRow_12.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_4 :
    majCellCheck 12 4 (majRow_12.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_5 :
    majCellCheck 12 5 (majRow_12.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_6 :
    majCellCheck 12 6 (majRow_12.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_7 :
    majCellCheck 12 7 (majRow_12.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_8 :
    majCellCheck 12 8 (majRow_12.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_9 :
    majCellCheck 12 9 (majRow_12.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_10 :
    majCellCheck 12 10 (majRow_12.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_11 :
    majCellCheck 12 11 (majRow_12.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_cell_12 :
    majCellCheck 12 12 (majRow_12.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_12_all : ∀ l, l ≤ 12 →
    majCellCheck 12 l (majRow_12.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_12_cell_0, majRow_12_cell_1, majRow_12_cell_2, majRow_12_cell_3, majRow_12_cell_4, majRow_12_cell_5, majRow_12_cell_6, majRow_12_cell_7, majRow_12_cell_8, majRow_12_cell_9, majRow_12_cell_10, majRow_12_cell_11, majRow_12_cell_12]

def majRow_13 : List (MajTree × MajTree) := [
  ((.leaf 14), (.leaf 15)),
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
  ((.leaf 27), (.leaf 28))
]

theorem majRow_13_cell_0 :
    majCellCheck 13 0 (majRow_13.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_1 :
    majCellCheck 13 1 (majRow_13.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_2 :
    majCellCheck 13 2 (majRow_13.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_3 :
    majCellCheck 13 3 (majRow_13.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_4 :
    majCellCheck 13 4 (majRow_13.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_5 :
    majCellCheck 13 5 (majRow_13.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_6 :
    majCellCheck 13 6 (majRow_13.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_7 :
    majCellCheck 13 7 (majRow_13.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_8 :
    majCellCheck 13 8 (majRow_13.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_9 :
    majCellCheck 13 9 (majRow_13.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_10 :
    majCellCheck 13 10 (majRow_13.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_11 :
    majCellCheck 13 11 (majRow_13.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_12 :
    majCellCheck 13 12 (majRow_13.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_cell_13 :
    majCellCheck 13 13 (majRow_13.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_13_all : ∀ l, l ≤ 13 →
    majCellCheck 13 l (majRow_13.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_13_cell_0, majRow_13_cell_1, majRow_13_cell_2, majRow_13_cell_3, majRow_13_cell_4, majRow_13_cell_5, majRow_13_cell_6, majRow_13_cell_7, majRow_13_cell_8, majRow_13_cell_9, majRow_13_cell_10, majRow_13_cell_11, majRow_13_cell_12, majRow_13_cell_13]

def majRow_14 : List (MajTree × MajTree) := [
  ((.leaf 15), (.leaf 16)),
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
  ((.leaf 20), (.leaf 21)),
  ((.leaf 21), (.leaf 22)),
  ((.leaf 22), (.leaf 23)),
  ((.leaf 23), (.leaf 24)),
  ((.leaf 24), (.leaf 25)),
  ((.leaf 25), (.leaf 26)),
  ((.leaf 26), (.leaf 27)),
  ((.leaf 27), (.leaf 28)),
  ((.leaf 28), (.leaf 29)),
  ((.leaf 29), (.leaf 30))
]

theorem majRow_14_cell_0 :
    majCellCheck 14 0 (majRow_14.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_1 :
    majCellCheck 14 1 (majRow_14.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_2 :
    majCellCheck 14 2 (majRow_14.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_3 :
    majCellCheck 14 3 (majRow_14.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_4 :
    majCellCheck 14 4 (majRow_14.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_5 :
    majCellCheck 14 5 (majRow_14.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_6 :
    majCellCheck 14 6 (majRow_14.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_7 :
    majCellCheck 14 7 (majRow_14.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_8 :
    majCellCheck 14 8 (majRow_14.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_9 :
    majCellCheck 14 9 (majRow_14.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_10 :
    majCellCheck 14 10 (majRow_14.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_11 :
    majCellCheck 14 11 (majRow_14.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_12 :
    majCellCheck 14 12 (majRow_14.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_13 :
    majCellCheck 14 13 (majRow_14.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_cell_14 :
    majCellCheck 14 14 (majRow_14.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_14_all : ∀ l, l ≤ 14 →
    majCellCheck 14 l (majRow_14.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_14_cell_0, majRow_14_cell_1, majRow_14_cell_2, majRow_14_cell_3, majRow_14_cell_4, majRow_14_cell_5, majRow_14_cell_6, majRow_14_cell_7, majRow_14_cell_8, majRow_14_cell_9, majRow_14_cell_10, majRow_14_cell_11, majRow_14_cell_12, majRow_14_cell_13, majRow_14_cell_14]

def majRow_15 : List (MajTree × MajTree) := [
  ((.leaf 16), (.leaf 17)),
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
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
  ((.leaf 31), (.leaf 32))
]

theorem majRow_15_cell_0 :
    majCellCheck 15 0 (majRow_15.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_1 :
    majCellCheck 15 1 (majRow_15.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_2 :
    majCellCheck 15 2 (majRow_15.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_3 :
    majCellCheck 15 3 (majRow_15.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_4 :
    majCellCheck 15 4 (majRow_15.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_5 :
    majCellCheck 15 5 (majRow_15.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_6 :
    majCellCheck 15 6 (majRow_15.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_7 :
    majCellCheck 15 7 (majRow_15.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_8 :
    majCellCheck 15 8 (majRow_15.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_9 :
    majCellCheck 15 9 (majRow_15.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_10 :
    majCellCheck 15 10 (majRow_15.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_11 :
    majCellCheck 15 11 (majRow_15.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_12 :
    majCellCheck 15 12 (majRow_15.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_13 :
    majCellCheck 15 13 (majRow_15.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_14 :
    majCellCheck 15 14 (majRow_15.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_cell_15 :
    majCellCheck 15 15 (majRow_15.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_15_all : ∀ l, l ≤ 15 →
    majCellCheck 15 l (majRow_15.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_15_cell_0, majRow_15_cell_1, majRow_15_cell_2, majRow_15_cell_3, majRow_15_cell_4, majRow_15_cell_5, majRow_15_cell_6, majRow_15_cell_7, majRow_15_cell_8, majRow_15_cell_9, majRow_15_cell_10, majRow_15_cell_11, majRow_15_cell_12, majRow_15_cell_13, majRow_15_cell_14, majRow_15_cell_15]

def majRow_16 : List (MajTree × MajTree) := [
  ((.leaf 17), (.leaf 18)),
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
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
  ((.leaf 33), (.leaf 34))
]

theorem majRow_16_cell_0 :
    majCellCheck 16 0 (majRow_16.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_1 :
    majCellCheck 16 1 (majRow_16.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_2 :
    majCellCheck 16 2 (majRow_16.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_3 :
    majCellCheck 16 3 (majRow_16.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_4 :
    majCellCheck 16 4 (majRow_16.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_5 :
    majCellCheck 16 5 (majRow_16.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_6 :
    majCellCheck 16 6 (majRow_16.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_7 :
    majCellCheck 16 7 (majRow_16.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_8 :
    majCellCheck 16 8 (majRow_16.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_9 :
    majCellCheck 16 9 (majRow_16.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_10 :
    majCellCheck 16 10 (majRow_16.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_11 :
    majCellCheck 16 11 (majRow_16.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_12 :
    majCellCheck 16 12 (majRow_16.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_13 :
    majCellCheck 16 13 (majRow_16.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_14 :
    majCellCheck 16 14 (majRow_16.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_15 :
    majCellCheck 16 15 (majRow_16.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_cell_16 :
    majCellCheck 16 16 (majRow_16.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_16_all : ∀ l, l ≤ 16 →
    majCellCheck 16 l (majRow_16.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_16_cell_0, majRow_16_cell_1, majRow_16_cell_2, majRow_16_cell_3, majRow_16_cell_4, majRow_16_cell_5, majRow_16_cell_6, majRow_16_cell_7, majRow_16_cell_8, majRow_16_cell_9, majRow_16_cell_10, majRow_16_cell_11, majRow_16_cell_12, majRow_16_cell_13, majRow_16_cell_14, majRow_16_cell_15, majRow_16_cell_16]

def majRow_17 : List (MajTree × MajTree) := [
  ((.leaf 18), (.leaf 19)),
  ((.leaf 19), (.leaf 20)),
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
  ((.leaf 35), (.leaf 36))
]

theorem majRow_17_cell_0 :
    majCellCheck 17 0 (majRow_17.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_1 :
    majCellCheck 17 1 (majRow_17.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_2 :
    majCellCheck 17 2 (majRow_17.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_3 :
    majCellCheck 17 3 (majRow_17.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_4 :
    majCellCheck 17 4 (majRow_17.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_5 :
    majCellCheck 17 5 (majRow_17.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_6 :
    majCellCheck 17 6 (majRow_17.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_7 :
    majCellCheck 17 7 (majRow_17.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_8 :
    majCellCheck 17 8 (majRow_17.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_9 :
    majCellCheck 17 9 (majRow_17.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_10 :
    majCellCheck 17 10 (majRow_17.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_11 :
    majCellCheck 17 11 (majRow_17.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_12 :
    majCellCheck 17 12 (majRow_17.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_13 :
    majCellCheck 17 13 (majRow_17.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_14 :
    majCellCheck 17 14 (majRow_17.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_15 :
    majCellCheck 17 15 (majRow_17.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_16 :
    majCellCheck 17 16 (majRow_17.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_cell_17 :
    majCellCheck 17 17 (majRow_17.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_17_all : ∀ l, l ≤ 17 →
    majCellCheck 17 l (majRow_17.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_17_cell_0, majRow_17_cell_1, majRow_17_cell_2, majRow_17_cell_3, majRow_17_cell_4, majRow_17_cell_5, majRow_17_cell_6, majRow_17_cell_7, majRow_17_cell_8, majRow_17_cell_9, majRow_17_cell_10, majRow_17_cell_11, majRow_17_cell_12, majRow_17_cell_13, majRow_17_cell_14, majRow_17_cell_15, majRow_17_cell_16, majRow_17_cell_17]

def majRow_18 : List (MajTree × MajTree) := [
  ((.leaf 19), (.leaf 20)),
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
  ((.leaf 37), (.leaf 38))
]

theorem majRow_18_cell_0 :
    majCellCheck 18 0 (majRow_18.getD 0 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_1 :
    majCellCheck 18 1 (majRow_18.getD 1 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_2 :
    majCellCheck 18 2 (majRow_18.getD 2 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_3 :
    majCellCheck 18 3 (majRow_18.getD 3 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_4 :
    majCellCheck 18 4 (majRow_18.getD 4 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_5 :
    majCellCheck 18 5 (majRow_18.getD 5 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_6 :
    majCellCheck 18 6 (majRow_18.getD 6 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_7 :
    majCellCheck 18 7 (majRow_18.getD 7 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_8 :
    majCellCheck 18 8 (majRow_18.getD 8 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_9 :
    majCellCheck 18 9 (majRow_18.getD 9 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_10 :
    majCellCheck 18 10 (majRow_18.getD 10 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_11 :
    majCellCheck 18 11 (majRow_18.getD 11 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_12 :
    majCellCheck 18 12 (majRow_18.getD 12 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_13 :
    majCellCheck 18 13 (majRow_18.getD 13 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_14 :
    majCellCheck 18 14 (majRow_18.getD 14 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_15 :
    majCellCheck 18 15 (majRow_18.getD 15 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_16 :
    majCellCheck 18 16 (majRow_18.getD 16 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_17 :
    majCellCheck 18 17 (majRow_18.getD 17 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_cell_18 :
    majCellCheck 18 18 (majRow_18.getD 18 (.leaf 0, .leaf 0)) = true := by
  decide +kernel

theorem majRow_18_all : ∀ l, l ≤ 18 →
    majCellCheck 18 l (majRow_18.getD l (.leaf 0, .leaf 0)) = true := by
  intro l hl
  interval_cases l
  exacts [majRow_18_cell_0, majRow_18_cell_1, majRow_18_cell_2, majRow_18_cell_3, majRow_18_cell_4, majRow_18_cell_5, majRow_18_cell_6, majRow_18_cell_7, majRow_18_cell_8, majRow_18_cell_9, majRow_18_cell_10, majRow_18_cell_11, majRow_18_cell_12, majRow_18_cell_13, majRow_18_cell_14, majRow_18_cell_15, majRow_18_cell_16, majRow_18_cell_17, majRow_18_cell_18]

end PartialBalayage.Maximal.Square
