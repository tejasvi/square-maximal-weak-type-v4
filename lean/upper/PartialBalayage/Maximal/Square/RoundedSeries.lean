/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

/-!
# Downward-rounded positive series coefficients and list Horner evaluation

Coefficients of positive power series are replaced by dyadic lower bounds with a fixed
number of fractional bits, produced by a rounded recurrence. A list of the rounded values
is generated in one pass, and finite sums are evaluated by Horner recursion over a list.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- Downward rounding to `2^-P`. -/
def roundDown (P : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ P⌋ : ℚ) / 2 ^ P

theorem roundDown_le (P : ℕ) (q : ℚ) : roundDown P q ≤ q := by
  unfold roundDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem roundDown_nonneg (P : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ roundDown P q := by
  unfold roundDown
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (by positivity)

/-- Rounded coefficients of `(1 - z)^(-e)`: `b 0 = 1`, `b (n+1) = round ((n + e) / (n + 1) * b n)`. -/
def roundedRising (P : ℕ) (e : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => roundDown P (((n : ℚ) + e) / (n + 1) * roundedRising P e n)

/-- The exact coefficients of `(1 - z)^(-e)`. -/
def exactRising (e : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ((n : ℚ) + e) / (n + 1) * exactRising e n

theorem roundedRising_nonneg (P : ℕ) {e : ℚ} (he : 0 ≤ e) (n : ℕ) : 0 ≤ roundedRising P e n := by
  induction n with
  | zero => simp [roundedRising]
  | succ n ih => exact roundDown_nonneg P (mul_nonneg (div_nonneg (by positivity) (by positivity)) ih)

theorem roundedRising_le (P : ℕ) {e : ℚ} (he : 0 ≤ e) (n : ℕ) :
    roundedRising P e n ≤ exactRising e n := by
  induction n with
  | zero => simp [roundedRising, exactRising]
  | succ n ih =>
    simp only [roundedRising, exactRising]
    exact (roundDown_le P _).trans
      (mul_le_mul_of_nonneg_left ih (div_nonneg (by positivity) (by positivity)))

/-- One-pass list of `f n (roundedRising P e n)` for `n = k, ..., k + N - 1`, carrying the recurrence. -/
def roundedRisingListAux (P : ℕ) (e : ℚ) (f : ℕ → ℚ → ℚ) : ℕ → ℕ → ℚ → List ℚ
  | 0, _, _ => []
  | N + 1, k, b => f k b :: roundedRisingListAux P e f N (k + 1)
      (roundDown P (((k : ℚ) + e) / (k + 1) * b))

/-- The first `N` values `f n (roundedRising P e n)`. -/
def roundedRisingList (P : ℕ) (e : ℚ) (f : ℕ → ℚ → ℚ) (N : ℕ) : List ℚ :=
  roundedRisingListAux P e f N 0 1

theorem getD_roundedRisingListAux (P : ℕ) (e : ℚ) (f : ℕ → ℚ → ℚ) (N k n : ℕ) (hn : n < N) :
    (roundedRisingListAux P e f N k (roundedRising P e k)).getD n 0 =
      f (k + n) (roundedRising P e (k + n)) := by
  induction N generalizing k n with
  | zero => omega
  | succ N ih =>
    cases n with
    | zero => simp [roundedRisingListAux]
    | succ n =>
      simp only [roundedRisingListAux, List.getD_cons_succ]
      have h := ih (k + 1) n (by omega)
      rw [show k + 1 + n = k + (n + 1) by omega] at h
      exact h

theorem getD_roundedRisingList (P : ℕ) (e : ℚ) (f : ℕ → ℚ → ℚ) {N n : ℕ} (hn : n < N) :
    (roundedRisingList P e f N).getD n 0 = f n (roundedRising P e n) := by
  have h := getD_roundedRisingListAux P e f N 0 n hn
  simpa [roundedRisingList, roundedRising] using h

theorem length_roundedRisingListAux (P : ℕ) (e : ℚ) (f : ℕ → ℚ → ℚ) (N k : ℕ) (b : ℚ) :
    (roundedRisingListAux P e f N k b).length = N := by
  induction N generalizing k b with
  | zero => rfl
  | succ N ih => simp [roundedRisingListAux, ih]

/-- Horner evaluation of `∑ cs[n] x^n` over a coefficient list. -/
def hornerList (cs : List ℚ) (x : ℚ) : ℚ := cs.foldr (fun c acc ↦ c + x * acc) 0

theorem hornerList_eq (cs : List ℚ) (x : ℚ) :
    hornerList cs x = ∑ n ∈ Finset.range cs.length, cs.getD n 0 * x ^ n := by
  induction cs with
  | nil => simp [hornerList]
  | cons c cs ih =>
    rw [show hornerList (c :: cs) x = c + x * hornerList cs x from rfl, ih,
      List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring

/-- The first `N` entries of a list, read through `getD`. -/
theorem sum_take_getD (cs : List ℚ) {N : ℕ} (hN : N ≤ cs.length) (g : ℕ → ℚ → ℚ) :
    ∑ n ∈ Finset.range (cs.take N).length, g n ((cs.take N).getD n 0) =
      ∑ n ∈ Finset.range N, g n (cs.getD n 0) := by
  rw [List.length_take, min_eq_left hN]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_range.mp hn
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hn']

/-- Coefficient list `[k * c 0, (k + 1) * c 1, ...]`. -/
def scaledList : List ℚ → ℕ → List ℚ
  | [], _ => []
  | c :: cs, k => ((k : ℚ) * c) :: scaledList cs (k + 1)

theorem length_scaledList (cs : List ℚ) (k : ℕ) : (scaledList cs k).length = cs.length := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp [scaledList, ih]

theorem getD_scaledList (cs : List ℚ) (k n : ℕ) :
    (scaledList cs k).getD n 0 = ((k + n : ℕ) : ℚ) * cs.getD n 0 := by
  induction cs generalizing k n with
  | nil => simp [scaledList]
  | cons c cs ih =>
    cases n with
    | zero => simp [scaledList]
    | succ n =>
      simp only [scaledList, List.getD_cons_succ, ih]
      congr 2
      omega

/-- Coefficient list with the odd-index entries replaced by zero, starting at index parity `k`. -/
def evenList : List ℚ → ℕ → List ℚ
  | [], _ => []
  | c :: cs, k => (if k % 2 = 0 then c else 0) :: evenList cs (k + 1)

theorem length_evenList (cs : List ℚ) (k : ℕ) : (evenList cs k).length = cs.length := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp [evenList, ih]

theorem getD_evenList (cs : List ℚ) (k n : ℕ) :
    (evenList cs k).getD n 0 = if (k + n) % 2 = 0 then cs.getD n 0 else 0 := by
  induction cs generalizing k n with
  | nil => simp [evenList]
  | cons c cs ih =>
    cases n with
    | zero => simp [evenList]
    | succ n =>
      simp only [evenList, List.getD_cons_succ, ih]
      rw [show k + 1 + n = k + (n + 1) by omega]

end PartialBalayage.Maximal.Square
