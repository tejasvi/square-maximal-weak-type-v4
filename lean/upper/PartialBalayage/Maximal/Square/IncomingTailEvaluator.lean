/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: term counts up to 8192 (Fin 8193); the finite tails are evaluated by Horner recursion over the cached coefficient list (one pass per evaluation) instead of indexed lookups. -/
module

public import PartialBalayage.Maximal.Square.IncomingCoefficientData
public import PartialBalayage.Maximal.Square.RoundedSeries
public import PartialBalayage.Maximal.Square.RadialPlaneInterval

/-!
# Exact Horner evaluation of the genuine finite incoming tails

The cached rational coefficients and ordinary Horner recursion evaluate
the actual finite tail polynomials and their actual derivatives. Generic
proved equalities connect every bounded term count and rational point to
the original sums; no finite-evaluation proposition is assumed.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- Ordinary exact Horner recursion for a finite rational coefficient family. -/
def incomingHorner (c : ℕ → ℚ) (N : ℕ) (x : ℚ) : ℚ :=
  match N with
  | 0 => 0
  | n + 1 => c 0 + x * incomingHorner (fun k ↦ c (k + 1)) n x

/-- The genuine recursive evaluation equals the original finite polynomial sum. -/
theorem incomingHorner_eq (c : ℕ → ℚ) (N : ℕ) (x : ℚ) :
    incomingHorner c N x = rationalRadialValue c N x := by
  induction N generalizing c with
  | zero => simp [incomingHorner, rationalRadialValue]
  | succ n ih =>
    rw [incomingHorner, ih]
    unfold rationalRadialValue
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    rw [Finset.mul_sum]
    rw [add_comm (∑ k ∈ Finset.range n, c (k + 1) * x ^ (k + 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring

/-- The rounded even coefficient family. -/
theorem radialEvenCoefficient_eq (n : ℕ) :
    radialEvenCoefficient n = if n % 2 = 0 then radialIncomingCoefficient n else 0 := by
  unfold radialEvenCoefficient
  simp only [Nat.even_iff]

/-- A list agreeing with a coefficient family below `N` evaluates its finite polynomial. -/
theorem hornerList_take_eq {cs : List ℚ} {c : ℕ → ℚ} {N : ℕ} (hN : N ≤ cs.length)
    (hc : ∀ n, n < N → cs.getD n 0 = c n) (x : ℚ) :
    hornerList (cs.take N) x = rationalRadialValue c N x := by
  rw [hornerList_eq, sum_take_getD cs hN (fun n a ↦ a * x ^ n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hc n (Finset.mem_range.mp hn)]

/-- The derivative coefficient list of a list agreeing with a family below `N`. -/
theorem hornerList_scaled_take_eq {cs : List ℚ} {c : ℕ → ℚ} {N : ℕ} (hN : N ≤ cs.length)
    (hc : ∀ n, n < N → cs.getD n 0 = c n) (x : ℚ) :
    hornerList (scaledList ((cs.take N).drop 1) 1) x = rationalRadialDerivative c N x := by
  rw [hornerList_eq, length_scaledList, List.length_drop, List.length_take, min_eq_left hN]
  unfold rationalRadialDerivative
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ' _ M]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_range.mp hm
    rw [getD_scaledList, List.getD_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD, hc (1 + m) (by omega)]
    rw [show 1 + m = m + 1 by omega]
    ring

/-- Fast exact evaluation of the actual incoming tail at every supported term count. -/
def incomingTailValue (N : Fin 8193) (x : ℚ) : ℚ :=
  hornerList (cachedIncomingList.take N.val) x

/-- Fast exact evaluation of the actual incoming-tail derivative. -/
def incomingTailDerivative (N : Fin 8193) (x : ℚ) : ℚ :=
  hornerList (scaledList ((cachedIncomingList.take N.val).drop 1) 1) x

/-- Fast exact evaluation of the actual even incoming tail. -/
def incomingEvenTailValue (N : Fin 8193) (x : ℚ) : ℚ :=
  hornerList ((evenList cachedIncomingList 0).take N.val) x

/-- Fast exact evaluation of the actual even incoming-tail derivative. -/
def incomingEvenTailDerivative (N : Fin 8193) (x : ℚ) : ℚ :=
  hornerList (scaledList (((evenList cachedIncomingList 0).take N.val).drop 1) 1) x

private theorem cache_le (N : Fin 8193) : N.val ≤ cachedIncomingList.length := by
  rw [length_cachedIncomingList]; omega

private theorem even_cache_le (N : Fin 8193) : N.val ≤ (evenList cachedIncomingList 0).length := by
  rw [length_evenList, length_cachedIncomingList]; omega

private theorem cache_getD (N : Fin 8193) :
    ∀ n, n < N.val → cachedIncomingList.getD n 0 = radialIncomingCoefficient n :=
  fun n hn ↦ getD_cachedIncomingList (by omega)

private theorem even_cache_getD (N : Fin 8193) :
    ∀ n, n < N.val → (evenList cachedIncomingList 0).getD n 0 = radialEvenCoefficient n := by
  intro n hn
  rw [getD_evenList, zero_add, radialEvenCoefficient_eq, getD_cachedIncomingList (by omega)]

/-- Exact generic equality with the actual original incoming-tail sum. -/
theorem incomingTailValue_eq (N : Fin 8193) (x : ℚ) :
    incomingTailValue N x = rationalRadialValue radialIncomingCoefficient N.val x :=
  hornerList_take_eq (cache_le N) (cache_getD N) x

/-- Exact generic equality with the actual original incoming-tail derivative. -/
theorem incomingTailDerivative_eq (N : Fin 8193) (x : ℚ) :
    incomingTailDerivative N x = rationalRadialDerivative radialIncomingCoefficient N.val x :=
  hornerList_scaled_take_eq (cache_le N) (cache_getD N) x

/-- Exact generic equality with the actual original even-tail sum. -/
theorem incomingEvenTailValue_eq (N : Fin 8193) (x : ℚ) :
    incomingEvenTailValue N x = rationalRadialValue radialEvenCoefficient N.val x :=
  hornerList_take_eq (even_cache_le N) (even_cache_getD N) x

/-- Exact generic equality with the actual original even-tail derivative. -/
theorem incomingEvenTailDerivative_eq (N : Fin 8193) (x : ℚ) :
    incomingEvenTailDerivative N x = rationalRadialDerivative radialEvenCoefficient N.val x :=
  hornerList_scaled_take_eq (even_cache_le N) (even_cache_getD N) x

end PartialBalayage.Maximal.Square
