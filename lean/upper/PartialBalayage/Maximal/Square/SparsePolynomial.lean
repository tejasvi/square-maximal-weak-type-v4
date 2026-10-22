/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: grid cells of width 1/32 instead of 1/16. -/
module

public import PartialBalayage.Maximal.Square.RationalEvaluation
public import PartialBalayage.Maximal.Square.ArrayPolynomial
public import PartialBalayage.Maximal.Square.CellMatrix

/-!
# Sound computable sparse normalization of the actual lower polynomial

Sparse rational multiplication is proved to evaluate as ordinary polynomial
multiplication. Ordinary kernel evaluation can therefore check a literal normal form
without reducing the noncomputable multivariate-polynomial representation.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- A finite list of rational monomials, with repetitions allowed. -/
abbrev SparsePlanePolynomial := List ((ℕ × ℕ) × ℚ)

/-- Genuine rational evaluation of a finite monomial list. -/
def sparseEvaluate (L : SparsePlanePolynomial) (z : Fin 2 → ℚ) : ℚ :=
  (L.map (fun m ↦ m.2 * (z 0 ^ m.1.1 * z 1 ^ m.1.2))).sum

/-- A zero coefficient is omitted from the computable monomial representation. -/
def sparseTerm (p : ℕ × ℕ) (c : ℚ) : SparsePlanePolynomial :=
  if c = 0 then [] else [(p, c)]

/-- Scalar multiplication on the sparse representation. -/
def sparseScale (c : ℚ) (L : SparsePlanePolynomial) : SparsePlanePolynomial :=
  if c = 0 then [] else L.map (fun m ↦ (m.1, c * m.2))

/-- Exact distributive multiplication of two sparse monomial lists. -/
def sparseMultiply : SparsePlanePolynomial → SparsePlanePolynomial → SparsePlanePolynomial
  | [], _ => []
  | m :: L, M => M.map (fun n ↦ ((m.1.1 + n.1.1, m.1.2 + n.1.2), m.2 * n.2)) ++
      sparseMultiply L M

/-- Natural powers formed using exact sparse multiplication. -/
def sparsePower (L : SparsePlanePolynomial) : ℕ → SparsePlanePolynomial
  | 0 => sparseTerm (0, 0) 1
  | n + 1 => sparseMultiply L (sparsePower L n)

/-- The actual affine expression with its zero monomials omitted. -/
def sparseAffine (a b c : ℚ) : SparsePlanePolynomial :=
  sparseTerm (0, 0) a ++ sparseTerm (1, 0) (b - a) ++ sparseTerm (0, 1) (c - a)

theorem sparseEvaluate_append (L M : SparsePlanePolynomial) (z : Fin 2 → ℚ) :
    sparseEvaluate (L ++ M) z = sparseEvaluate L z + sparseEvaluate M z := by
  simp only [sparseEvaluate, List.map_append, List.sum_append]

theorem sparseEvaluate_term (p : ℕ × ℕ) (c : ℚ) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparseTerm p c) z = c * (z 0 ^ p.1 * z 1 ^ p.2) := by
  by_cases hc : c = 0 <;> simp [sparseTerm, hc, sparseEvaluate]

theorem sparseEvaluate_scale (c : ℚ) (L : SparsePlanePolynomial) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparseScale c L) z = c * sparseEvaluate L z := by
  by_cases hc : c = 0
  · simp [sparseScale, hc, sparseEvaluate]
  simp only [sparseScale, ite_eq_right hc]
  induction L with
  | nil => simp [sparseEvaluate]
  | cons m L ih =>
    simp only [List.map_cons, sparseEvaluate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem sparseEvaluate_mapped_product (m : (ℕ × ℕ) × ℚ)
    (M : SparsePlanePolynomial) (z : Fin 2 → ℚ) :
    sparseEvaluate (M.map (fun n ↦
      ((m.1.1 + n.1.1, m.1.2 + n.1.2), m.2 * n.2))) z =
        (m.2 * (z 0 ^ m.1.1 * z 1 ^ m.1.2)) * sparseEvaluate M z := by
  induction M with
  | nil => simp [sparseEvaluate]
  | cons n M ih =>
    simp only [List.map_cons, sparseEvaluate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [pow_add]
    ring

theorem sparseEvaluate_multiply (L M : SparsePlanePolynomial) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparseMultiply L M) z = sparseEvaluate L z * sparseEvaluate M z := by
  induction L with
  | nil => simp [sparseMultiply, sparseEvaluate]
  | cons m L ih =>
    rw [sparseMultiply, sparseEvaluate_append, sparseEvaluate_mapped_product, ih]
    simp only [sparseEvaluate, List.map_cons, List.sum_cons]
    ring

theorem sparseEvaluate_power (L : SparsePlanePolynomial) (n : ℕ) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparsePower L n) z = sparseEvaluate L z ^ n := by
  induction n with
  | zero => simp [sparsePower, sparseEvaluate_term]
  | succ n ih => rw [sparsePower, sparseEvaluate_multiply, ih, pow_succ']

theorem sparseEvaluate_affine (a b c : ℚ) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparseAffine a b c) z = a + (b - a) * z 0 + (c - a) * z 1 := by
  simp [sparseAffine, sparseEvaluate_append, sparseEvaluate_term, add_assoc]

/-- The computable sparse pullback of the actual sixteen-entry cell matrix. -/
def sparseLowerPullback (k l : ℤ) (T : RationalTriangle)
    (c : Fin 4 → Fin 4 → ℚ) (q height slope target : ℚ) : SparsePlanePolynomial :=
  let X := sparseAffine T.v₀.1 T.v₁.1 T.v₂.1
  let Y := sparseAffine T.v₀.2 T.v₁.2 T.v₂.2
  ([0, 1, 2, 3].flatMap (fun a ↦ [0, 1, 2, 3].flatMap (fun b ↦
    sparseScale (cellMatrixExtension c a b)
      (sparseMultiply (sparsePower X a) (sparsePower Y b))))) ++
    sparseTerm (0, 0) (height + slope * (q - (k + l) / 32) - target) ++
      sparseScale (-(slope / 32)) (X ++ Y)

theorem sparseLowerPullback_eval (k l : ℤ) (T : RationalTriangle)
    (c : Fin 4 → Fin 4 → ℚ) (q height slope target : ℚ) (z : Fin 2 → ℚ) :
    sparseEvaluate (sparseLowerPullback k l T c q height slope target) z =
      (∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        cellMatrixExtension c a b *
          ((T.rationalPoint z).1 ^ a * (T.rationalPoint z).2 ^ b)) +
        (height + slope * (q - (k + l) / 32) - target) -
          (slope / 32) * ((T.rationalPoint z).1 + (T.rationalPoint z).2) := by
  simp only [sparseLowerPullback, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    sparseEvaluate_append, sparseEvaluate_scale, sparseEvaluate_multiply,
    sparseEvaluate_power, sparseEvaluate_affine, sparseEvaluate_term,
    Finset.sum_range_succ, Finset.sum_range_zero, RationalTriangle.rationalPoint]
  norm_num only [pow_zero, one_mul, mul_one, mul_zero, zero_mul]
  ring

/-- Collect every repeated occurrence of one ordinary monomial. -/
def sparseCoefficient (L : SparsePlanePolynomial) (p : ℕ × ℕ) : ℚ :=
  (L.map (fun m ↦ if m.1 = p then m.2 else 0)).sum

/-- A decidable support check for total degree at most six. -/
def sparseDegreeSix (L : SparsePlanePolynomial) : Bool :=
  L.all (fun m ↦ decide (m.1.1 + m.1.2 ≤ 6))

theorem sparseDegreeSix_iff (L : SparsePlanePolynomial) :
    sparseDegreeSix L = true ↔ ∀ m ∈ L, m.1.1 + m.1.2 ≤ 6 := by
  simp only [sparseDegreeSix, List.all_eq_true, decide_eq_true_eq]

/-- Collecting the monomials reconstructs the genuine rational evaluation. -/
theorem sparseEvaluate_eq_triangle_sum (L : SparsePlanePolynomial)
    (hL : sparseDegreeSix L = true) (z : Fin 2 → ℚ) :
    sparseEvaluate L z = ∑ p ∈ triangleIndices,
      sparseCoefficient L p * (z 0 ^ p.1 * z 1 ^ p.2) := by
  have hdeg := (sparseDegreeSix_iff L).mp hL
  induction L with
  | nil => simp [sparseEvaluate, sparseCoefficient]
  | cons m L ih =>
    have hm : m.1 ∈ triangleIndices := mem_triangleIndices.mpr (hdeg m (by simp))
    have htail : sparseDegreeSix L = true := (sparseDegreeSix_iff L).mpr
      (fun n hn ↦ hdeg n (by simp [hn]))
    have ih' := ih htail (fun n hn ↦ hdeg n (by simp [hn]))
    simp only [sparseEvaluate, sparseCoefficient, List.map_cons, List.sum_cons,
      add_mul, Finset.sum_add_distrib] at ih' ⊢
    rw [← ih']
    congr 1
    simp [ite_mul, hm]

/-- Kernel-checked sparse data identify the actual lower multivariate polynomial. -/
theorem lowerPullbackPolynomial_eq_array_of_sparse_checks (k l : ℤ)
    (T : RationalTriangle) (c : Fin 4 → Fin 4 → ℚ)
    (hcell : ∀ a b : Fin 4, correctionCellCoefficient k l a b = c a b)
    (q height slope target : ℚ) (a : ℕ × ℕ → ℚ)
    (hdegree : sparseDegreeSix (sparseLowerPullback k l T c q height slope target) = true)
    (hcoeff : ∀ i j : Fin 7, i.val + j.val ≤ 6 →
      sparseCoefficient (sparseLowerPullback k l T c q height slope target) (i.val, j.val) =
        a (i.val, j.val)) :
    lowerPullbackPolynomial k l T q height slope target = planeArrayPolynomial a := by
  apply planePolynomial_eq_array_of_eval
  intro z
  rw [lowerPullbackPolynomial_eval_rat]
  simp only [correctionCellCoefficient_eq_matrix k l c hcell]
  rw [← sparseLowerPullback_eval k l T c q height slope target z,
    sparseEvaluate_eq_triangle_sum _ hdegree]
  apply Finset.sum_congr rfl
  intro p hp
  have h := mem_triangleIndices.mp hp
  rw [hcoeff ⟨p.1, by omega⟩ ⟨p.2, by omega⟩ h]

end PartialBalayage.Maximal.Square
