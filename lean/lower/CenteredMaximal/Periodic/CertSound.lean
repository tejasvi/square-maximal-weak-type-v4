/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import CenteredMaximal.Periodic.LowerBound
public import CenteredMaximal.Periodic.Cert

/-!
# Soundness of the certificate checker

If `checkCert c rNum rDen = true`, then `rNum / rDen ≤ c₂` (`ofReal_le_weakTypeConstant`).

The certificate describes a periodic configuration (`toConfig`). Its pieces are pairwise disjoint
half-open rectangles in the period cell (`sep` order), so the area of their union `region` is the
sum of their areas (`volume_region`), and every point of a piece lies in a witness rectangle, whose
radius and atoms give a level-one witness (`exists_isWitness`). The lower bound of
`Config.ofReal_div_le_weakTypeConstant` then applies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace CenteredMaximal.Periodic.Cert

/-! ### The checker functions -/

theorem lt_eq_true {a b : ℕ} : lt a b = true ↔ a < b := by
  simp only [lt, Nat.ble_eq]
  omega

theorem lookup_eq (l : List Atom) (i : ℕ) : lookup l i = l[i]? := by
  induction l generalizing i with
  | nil => simp [lookup]
  | cons a l ih => cases i <;> simp [lookup, ih]

theorem rectAt_eq (l : List Rect) (k : ℕ) : rectAt l k = l[k]? := by
  induction l generalizing k with
  | nil => simp [rectAt]
  | cons a l ih => cases k <;> simp [rectAt, ih]

/-- A strictly increasing list is pairwise strictly increasing. -/
theorem sortedLt_pairwise : ∀ l : List ℕ, sortedLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [sortedLt, Bool.and_eq_true, lt_eq_true] at h
    have ih := sortedLt_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun x hx ↦ ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

variable (c : Cert)

/-- The atom number `i` of the period cell (the default atom if there is none). -/
def atomAt (i : ℕ) : Atom := c.atoms.getD i default

theorem atomAt_of_lookup {i : ℕ} {a : Atom} (h : lookup c.atoms i = some a) :
    i < c.atoms.length ∧ c.atomAt i = a := by
  rw [lookup_eq, List.getElem?_eq_some_iff] at h
  obtain ⟨hi, ha⟩ := h
  refine ⟨hi, ?_⟩
  simp [atomAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, ha]

/-- What `atomsMass` checks: every code is an atom of the period cell within `rho` of the
rectangle (in offset coordinates), and the result is the total mass. -/
theorem atomsMass_spec (r : Rect) : ∀ (ts : List ℕ) (s : ℕ), atomsMass c r ts = some s →
    (∀ t ∈ ts, t / 9 < c.atoms.length ∧
      (c.atomAt (t / 9)).x + t % 9 / 3 * c.Px ≤ r.x0 + c.Px + r.rho ∧
      r.x1 + c.Px ≤ (c.atomAt (t / 9)).x + t % 9 / 3 * c.Px + r.rho ∧
      (c.atomAt (t / 9)).y + t % 3 * c.Py ≤ r.y0 + c.Py + r.rho ∧
      r.y1 + c.Py ≤ (c.atomAt (t / 9)).y + t % 3 * c.Py + r.rho) ∧
    s = (ts.map fun t ↦ (c.atomAt (t / 9)).m).sum
  | [], s, h => by
    simp only [atomsMass, Option.some.injEq] at h
    simp [← h]
  | t :: ts, s, h => by
    simp only [atomsMass] at h
    cases hl : lookup c.atoms (t / 9) with
    | none => simp [hl] at h
    | some a =>
      obtain ⟨hlt, hat⟩ := c.atomAt_of_lookup hl
      simp only [hl] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.ble_eq] at hc
        cases hr : atomsMass c r ts with
        | none => simp [hr] at h
        | some s' =>
          simp only [hr, Option.some.injEq] at h
          obtain ⟨ih₁, ih₂⟩ := atomsMass_spec r ts s' hr
          refine ⟨fun u hu ↦ ?_, ?_⟩
          · rcases List.mem_cons.1 hu with rfl | hu
            · rw [hat]
              exact ⟨hlt, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
            · exact ih₁ u hu
          · rw [List.map_cons, List.sum_cons, hat, ← ih₂, ← h]
      · simp at h

/-- What `rectOK` checks. -/
theorem rectOK_spec {r : Rect} (h : rectOK c r = true) :
    r.codes.Pairwise (· < ·) ∧ c.Q ≤ 2 * r.rho * c.ellInv ∧
      ∃ s, atomsMass c r r.codes = some s ∧ 4 * r.rho * r.rho * c.Dm ≤ s * (c.Q * c.Q) := by
  simp only [rectOK, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨sortedLt_pairwise _ h₁, h₂, ?_⟩
  cases hs : atomsMass c r r.codes with
  | none => simp [hs] at h₃
  | some s =>
    simp only [hs, Nat.ble_eq] at h₃
    exact ⟨s, rfl, h₃⟩

theorem rectOK_of_mem : ∀ {l : List Rect}, rectsOK c l = true → ∀ r ∈ l, rectOK c r = true
  | [], _, r, hr => by simp at hr
  | r' :: l, h, r, hr => by
    simp only [rectsOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · exact rectOK_of_mem h.2 r hr

/-- What `pieceOK` checks. -/
theorem pieceOK_spec {p : Piece} (h : pieceOK c p = true) :
    p.xa < p.xb ∧ p.xb ≤ c.Px ∧ p.ya < p.yb ∧ p.yb ≤ c.Py ∧
      ∃ r ∈ c.rects, r.x0 ≤ p.xa ∧ p.xb ≤ r.x1 ∧ r.y0 ≤ p.ya ∧ p.yb ≤ r.y1 := by
  simp only [pieceOK, Bool.and_eq_true, lt_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  cases hr : rectAt c.rects p.k with
  | none => simp [hr] at h₅
  | some r =>
    simp only [hr, Bool.and_eq_true, Nat.ble_eq] at h₅
    rw [rectAt_eq] at hr
    exact ⟨r, List.mem_of_getElem? hr, h₅.1.1.1, h₅.1.1.2, h₅.1.2, h₅.2⟩

/-- The order of consecutive pieces. -/
def Sep (p q : Piece) : Prop :=
  p.xb ≤ q.xa ∨ (p.xa = q.xa ∧ p.xb = q.xb ∧ p.yb ≤ q.ya)

theorem sep_spec {p q : Piece} (h : sep p q = true) : Sep p q := by
  simpa only [sep, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Sep,
    and_assoc] using h

theorem piecesOK_head {p : Piece} {l : List Piece} (h : piecesOK c (p :: l) = true) :
    pieceOK c p = true := by
  cases l with
  | nil => simpa [piecesOK] using h
  | cons q l =>
    simp only [piecesOK, Bool.and_eq_true] at h
    exact h.1.1

theorem piecesOK_tail {p : Piece} {l : List Piece} (h : piecesOK c (p :: l) = true) :
    piecesOK c l = true := by
  cases l with
  | nil => rfl
  | cons q l =>
    simp only [piecesOK, Bool.and_eq_true] at h
    exact h.2

theorem pieceOK_of_mem : ∀ {l : List Piece}, piecesOK c l = true → ∀ p ∈ l, pieceOK c p = true
  | [], _, p, hp => by simp at hp
  | p' :: l, h, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact c.piecesOK_head h
    · exact pieceOK_of_mem (c.piecesOK_tail h) p hp

/-- In a valid list of pieces, every piece comes before (`Sep`) all later pieces. -/
theorem sep_of_piecesOK : ∀ (l : List Piece) (p : Piece), piecesOK c (p :: l) = true →
    ∀ q ∈ l, Sep p q
  | [], _, _, q, hq => by simp at hq
  | q :: l, p, h, r, hr => by
    have h' := h
    simp only [piecesOK, Bool.and_eq_true] at h'
    have hpq := sep_spec h'.1.2
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hpq
    · have hqr := sep_of_piecesOK l q h'.2 r hr
      have hq := c.pieceOK_spec (c.piecesOK_head h'.2)
      unfold Sep at hpq hqr ⊢
      omega

/-! ### The configuration and the covered region -/

/-- The periodic configuration described by a certificate. -/
def toConfig (hQ : 0 < c.Q) (hPx : 0 < c.Px) (hPy : 0 < c.Py) (he : 0 < c.ellInv) : Config where
  px := c.Px / c.Q
  py := c.Py / c.Q
  n := c.atoms.length
  ax i := (c.atomAt i).x / c.Q
  ay i := (c.atomAt i).y / c.Q
  am i := (c.atomAt i).m / c.Dm
  ell := 1 / c.ellInv
  px_pos := div_pos (Nat.cast_pos.2 hPx) (Nat.cast_pos.2 hQ)
  py_pos := div_pos (Nat.cast_pos.2 hPy) (Nat.cast_pos.2 hQ)
  am_nonneg _ := by positivity
  ell_pos := one_div_pos.2 (Nat.cast_pos.2 he)

/-- The half-open rectangle `[xa / Q, xb / Q) × [ya / Q, yb / Q)` of a piece. -/
def pieceSet (p : Piece) : Set (Fin 2 → ℝ) :=
  univ.pi fun i ↦
    Ico (![(p.xa : ℝ) / c.Q, (p.ya : ℝ) / c.Q] i) (![(p.xb : ℝ) / c.Q, (p.yb : ℝ) / c.Q] i)

/-- The union of the pieces of a list. -/
def region : List Piece → Set (Fin 2 → ℝ)
  | [] => ∅
  | p :: l => c.pieceSet p ∪ region l

theorem mem_pieceSet {p : Piece} {z : Fin 2 → ℝ} :
    z ∈ c.pieceSet p ↔ ((p.xa : ℝ) / c.Q ≤ z 0 ∧ z 0 < p.xb / c.Q) ∧
      ((p.ya : ℝ) / c.Q ≤ z 1 ∧ z 1 < p.yb / c.Q) := by
  simp [pieceSet, Fin.forall_fin_two]

theorem measurableSet_region : ∀ l : List Piece, MeasurableSet (c.region l)
  | [] => MeasurableSet.empty
  | _ :: l => (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico).union (measurableSet_region l)

theorem mem_region : ∀ {l : List Piece} {z : Fin 2 → ℝ}, z ∈ c.region l → ∃ p ∈ l, z ∈ c.pieceSet p
  | [], z, hz => by simp [region] at hz
  | p :: l, z, hz => by
    rcases hz with hz | hz
    · exact ⟨p, List.mem_cons_self .., hz⟩
    · obtain ⟨q, hq, hzq⟩ := mem_region hz
      exact ⟨q, List.mem_cons_of_mem _ hq, hzq⟩

theorem disjoint_pieceSet (hQ : 0 < c.Q) {p q : Piece} (h : Sep p q) :
    Disjoint (c.pieceSet p) (c.pieceSet q) := by
  rw [Set.disjoint_left]
  intro z hp hq
  rw [mem_pieceSet] at hp hq
  rcases h with h | ⟨-, -, h⟩
  · have : (p.xb : ℝ) / c.Q ≤ q.xa / c.Q := by gcongr
    linarith [hp.1.2, hq.1.1]
  · have : (p.yb : ℝ) / c.Q ≤ q.ya / c.Q := by gcongr
    linarith [hp.2.2, hq.2.1]

theorem disjoint_region (hQ : 0 < c.Q) {p : Piece} :
    ∀ {l : List Piece}, (∀ q ∈ l, Sep p q) → Disjoint (c.pieceSet p) (c.region l)
  | [], _ => by simp [region]
  | q :: l, h => Disjoint.union_right (c.disjoint_pieceSet hQ (h q (List.mem_cons_self ..)))
      (disjoint_region hQ fun r hr ↦ h r (List.mem_cons_of_mem _ hr))

theorem volume_pieceSet (hQ : 0 < c.Q) {p : Piece} (hx : p.xa ≤ p.xb) (hy : p.ya ≤ p.yb) :
    volume (c.pieceSet p) = ENNReal.ofReal (((p.xb - p.xa) * (p.yb - p.ya) : ℕ) / (c.Q * c.Q)) := by
  rw [pieceSet, Real.volume_pi_Ico, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hQ' : (0 : ℝ) < c.Q := Nat.cast_pos.2 hQ
  rw [← ENNReal.ofReal_mul (sub_nonneg.2 (by gcongr))]
  congr 1
  push_cast [Nat.cast_sub hx, Nat.cast_sub hy]
  field_simp

/-- The area of the union of a valid list of pieces is the total area of the pieces. -/
theorem volume_region (hQ : 0 < c.Q) : ∀ l : List Piece, piecesOK c l = true →
    volume (c.region l) = ENNReal.ofReal ((area l : ℝ) / (c.Q * c.Q))
  | [], _ => by simp [region, area]
  | p :: l, h => by
    have hp := c.pieceOK_spec (c.piecesOK_head h)
    rw [region, measure_union (c.disjoint_region hQ (c.sep_of_piecesOK l p h))
      (c.measurableSet_region l), c.volume_pieceSet hQ hp.1.le hp.2.2.1.le,
      volume_region hQ l (c.piecesOK_tail h), ← ENNReal.ofReal_add (by positivity) (by positivity),
      area]
    congr 1
    push_cast
    ring

theorem region_subset_cell (hQ : 0 < c.Q) (hPx : 0 < c.Px) (hPy : 0 < c.Py) (he : 0 < c.ellInv) :
    ∀ {l : List Piece}, piecesOK c l = true → c.region l ⊆ (c.toConfig hQ hPx hPy he).cell := by
  intro l hl z hz
  obtain ⟨p, hp, hzp⟩ := c.mem_region hz
  obtain ⟨-, hxb, -, hyb, -⟩ := c.pieceOK_spec (c.pieceOK_of_mem hl p hp)
  rw [mem_pieceSet] at hzp
  rw [Config.mem_cell]
  simp only [toConfig]
  refine ⟨⟨le_trans (by positivity) hzp.1.1, hzp.1.2.trans_le ?_⟩,
    ⟨le_trans (by positivity) hzp.2.1, hzp.2.2.trans_le ?_⟩⟩ <;>
  · gcongr

/-! ### Witnesses -/

/-- The index `(i, a - 1, b - 1)` of the atom with code `9 i + 3 a + b`. -/
def decode (t : ℕ) : ℕ × ℤ × ℤ := (t / 9, ((t % 9 / 3 : ℕ) : ℤ) - 1, ((t % 3 : ℕ) : ℤ) - 1)

theorem decode_injective : Function.Injective decode := by
  intro t u h
  simp only [decode, Prod.mk.injEq, sub_left_inj, Nat.cast_inj] at h
  omega

/-- `|X / Q - z| ≤ ρ / Q` from bounds on `X` in units of `1 / Q`. -/
private theorem abs_sub_le_of_bounds {Q X ρ x0 x1 xa xb z : ℝ} (hQ : 0 < Q)
    (h₁ : X ≤ x0 + ρ) (h₂ : x1 ≤ X + ρ) (h₃ : x0 ≤ xa) (h₄ : xb ≤ x1) (h₅ : xa / Q ≤ z)
    (h₆ : z < xb / Q) : |X / Q - z| ≤ ρ / Q := by
  rw [div_le_iff₀ hQ] at h₅
  rw [lt_div_iff₀ hQ] at h₆
  have e : X / Q - z = (X - z * Q) / Q := by field_simp
  rw [e, abs_div, abs_of_pos hQ, div_le_div_iff_of_pos_right hQ, abs_le]
  constructor <;> linarith

private theorem sum_map_cast_div (l : List ℕ) (f : ℕ → ℕ) (d : ℝ) :
    (l.map fun t ↦ (f t : ℝ) / d).sum = ((l.map f).sum : ℕ) / d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- Every point of a piece of a valid certificate has a level-one witness with atoms in
`nearBox 0 0`. -/
theorem exists_isWitness (hQ : 0 < c.Q) (hPx : 0 < c.Px) (hPy : 0 < c.Py) (he : 0 < c.ellInv)
    (hDm : 0 < c.Dm) (hr : rectsOK c c.rects = true) {p : Piece} (hp : pieceOK c p = true)
    {z : Fin 2 → ℝ} (hz : z ∈ c.pieceSet p) :
    ∃ L A, A ⊆ (c.toConfig hQ hPx hPy he).nearBox 0 0 ∧
      (c.toConfig hQ hPx hPy he).IsWitness (z 0) (z 1) L A := by
  obtain ⟨-, -, -, -, r, hrm, hx0, hx1, hy0, hy1⟩ := c.pieceOK_spec hp
  obtain ⟨hsort, hell, s, hs, hmass⟩ := c.rectOK_spec (c.rectOK_of_mem hr r hrm)
  obtain ⟨hat, hsum⟩ := c.atomsMass_spec r r.codes s hs
  rw [mem_pieceSet] at hz
  have hQ' : (0 : ℝ) < c.Q := Nat.cast_pos.2 hQ
  have hDm' : (0 : ℝ) < c.Dm := Nat.cast_pos.2 hDm
  have he' : (0 : ℝ) < c.ellInv := Nat.cast_pos.2 he
  have hnd : (r.codes.map decode).Nodup :=
    (List.Nodup.map decode_injective (hsort.imp fun h ↦ h.ne))
  refine ⟨2 * r.rho / c.Q, (r.codes.map decode).toFinset, ?_, ?_, ?_, ?_⟩
  · -- the atoms lie in the period cell `(0, 0)` and its neighbours
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    have := (hat t ht).1
    simp only [Config.nearBox, toConfig, decode, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc]
    omega
  · -- the side is at least `1 / ellInv`
    simp only [toConfig]
    rw [div_le_div_iff₀ he' hQ', one_mul]
    exact_mod_cast hell
  · -- the mass is at least `L²`
    rw [List.sum_toFinset _ hnd, List.map_map]
    have : ((r.codes.map ((Config.mass (c.toConfig hQ hPx hPy he)) ∘ decode)).sum : ℝ) =
        (s : ℝ) / c.Dm := by
      show (r.codes.map fun t ↦ ((c.atomAt (t / 9)).m : ℝ) / c.Dm).sum = _
      rw [sum_map_cast_div, hsum]
    rw [this, div_pow, div_le_div_iff₀ (by positivity) hDm']
    exact_mod_cast (by nlinarith [hmass] : (2 * r.rho) ^ 2 * c.Dm ≤ s * c.Q ^ 2)
  · -- every atom lies within `L / 2 = rho / Q` of `z`
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    obtain ⟨-, h₁, h₂, h₃, h₄⟩ := hat t ht
    simp only [toConfig, decode]
    generalize t % 9 / 3 = a at h₁ h₂ ⊢
    generalize t % 3 = b at h₃ h₄ ⊢
    generalize c.atomAt (t / 9) = atm at h₁ h₂ h₃ h₄ ⊢
    have hL : 2 * (r.rho : ℝ) / c.Q / 2 = r.rho / c.Q := by ring
    have hX : (atm.x : ℝ) / c.Q + (((a : ℤ) - 1 : ℤ) : ℝ) * (c.Px / c.Q) =
        (((atm.x + a * c.Px : ℕ) : ℝ) - c.Px) / c.Q := by
      push_cast
      field_simp
      ring
    have hY : (atm.y : ℝ) / c.Q + (((b : ℤ) - 1 : ℤ) : ℝ) * (c.Py / c.Q) =
        (((atm.y + b * c.Py : ℕ) : ℝ) - c.Py) / c.Q := by
      push_cast
      field_simp
      ring
    rw [hL, hX, hY]
    have h₁' := (Nat.cast_le (α := ℝ)).2 h₁
    have h₂' := (Nat.cast_le (α := ℝ)).2 h₂
    have h₃' := (Nat.cast_le (α := ℝ)).2 h₃
    have h₄' := (Nat.cast_le (α := ℝ)).2 h₄
    push_cast at h₁' h₂' h₃' h₄'
    constructor
    · refine abs_sub_le_of_bounds hQ' (x0 := r.x0) (x1 := r.x1) (xa := p.xa) (xb := p.xb)
        ?_ ?_ (by exact_mod_cast hx0) (by exact_mod_cast hx1) hz.1.1 hz.1.2
      · push_cast
        linarith
      · push_cast
        linarith
    · refine abs_sub_le_of_bounds hQ' (x0 := r.y0) (x1 := r.y1) (xa := p.ya) (xb := p.yb)
        ?_ ?_ (by exact_mod_cast hy0) (by exact_mod_cast hy1) hz.2.1 hz.2.2
      · push_cast
        linarith
      · push_cast
        linarith

/-! ### The lower bound -/

theorem cellMass_toConfig (hQ : 0 < c.Q) (hPx : 0 < c.Px) (hPy : 0 < c.Py) (he : 0 < c.ellInv) :
    (c.toConfig hQ hPx hPy he).cellMass = (cellMass c.atoms : ℝ) / c.Dm := by
  simp only [Config.cellMass, toConfig, atomAt]
  rw [← Finset.sum_div]
  congr 1
  have : ∀ l : List Atom, ∑ i ∈ Finset.range l.length, ((l.getD i default).m : ℝ) =
      (cellMass l : ℝ) := by
    intro l
    induction l with
    | nil => simp [cellMass]
    | cons a l ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, ih, cellMass]
      push_cast
      ring
  exact this c.atoms

/-- **Soundness.** A valid certificate proves `rNum / rDen ≤ c₂`. -/
theorem ofReal_le_weakTypeConstant {rNum rDen : ℕ} (h : checkCert c rNum rDen = true) :
    ENNReal.ofReal ((rNum : ℝ) / rDen) ≤ weakTypeConstant 2 := by
  simp only [checkCert, Bool.and_eq_true, lt_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hQ, hDm⟩, hPx⟩, hPy⟩, he⟩, hrDen⟩, hm⟩, hr⟩, hp⟩, hratio⟩ := h
  set cfg := c.toConfig hQ hPx hPy he
  have hQ' : (0 : ℝ) < c.Q := Nat.cast_pos.2 hQ
  have hDm' : (0 : ℝ) < c.Dm := Nat.cast_pos.2 hDm
  have hm' : (0 : ℝ) < cellMass c.atoms := Nat.cast_pos.2 hm
  have hcm : 0 < cfg.cellMass := by
    rw [c.cellMass_toConfig]
    positivity
  have key := cfg.ofReal_div_le_weakTypeConstant (c.measurableSet_region c.pieces)
    (c.region_subset_cell hQ hPx hPy he hp)
    (fun z hz ↦ by
      obtain ⟨p, hpm, hzp⟩ := c.mem_region hz
      exact c.exists_isWitness hQ hPx hPy he hDm hr (c.pieceOK_of_mem hp p hpm) hzp)
    (c.volume_region hQ c.pieces hp).symm.le hcm
  refine (ENNReal.ofReal_le_ofReal ?_).trans key
  have e : (area c.pieces : ℝ) / (c.Q * c.Q) / ((cellMass c.atoms : ℝ) / c.Dm) =
      (area c.pieces * c.Dm : ℝ) / (c.Q * c.Q * cellMass c.atoms) := by
    field_simp
  rw [c.cellMass_toConfig, e, div_le_div_iff₀ (by positivity) (by positivity)]
  have := (Nat.cast_le (α := ℝ)).2 hratio
  push_cast at this
  calc (rNum : ℝ) * (c.Q * c.Q * cellMass c.atoms) = rNum * (c.Q * c.Q) * cellMass c.atoms := by
        ring
    _ ≤ _ := this

end CenteredMaximal.Periodic.Cert
