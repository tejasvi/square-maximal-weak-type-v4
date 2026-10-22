/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.MajorizationTriangle
public import PartialBalayage.Maximal.Square.SparsePolynomial
public import PartialBalayage.Maximal.Square.SquareGridGeometry
public import PartialBalayage.Maximal.Square.KernelMajorization
public import PartialBalayage.Maximal.Square.CellLocalCoefficient
public import PartialBalayage.Maximal.Square.Data.MajRadialRows

/-!
# List-driven majorization certificates for the kernel

Each ordered grid cell carries two subdivision trees (for its lower and upper closed
triangles). A leaf records which rational radial minorant is used: none, a tangent at a grid
radius above the triangle, the tangent at the support radius, or a tangent below the triangle.
Boolean checks recompute the actual lower polynomial by exact sparse arithmetic and test its
degree-six Bernstein coefficients; soundness theorems turn successful checks into kernel bounds.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-! ## Representative coefficients by search -/

/-- The orbit representative test used by the search. -/
def repTest (i j : ℕ) (t : ℕ × ℕ × ℚ) : Bool := t.1 == i && t.2.1 == j

/-- The coefficient of the first orbit with representative `(i, j)`, or zero. -/
def repSearch (L : List (ℕ × ℕ × ℚ)) (i j : ℕ) : ℚ :=
  match L.find? (repTest i j) with
  | some t => t.2.2
  | none => 0

theorem repTest_eq_true {i j : ℕ} {t : ℕ × ℕ × ℚ} :
    repTest i j t = true ↔ (t.1 = i ∧ t.2.1 = j) := by
  simp [repTest]

/-- On a list with distinct representatives, the filtered sum is the searched coefficient. -/
theorem sum_eq_repSearch (i j : ℕ) : ∀ (L : List (ℕ × ℕ × ℚ)),
    (L.map (fun t ↦ (t.1, t.2.1))).Nodup →
      (L.map (fun t ↦ if t.1 = i ∧ t.2.1 = j then t.2.2 else 0)).sum = repSearch L i j := by
  intro L
  induction L with
  | nil => intro _; simp [repSearch]
  | cons t L ih =>
    intro hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnot, hnd⟩ := hnd
    by_cases ht : t.1 = i ∧ t.2.1 = j
    · have hzero : (L.map (fun t ↦ if t.1 = i ∧ t.2.1 = j then t.2.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hz
        have hn : ¬ (t'.1 = i ∧ t'.2.1 = j) := by
          rintro ⟨h₁, h₂⟩
          exact hnot ⟨t', ht', by rw [h₁, h₂, ht.1, ht.2]⟩
        simp only [hn, ↓reduceIte]
      have hfind : (t :: L).find? (repTest i j) = some t := by
        simp [repTest_eq_true.mpr ht]
      simp only [List.map_cons, List.sum_cons, ht, and_self, ↓reduceIte, hzero, add_zero,
        repSearch, hfind]
    · have hfind : (t :: L).find? (repTest i j) = L.find? (repTest i j) := by
        have hf : repTest i j t = false := by
          cases h : repTest i j t
          · rfl
          · exact absurd (repTest_eq_true.mp h) ht
        simp [hf]
      simp only [List.map_cons, List.sum_cons, ht, ↓reduceIte, zero_add]
      rw [ih hnd]
      simp only [repSearch, hfind]

/-- Guarded search for the representative coefficient. -/
def repLookup (i j : ℕ) : ℚ := repSearch splineOrbits i j

theorem representativeCoefficient_eq_repLookup (i j : ℕ) :
    representativeCoefficient i j = repLookup i j := by
  unfold representativeCoefficient repLookup
  exact sum_eq_repSearch i j splineOrbits splineOrbits_indices_nodup

/-- The actual bicubic cell coefficients computed by representative search. -/
def majCellMatrix (k l : ℕ) (a b : Fin 4) : ℚ :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
    repLookup (max ((k : ℤ) - 1 + i).natAbs ((l : ℤ) - 1 + j).natAbs)
      (min ((k : ℤ) - 1 + i).natAbs ((l : ℤ) - 1 + j).natAbs) *
        (cubicSplineCellCoefficient (1 - i) a * cubicSplineCellCoefficient (1 - j) b)

theorem correctionCellCoefficient_eq_majCellMatrix (k l : ℕ) (a b : Fin 4) :
    correctionCellCoefficient k l a b = majCellMatrix k l a b := by
  rw [correctionCellCoefficient_eq_local_range]
  simp only [localCellCoefficient, majCellMatrix, representativeCoefficient_eq_repLookup]

/-! ## Radial rows and leaf kinds -/

/-- Radial row `m` (`m = 1, ..., 53`); row 53 is the support radius. -/
def majRow (m : ℕ) : RadialPowerData := majRadialRows.getD (m - 1) ⟨1, 0, 0, 0, 0⟩

/-- The support-radius row. -/
def majRowR : RadialPowerData := majRow 53

theorem majRow_valid {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m ≤ 53) : (majRow m).IsValid := by
  have hc := majRadialRows_valid
  have hl := majRadialRows_length
  rw [List.all_eq_true] at hc
  have hmem : majRadialRows.getD (m - 1) ⟨1, 0, 0, 0, 0⟩ ∈ majRadialRows := by
    have hlt : m - 1 < majRadialRows.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem ..
  exact of_decide_eq_true (hc _ hmem)

theorem majRowR_valid : majRowR.IsValid := majRow_valid (by norm_num) (by norm_num)

theorem majRowR_radius : majRowR.radius = supportRadiusRat := by
  unfold majRowR majRow supportRadiusRat
  exact majRadialRows_lastRadius

/-- The rational radial minorant `(q, height, slope)` of a leaf kind. -/
def leafRadial (kind : ℕ) : ℚ × ℚ × ℚ :=
  if kind = 0 then (0, 0, 0)
  else if kind ≤ 53 then
    ((majRow kind).radius, certifiedRadialHeight (majRow kind) majRowR,
      certifiedRadialSlope (majRow kind))
  else if 101 ≤ kind ∧ kind ≤ 153 then
    ((majRow (kind - 100)).radius, certifiedRadialHeight (majRow (kind - 100)) majRowR,
      certifiedRadialSlopeUpper (majRow (kind - 100)))
  else (0, 0, 0)

/-- The geometric side condition of a leaf kind. -/
def leafRadiusOK (k l : ℕ) (T : RationalTriangle) (kind : ℕ) : Bool :=
  if kind = 0 ∨ kind = 53 then true
  else if kind ≤ 52 then decide (T.HasRadiusBound k l (majRow kind).radius)
  else if 101 ≤ kind ∧ kind ≤ 153 then
    decide (T.HasRadiusLowerBound k l (majRow (kind - 100)).radius)
  else false

/-- A tangent of the order-47/40 power taken below the point is an actual lower bound. -/
theorem rpow_tangent_below {r q : ℝ} (hq : 0 < q) (hqr : q ≤ r) :
    q ^ (-(47 / 40 : ℝ)) - (47 / 40 : ℝ) * q ^ (-(87 / 40 : ℝ)) * (r - q) ≤
      r ^ (-(47 / 40 : ℝ)) := by
  rcases eq_or_lt_of_le hqr with h | h
  · subst r; simp
  have hd : HasDerivAt (fun x : ℝ ↦ x ^ (-(47 / 40 : ℝ)))
      (-(47 / 40 : ℝ) * q ^ (-(87 / 40 : ℝ))) q := by
    convert Real.hasDerivAt_rpow_const (p := -(47 / 40 : ℝ)) (Or.inl hq.ne') using 1
    norm_num
  have hconv := convexOn_rpow_of_nonpos (-(47 / 40 : ℝ)) (by norm_num)
  have hs := hconv.le_slope_of_hasDerivAt hq (show r ∈ Set.Ioi (0 : ℝ) from hq.trans h) h hd
  rw [slope_def_field] at hs
  have hs' := (le_div_iff₀ (sub_pos.mpr h)).mp hs
  nlinarith

/-- A tangent below the point, with an upper rational slope, bounds the radial base below. -/
theorem radialBase_lower_tangent_below {u v q height slope : ℝ}
    (hq : 0 < q) (hqr : q ≤ diamondRadius u v)
    (hheight : height ≤ radialCoefficient *
      (q ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))))
    (hslope : (47 / 40 : ℝ) * radialCoefficient * q ^ (-(87 / 40 : ℝ)) ≤ slope) :
    height + slope * (q - diamondRadius u v) ≤ radialBase u v := by
  have ht := mul_le_mul_of_nonneg_left (rpow_tangent_below hq hqr) radialCoefficient_pos.le
  have hs := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hqr)
  have hm := le_max_left
    ((diamondRadius u v) ^ (-(47 / 40 : ℝ)) - supportRadius ^ (-(47 / 40 : ℝ))) 0
  have hm' := mul_le_mul_of_nonneg_left hm radialCoefficient_pos.le
  unfold radialBase
  nlinarith

/-- The radial minorant of every accepted leaf kind is valid at every point of the triangle. -/
theorem leafRadial_valid (k l : ℕ) (T : RationalTriangle) (kind : ℕ)
    (hok : leafRadiusOK k l T kind = true) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1)
    (hu : 0 ≤ ((k : ℝ) + (T.point x y).1) / 32) (hv : 0 ≤ ((l : ℝ) + (T.point x y).2) / 32)
    (hr : 0 < ((k : ℝ) + (T.point x y).1) / 32 + ((l : ℝ) + (T.point x y).2) / 32) :
    ((leafRadial kind).2.1 : ℝ) + ((leafRadial kind).2.2 : ℝ) * (((leafRadial kind).1 : ℝ) -
      (((k : ℝ) + (T.point x y).1) / 32 + ((l : ℝ) + (T.point x y).2) / 32)) ≤
        radialBase (((k : ℝ) + (T.point x y).1) / 32) (((l : ℝ) + (T.point x y).2) / 32) := by
  set u := ((k : ℝ) + (T.point x y).1) / 32 with hu_def
  set v := ((l : ℝ) + (T.point x y).2) / 32 with hv_def
  have hdr : diamondRadius u v = u + v := by
    simp only [diamondRadius, abs_of_nonneg hu, abs_of_nonneg hv]
  have hR := majRowR_valid
  have hRr := majRowR_radius
  by_cases h0 : kind = 0
  · subst kind
    simp only [leafRadial, ↓reduceIte, Rat.cast_zero, zero_mul, add_zero]
    exact radialBase_nonneg u v
  by_cases h53 : kind = 53
  · subst kind
    have hd := majRow_valid (m := 53) (by norm_num) (by norm_num)
    have hq : majRow 53 = majRowR := rfl
    have hheight : certifiedRadialHeight (majRow 53) majRowR = 0 := by
      rw [certifiedRadialHeight, hq, hRr, if_pos rfl]
    simp only [leafRadial, show (53 : ℕ) ≠ 0 by norm_num, ↓reduceIte,
      show (53 : ℕ) ≤ 53 by norm_num, hheight, Rat.cast_zero, zero_add]
    have hslope0 := certifiedRadialSlope_nonneg hd
    by_cases hin : u + v ≤ ((majRow 53).radius : ℝ)
    · have hq0 : 0 < ((majRow 53).radius : ℝ) := by exact_mod_cast hd.1
      have h := radialBase_lower_tangent (u := u) (v := v) (by rw [hdr]; exact hr) hq0
        (by rw [hdr]; exact hin) (certifiedRadialHeight_le hd hR hRr) (certifiedRadialSlope_le hd)
      rw [hdr, hheight, Rat.cast_zero, zero_add] at h
      exact h
    · have hneg : ((certifiedRadialSlope (majRow 53) : ℚ) : ℝ) *
          (((majRow 53).radius : ℝ) - (u + v)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hslope0 (by linarith)
      exact hneg.trans (radialBase_nonneg u v)
  by_cases hfwd : kind ≤ 52
  · have hk1 : 1 ≤ kind := by omega
    have hd := majRow_valid (m := kind) hk1 (by omega)
    have hb : T.HasRadiusBound k l (majRow kind).radius := by
      simp only [leafRadiusOK, h0, h53, or_self, ↓reduceIte, hfwd, decide_eq_true_eq] at hok
      exact hok
    have hin := T.radius_le_of_vertices k l hb hx hy hxy
    have hq0 : 0 < ((majRow kind).radius : ℝ) := by exact_mod_cast hd.1
    have h := radialBase_lower_tangent (u := u) (v := v) (by rw [hdr]; exact hr) hq0
      (by rw [hdr]; exact hin) (certifiedRadialHeight_le hd hR hRr) (certifiedRadialSlope_le hd)
    rw [hdr] at h
    simp only [leafRadial, h0, ↓reduceIte, show kind ≤ 53 by omega]
    exact h
  by_cases hrev : 101 ≤ kind ∧ kind ≤ 153
  · have hm1 : 1 ≤ kind - 100 := by omega
    have hd := majRow_valid (m := kind - 100) hm1 (by omega)
    have hb : T.HasRadiusLowerBound k l (majRow (kind - 100)).radius := by
      simp only [leafRadiusOK, h0, h53, or_self, ↓reduceIte, hfwd, hrev, and_self,
        decide_eq_true_eq] at hok
      exact hok
    have hin := T.le_radius_of_vertices k l hb hx hy hxy
    have hq0 : 0 < ((majRow (kind - 100)).radius : ℝ) := by exact_mod_cast hd.1
    have h := radialBase_lower_tangent_below (u := u) (v := v) hq0 (by rw [hdr]; exact hin)
      (certifiedRadialHeight_le hd hR hRr) (le_certifiedRadialSlopeUpper hd)
    rw [hdr] at h
    simp only [leafRadial, h0, ↓reduceIte, show ¬ kind ≤ 53 by omega, hrev, and_self]
    exact h
  · simp only [leafRadiusOK, h0, h53, or_self, ↓reduceIte, hfwd, hrev] at hok
    exact absurd hok (by decide)

/-! ## Leaf checks -/

instance (T : RationalTriangle) : Decidable T.InUnitBox := by
  unfold RationalTriangle.InUnitBox vertexInUnitBox; infer_instance

/-- The exact sparse lower polynomial of a leaf. -/
def majLeafPoly (k l : ℕ) (T : RationalTriangle) (kind : ℕ) (target : ℚ) :
    SparsePlanePolynomial :=
  sparseLowerPullback k l T (majCellMatrix k l) (leafRadial kind).1 (leafRadial kind).2.1
    (leafRadial kind).2.2 target

/-- The Boolean check of one leaf. -/
def majLeafCheck (k l : ℕ) (T : RationalTriangle) (kind : ℕ) (target : ℚ) : Bool :=
  decide T.InUnitBox && leafRadiusOK k l T kind &&
    sparseDegreeSix (majLeafPoly k l T kind target) &&
      (List.finRange 7).all (fun a ↦ (List.finRange 7).all (fun b ↦
        decide (a.val + b.val ≤ 6 → 0 ≤ triangleBernsteinCoefficient
          (sparseCoefficient (majLeafPoly k l T kind target)) a.val b.val)))

theorem majLeafCheck_sound {k l : ℕ} {T : RationalTriangle} {kind : ℕ} {target : ℚ}
    (htarget : (target : ℝ) ≤ 1) (h : majLeafCheck k l T kind target = true)
    {p : ℝ × ℝ} (hp : T.Contains p) :
    (target : ℝ) ≤ kernel (((k : ℝ) + p.1) / 32) (((l : ℝ) + p.2) / 32) := by
  simp only [majLeafCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨hT, hok⟩, hdeg⟩, hbern⟩ := h
  rcases hp with ⟨x, y, hx, hy, hxy, rfl⟩
  have hpoly := lowerPullbackPolynomial_eq_array_of_sparse_checks k l T (majCellMatrix k l)
    (correctionCellCoefficient_eq_majCellMatrix k l) (leafRadial kind).1 (leafRadial kind).2.1
    (leafRadial kind).2.2 target (sparseCoefficient (majLeafPoly k l T kind target)) hdeg
    (fun i j _ ↦ rfl)
  have ht := T.point_in_unitBox hT hx hy hxy
  apply kernel_ge_target_of_lowerPullback k l T _ _ _ target htarget hT hx hy hxy
  · intro hr
    exact leafRadial_valid k l T kind hok hx hy hxy
      (div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) (by norm_num))
      (div_nonneg (add_nonneg (Nat.cast_nonneg l) ht.2.2.1) (by norm_num)) hr
  · intro q hq
    have hq' := mem_triangleIndices.mp hq
    have hb := hbern ⟨q.1, by omega⟩ ⟨q.2, by omega⟩ hq'
    rw [hpoly, planeArrayPolynomial_bernsteinCoefficient]
    exact hb

/-! ## Subdivision trees -/

/-- A midpoint subdivision tree whose leaves record radial kinds. -/
inductive MajTree where
  | leaf : ℕ → MajTree
  | node : MajTree → MajTree → MajTree → MajTree → MajTree

/-- The Boolean check of a subdivision tree on a triangle. -/
def majTreeCheck (k l : ℕ) (target : ℚ) : RationalTriangle → MajTree → Bool
  | T, .leaf kind => majLeafCheck k l T kind target
  | T, .node a b c d => majTreeCheck k l target T.child₀ a && majTreeCheck k l target T.child₁ b &&
      majTreeCheck k l target T.child₂ c && majTreeCheck k l target T.child₃ d

theorem majTreeCheck_sound (k l : ℕ) (target : ℚ) (htarget : (target : ℝ) ≤ 1) :
    ∀ (t : MajTree) (T : RationalTriangle), majTreeCheck k l target T t = true →
      ∀ p : ℝ × ℝ, T.Contains p →
        (target : ℝ) ≤ kernel (((k : ℝ) + p.1) / 32) (((l : ℝ) + p.2) / 32) := by
  intro t
  induction t with
  | leaf kind =>
    intro T h p hp
    exact majLeafCheck_sound htarget h hp
  | node a b c d iha ihb ihc ihd =>
    intro T h p hp
    simp only [majTreeCheck, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
    rcases T.contains_child_of_contains hp with h₀ | h₁ | h₂ | h₃
    · exact iha _ ha p h₀
    · exact ihb _ hb p h₁
    · exact ihc _ hc p h₂
    · exact ihd _ hd p h₃

/-! ## Rows of cells -/

/-- The target on the lower closed triangle of cell `(k, l)`. -/
def majTargetLower (k l : ℕ) : ℚ := if k + l ≤ 31 then 1 else 0

/-- The target on the upper closed triangle of cell `(k, l)`. -/
def majTargetUpper (k l : ℕ) : ℚ := if k + l ≤ 30 then 1 else 0

theorem majTargetLower_le_one (k l : ℕ) : (majTargetLower k l : ℝ) ≤ 1 := by
  unfold majTargetLower; split_ifs <;> norm_num

theorem majTargetUpper_le_one (k l : ℕ) : (majTargetUpper k l : ℝ) ≤ 1 := by
  unfold majTargetUpper; split_ifs <;> norm_num

theorem majTargetLower_nonneg (k l : ℕ) : (0 : ℝ) ≤ majTargetLower k l := by
  unfold majTargetLower; split_ifs <;> norm_num

theorem majTargetUpper_nonneg (k l : ℕ) : (0 : ℝ) ≤ majTargetUpper k l := by
  unfold majTargetUpper; split_ifs <;> norm_num

/-- The Boolean check of one cell. -/
def majCellCheck (k l : ℕ) (c : MajTree × MajTree) : Bool :=
  majTreeCheck k l (majTargetLower k l) lowerCellTriangle c.1 &&
    majTreeCheck k l (majTargetUpper k l) upperCellTriangle c.2

/-- The Boolean check of the cells `l₀, l₀ + 1, ...` of row `k`. -/
def majRowCheckFrom (k : ℕ) : ℕ → List (MajTree × MajTree) → Bool
  | _, [] => true
  | l, c :: cs => majCellCheck k l c && majRowCheckFrom k (l + 1) cs

/-- The Boolean check of a full row `k` (cells `l = 0, ..., k`). -/
def majRowCheck (k : ℕ) (L : List (MajTree × MajTree)) : Bool :=
  L.length == k + 1 && majRowCheckFrom k 0 L

theorem majRowCheckFrom_get (k : ℕ) : ∀ (L : List (MajTree × MajTree)) (l₀ : ℕ),
    majRowCheckFrom k l₀ L = true → ∀ i (hi : i < L.length), majCellCheck k (l₀ + i) L[i] = true := by
  intro L
  induction L with
  | nil => intro l₀ _ i hi; simp at hi
  | cons c cs ih =>
    intro l₀ h i hi
    simp only [majRowCheckFrom, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := ih (l₀ + 1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem majRowCheck_cell {k : ℕ} {L : List (MajTree × MajTree)} (h : majRowCheck k L = true)
    {l : ℕ} (hl : l ≤ k) : ∃ c, majCellCheck k l c = true := by
  simp only [majRowCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hi : l < L.length := by omega
  refine ⟨L[l], ?_⟩
  have := majRowCheckFrom_get k L 0 h.2 l hi
  simpa using this

/-- A checked cell bounds the kernel on its lower closed triangle. -/
theorem majCellCheck_lower {k l : ℕ} {c : MajTree × MajTree} (h : majCellCheck k l c = true)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ 1) :
    (majTargetLower k l : ℝ) ≤ kernel (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) := by
  simp only [majCellCheck, Bool.and_eq_true] at h
  exact majTreeCheck_sound k l _ (majTargetLower_le_one k l) c.1 _ h.1 (t, s)
    (lowerCellTriangle_contains ht hs hts)

/-- A checked cell bounds the kernel on its upper closed triangle. -/
theorem majCellCheck_upper {k l : ℕ} {c : MajTree × MajTree} (h : majCellCheck k l c = true)
    {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (hts : 1 ≤ t + s) :
    (majTargetUpper k l : ℝ) ≤ kernel (((k : ℝ) + t) / 32) (((l : ℝ) + s) / 32) := by
  simp only [majCellCheck, Bool.and_eq_true] at h
  exact majTreeCheck_sound k l _ (majTargetUpper_le_one k l) c.2 _ h.2 (t, s)
    (upperCellTriangle_contains ht hs hts)

end PartialBalayage.Maximal.Square
