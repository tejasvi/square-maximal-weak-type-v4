/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import PartialBalayage.Maximal.Square.KernelMajorizationProofCore

/-!
# From checked ordered cells to the quarter-plane majorization facts

Reflection reduces to the ordered sector `0 ≤ v ≤ u`. Beyond `9/4` the kernel vanishes; inside,
every point lies in a closed ordered grid cell of width `1/32`, whose two checked triangles give
the bounds. Points of the unit diamond on the line `k + l = 32` are moved to a neighbouring cell.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Every point with `0 ≤ v ≤ u < 9/4` lies in a closed ordered cell. -/
theorem ordered_cell_of_point {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u < 9 / 4) :
    ∃ k l : ℕ, l ≤ k ∧ k ≤ 71 ∧ ∃ t s : ℝ, 0 ≤ t ∧ t < 1 ∧ 0 ≤ s ∧ s < 1 ∧
      u = ((k : ℝ) + t) / 32 ∧ v = ((l : ℝ) + s) / 32 := by
  have hu0 : 0 ≤ u := hv.trans hvu
  have h32u : (0 : ℝ) ≤ 32 * u := by positivity
  have h32v : (0 : ℝ) ≤ 32 * v := by positivity
  have hk : ⌊32 * u⌋₊ < 72 := by
    rw [Nat.floor_lt h32u]; push_cast; linarith
  refine ⟨⌊32 * u⌋₊, ⌊32 * v⌋₊, Nat.floor_mono (by linarith : 32 * v ≤ 32 * u), by omega,
    32 * u - ⌊32 * u⌋₊, 32 * v - ⌊32 * v⌋₊, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [Nat.floor_le h32u]
  · linarith [Nat.lt_floor_add_one (32 * u)]
  · linarith [Nat.floor_le h32v]
  · linarith [Nat.lt_floor_add_one (32 * v)]
  · ring
  · ring

section Cells

variable (cert : ℕ → ℕ → MajTree × MajTree)
  (hcert : ∀ k l : ℕ, l ≤ k → k ≤ 71 → majCellCheck k l (cert k l) = true)
include hcert

theorem kernel_nonneg_ordered_of_cells {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    0 ≤ kernel u v := by
  have hu : 0 ≤ u := hv.trans hvu
  by_cases hbox : 9 / 4 ≤ u
  · rw [kernel_eq_zero_of_box (Or.inl (by rwa [abs_of_nonneg hu]))]
  obtain ⟨k, l, hlk, hk, t, s, ht0, ht1, hs0, hs1, rfl, rfl⟩ :=
    ordered_cell_of_point hv hvu (by linarith)
  have hc := hcert k l hlk hk
  by_cases hts : t + s ≤ 1
  · exact (majTargetLower_nonneg k l).trans (majCellCheck_lower hc ht0 hs0 hts)
  · exact (majTargetUpper_nonneg k l).trans
      (majCellCheck_upper hc ht1.le hs1.le (by linarith))

theorem one_le_kernel_ordered_of_cells {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u)
    (huv : u + v ≤ 1) : 1 ≤ kernel u v := by
  obtain ⟨k, l, hlk, hk, t, s, ht0, ht1, hs0, hs1, rfl, rfl⟩ :=
    ordered_cell_of_point hv hvu (by linarith)
  have hsum : (k : ℝ) + l + t + s ≤ 32 := by linarith
  have hkl32 : k + l ≤ 32 := by
    have h : ((k + l : ℕ) : ℝ) ≤ 32 := by push_cast; linarith
    exact_mod_cast h
  by_cases hts : t + s ≤ 1
  · by_cases hkl : k + l ≤ 31
    · have h := majCellCheck_lower (hcert k l hlk hk) ht0 hs0 hts
      rwa [majTargetLower, if_pos hkl, Rat.cast_one] at h
    · have hkl' : k + l = 32 := by omega
      have hkl'' : (k : ℝ) + l = 32 := by exact_mod_cast hkl'
      have ht : t = 0 := by linarith
      have hs : s = 0 := by linarith
      subst ht hs
      by_cases hlk' : l < k
      · have hk1 : 1 ≤ k := by omega
        have h := majCellCheck_lower (hcert (k - 1) l (by omega) (by omega))
          (by norm_num : (0 : ℝ) ≤ 1) (le_refl (0 : ℝ)) (by norm_num : (1 : ℝ) + 0 ≤ 1)
        rw [majTargetLower, if_pos (by omega), Rat.cast_one, Nat.cast_sub hk1] at h
        convert h using 2 <;> push_cast <;> ring
      · have hkk : k = 16 := by omega
        have hll : l = 16 := by omega
        subst hkk hll
        have h := majCellCheck_lower (hcert 16 15 (by norm_num) (by norm_num))
          (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) + 1 ≤ 1)
        rw [majTargetLower, if_pos (by norm_num), Rat.cast_one] at h
        convert h using 2 <;> push_cast <;> ring
  · have hkl : k + l ≤ 30 := by
      have h : ((k + l : ℕ) : ℝ) < 31 := by push_cast; linarith
      have h' : k + l < 31 := by exact_mod_cast h
      omega
    have h := majCellCheck_upper (hcert k l hlk hk) ht1.le hs1.le (by linarith)
    rwa [majTargetUpper, if_pos hkl, Rat.cast_one] at h

/-- Checked certificates for all ordered cells give the quarter-plane majorization facts. -/
theorem kernelMajorizationFacts_of_cells : KernelMajorizationFacts where
  nonneg_quarter := by
    intro u v hu hv
    rcases le_total v u with hvu | huv
    · exact kernel_nonneg_ordered_of_cells cert hcert hv hvu
    · rw [← kernel_swap]
      exact kernel_nonneg_ordered_of_cells cert hcert hu huv
  one_le_quarter := by
    intro u v hu hv huv
    rcases le_total v u with hvu | hvu'
    · exact one_le_kernel_ordered_of_cells cert hcert hv hvu huv
    · rw [← kernel_swap]
      exact one_le_kernel_ordered_of_cells cert hcert hu hvu' (by linarith)

end Cells

end PartialBalayage.Maximal.Square
