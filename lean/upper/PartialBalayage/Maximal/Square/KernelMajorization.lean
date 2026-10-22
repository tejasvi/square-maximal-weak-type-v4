/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the quarter-plane inequalities K >= 0 and K >= 1 on the unit diamond are
packaged as the class `KernelMajorizationFacts` (proved numerically for our kernel in a separate module), instead of
being proved here from the grid data of the 6/5 kernel; the global statements below are unchanged. -/
module

public import PartialBalayage.Maximal.Square.Kernel

/-!
# Global nonnegativity and diamond majorization of the actual kernel

The quarter-plane inequalities are the fields of `KernelMajorizationFacts`. Reflection symmetry
extends them to every actual point of the plane, including the origin and both diamond boundaries.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Reflection symmetry identifies the actual kernel at the absolute coordinates. -/
theorem kernel_abs (u v : ℝ) : kernel |u| |v| = kernel u v := by
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hu, abs_of_nonneg hv]
  · rw [abs_of_nonneg hu, abs_of_neg (by linarith), kernel_neg_right]
  · rw [abs_of_neg (by linarith), abs_of_nonneg hv, kernel_neg_left]
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith), kernel_neg_left,
      kernel_neg_right]

/-- The quarter-plane majorization facts of the actual kernel: `K ≥ 0` and `K ≥ 1` on the closed
unit quarter diamond. They are proved by the finite cell checks for our kernel. -/
class KernelMajorizationFacts : Prop where
  nonneg_quarter : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → 0 ≤ kernel u v
  one_le_quarter : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → u + v ≤ 1 → 1 ≤ kernel u v

theorem kernel_nonneg_quarter [KernelMajorizationFacts] {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ kernel u v :=
  KernelMajorizationFacts.nonneg_quarter hu hv

/-- The actual kernel is nonnegative at every point of the plane. -/
theorem kernel_nonneg [KernelMajorizationFacts] (u v : ℝ) : 0 ≤ kernel u v := by
  rw [← kernel_abs u v]
  exact kernel_nonneg_quarter (abs_nonneg u) (abs_nonneg v)

theorem one_le_kernel_quarter [KernelMajorizationFacts] {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : u + v ≤ 1) : 1 ≤ kernel u v :=
  KernelMajorizationFacts.one_le_quarter hu hv hr

/-- The actual kernel majorizes the indicator of the entire closed unit diamond. -/
theorem one_le_kernel_of_diamondRadius_le_one [KernelMajorizationFacts] {u v : ℝ}
    (hr : diamondRadius u v ≤ 1) : 1 ≤ kernel u v := by
  rw [← kernel_abs u v]
  exact one_le_kernel_quarter (abs_nonneg u) (abs_nonneg v) hr

/-- The actual Euclidean-plane kernel is nonnegative everywhere. -/
theorem euclideanKernel_nonneg [KernelMajorizationFacts] (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ euclideanKernel x := kernel_nonneg (x 0) (x 1)

/-- The actual Euclidean kernel majorizes one on the closed unit diamond. -/
theorem one_le_euclideanKernel_of_diamond [KernelMajorizationFacts] {x : EuclideanSpace ℝ (Fin 2)}
    (hx : |x 0| + |x 1| ≤ 1) : 1 ≤ euclideanKernel x :=
  one_le_kernel_of_diamondRadius_le_one hx

/-- The genuine closed-diamond indicator is bounded by the actual Euclidean kernel. -/
theorem indicator_diamond_le_euclideanKernel [KernelMajorizationFacts] (x : EuclideanSpace ℝ (Fin 2)) :
    Set.indicator {y : EuclideanSpace ℝ (Fin 2) | |y 0| + |y 1| ≤ 1}
      (fun _ ↦ (1 : ℝ)) x ≤ euclideanKernel x := by
  classical
  simp only [Set.indicator_apply]
  split_ifs with hx
  · exact one_le_euclideanKernel_of_diamond hx
  · exact euclideanKernel_nonneg x

end PartialBalayage.Maximal.Square
