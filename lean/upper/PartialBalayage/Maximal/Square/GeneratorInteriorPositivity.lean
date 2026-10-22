/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: interior support bound u + v < 264/5. -/
module

public import PartialBalayage.Maximal.Square.GeneratorLeafBlocks
public import PartialBalayage.Maximal.Square.GeneratorPartitionCoverage

/-!
# Unconditional positivity of the actual generator throughout the ordered interior

The genuine geometric partition covers every point in the ordered strict
support triangle. Every coverage label is identified with its checked source
leaf. Pointwise soundness then transfers its exact positive rational lower
bound to the actual radial plus tensor-spline generator density.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- The actual source density is strictly positive throughout its ordered interior. -/
theorem generatorInteriorDensity_pos_on_ordered_interior {u v : ℝ}
    (hv : 0 < v) (hvu : v ≤ u) (hr : u + v < 264 / 5) :
    0 < generatorInteriorDensity u v := by
  obtain ⟨p, hp⟩ := exists_generatorPartitionRectangle_contains hv hvu hr
  have hContains : (generatorPartitionLeaf p).rectangle.Contains u v := by
    simpa only [generatorPartitionLeaf_rectangle_eq] using hp
  exact GeneratorLeafData.positivity (generatorPartitionLeaf_valid p)
    hContains (hv.trans_le hvu) hv hr

end PartialBalayage.Maximal.Square
