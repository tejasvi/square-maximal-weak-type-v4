/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: order 47/40: rows enclose q^(-47/40) and q^(-87/40) by 40th-power checks; Lin's literal rows are replaced by the data module Data/MajRadialRows. -/
module

public import PartialBalayage.Maximal.Square.PowerEnclosure

/-!
# Exact radial root data for all majorization triangles

Each literal row is checked by ordinary rational arithmetic in Lean. The data generator
is outside the trusted proof: validity follows from the explicit 40th-power inequalities,
and the real fractional-power bounds follow from `IsPowerEnclosureDeg.rpow_bounds`.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- One exact radial enclosure row, at an actual positive radius. The fields enclose
`radius^(-47/40)` (`lowerSix`, `upperSix`) and `radius^(-87/40)` (`lowerEleven`, `upperEleven`). -/
structure RadialPowerData where
  radius : ℚ
  lowerSix : ℚ
  upperSix : ℚ
  lowerEleven : ℚ
  upperEleven : ℚ
  deriving DecidableEq

/-- The ordinary rational checks required for one actual radial enclosure row. -/
def RadialPowerData.IsValid (t : RadialPowerData) : Prop :=
  0 < t.radius ∧ IsPowerEnclosureDeg 40 t.radius (-47) t.lowerSix t.upperSix ∧
    IsPowerEnclosureDeg 40 t.radius (-87) t.lowerEleven t.upperEleven

instance (t : RadialPowerData) : Decidable t.IsValid := by
  unfold RadialPowerData.IsValid IsPowerEnclosureDeg
  infer_instance

end PartialBalayage.Maximal.Square
