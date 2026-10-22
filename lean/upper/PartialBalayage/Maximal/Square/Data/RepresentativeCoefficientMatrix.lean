/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the 25 x 25 literal array and its `norm_num` proof are replaced by the
lower-triangular table `representativeCoefficientRows` of our kernel (rows 0..71), identified with the orbit list by
one kernel pass (`representativeCoefficient_eq_rows`). -/
module

public import PartialBalayage.Maximal.Square.Data.RepresentativeCoefficientRows

/-!
# A proved finite literal cache of the actual representative coefficient function

The kernel-checked lower-triangular table records the immutable rational orbit
coefficients. Its proof is reused by the generator arithmetic, so repeated cell
calculations need not re-expand the complete orbit list.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

/-- A transparent finite lookup, with the actual zero value beyond the coefficient box. -/
def literalRepresentativeCoefficient (i j : ℕ) : ℚ :=
  (representativeCoefficientRows.getD i []).getD j 0

/-- The finite literal cache is the actual representative coefficient function on every index. -/
theorem representativeCoefficient_eq_literal (i j : ℕ) :
    representativeCoefficient i j = literalRepresentativeCoefficient i j :=
  representativeCoefficient_eq_rows i j

end PartialBalayage.Maximal.Square
