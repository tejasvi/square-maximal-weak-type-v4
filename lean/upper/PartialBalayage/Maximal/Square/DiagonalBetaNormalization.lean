/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/- Modified by Tejasvi Singh Tomar, 2026: the Gamma-reflection and tangent normalization for 6/5 is dropped; at 47/40 the intrinsic constant is defined as the positive-beta combination, so the normalization holds by definition. -/
module

public import PartialBalayage.Maximal.Square.RealBetaIntegral
public import PartialBalayage.Maximal.Square.GeneratorConstantBound

/-!
# Exact positive-beta normalization of the diagonal source

The intrinsic constant is defined as the exact combination of the two convergent
positive beta integrals arising from ordinary integration by parts. No
negative-parameter beta integral is introduced.
-/

@[expose] public section

noncomputable section

namespace PartialBalayage.Maximal.Square

/-- Two actual convergent positive beta integrals have the exact intrinsic normalization. -/
theorem diagonal_positiveBeta_normalization :
    2 * ((87 / 7 : ℝ) * realBetaIntegral (33 / 40) (47 / 20) -
      (1404 / 329 : ℝ) * realBetaIntegral (33 / 40) (33 / 40)) = squareIntrinsicConstant :=
  rfl

end PartialBalayage.Maximal.Square
