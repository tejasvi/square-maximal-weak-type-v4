/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.HarmonicRadialIntegrability
public import PartialBalayage.Maximal.RadialLocalIntegrability

/-!
# Integrable pairings of joined harmonic radial kernels

The explicit harmonic center integrability and a continuous outer profile give finite signed
Euclidean integrals against every continuous compactly supported density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PartialBalayage

/-- A radial kernel formed by joining a harmonic tangent to a curved outer profile. -/
def joinedRadialKernel (n : ℕ) (a q d b : ℝ) (ψO : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r < b then harmonicRadialTangent n a q d r else ψO r

/-- Joined harmonic radial kernels pair integrably with continuous compactly supported densities. -/
theorem integrable_joinedRadialKernel_mul_compact (n : ℕ) (hn : 1 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (q d : ℝ) (ψO : ℝ → ℝ) (hcψO : Continuous ψO)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (hgsupp : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ joinedRadialKernel n a q d b ψO ‖y - x‖ * g y) := by
  have : NeZero n := ⟨by omega⟩
  let φ := joinedRadialKernel n a q d b ψO
  apply integrable_radial_mul_of_weighted_local n x φ (b := b) _ g hg hgsupp
  intro R hbR
  have hi : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * φ r) (Ioo 0 b) := by
    have h := integrableOn_harmonicRadialTangent_mul_pow_mul n hn (b := b) ha q d
      (fun _ ↦ 1) continuous_const
    apply h.congr_fun
    · intro r hr
      simp only [φ, joinedRadialKernel, ite_eq_left hr.2, mul_one]
      ring
    · exact measurableSet_Ioo
  have ho : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * φ r) (Ico b R) := by
    have h : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * ψO r) (Icc b R) :=
      ((continuous_id.pow (n - 1)).mul hcψO).continuousOn
        |>.integrableOn_compact isCompact_Icc
    apply (h.mono_set Ico_subset_Icc_self).congr_fun
    · intro r hr
      simp only [φ, joinedRadialKernel, ite_eq_right (not_lt.mpr hr.1)]
    · exact measurableSet_Ico
  rw [← Ioo_union_Ico_eq_Ioo hb hbR.le]
  exact hi.union ho

end PartialBalayage
