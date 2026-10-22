/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

public import CenteredMaximal.Periodic.CertSound
public import CenteredMaximal.Periodic.Data

/-!
# The lower bound `c₂ ≥ 1.7027237335`

The certificate `Cert.cert` (a periodic configuration of 50 point masses per period cell, with its
witness rectangles and disjoint pieces) passes the checker in the kernel (`Cert.cert_check`), so its
covered area per unit mass, at least `17027237335 / 10¹⁰`, is a lower bound for the weak type
`(1, 1)` constant `c₂` of the centred maximal operator over squares
(`Cert.ofReal_le_weakTypeConstant`). The covered area per unit mass is exactly the rational number
of `ofReal_le_weakTypeConstant_two_exact`.
-/

@[expose] public section

namespace CenteredMaximal

namespace Periodic.Cert

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The certificate passes the checker, evaluated by the kernel. -/
theorem cert_check : checkCert cert 17027237335 10000000000 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The certificate passes the checker with the exact covered area per unit mass. -/
theorem cert_check_exact :
    checkCert cert 482167717377842991882283179477574801392641890014291050323
      283174368139841919615520431313000857449005056000000000000 = true := by
  decide +kernel

end Periodic.Cert

/-- **Lower bound.** `c₂ ≥ 1.7027237335`, where `c₂` is the weak type `(1, 1)` constant of the
centred maximal operator over axis-parallel squares in the plane. -/
theorem ofReal_le_weakTypeConstant_two :
    ENNReal.ofReal (17027237335 / 10000000000) ≤ weakTypeConstant 2 := by
  have h := Periodic.Cert.ofReal_le_weakTypeConstant Periodic.Cert.cert Periodic.Cert.cert_check
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

/-- **Lower bound, exact form.** `c₂` is at least the covered area per unit mass of the
certificate's configuration, the rational number below (`1.70272373359629…`). -/
theorem ofReal_le_weakTypeConstant_two_exact :
    ENNReal.ofReal (482167717377842991882283179477574801392641890014291050323 /
      283174368139841919615520431313000857449005056000000000000) ≤ weakTypeConstant 2 := by
  have h := Periodic.Cert.ofReal_le_weakTypeConstant Periodic.Cert.cert
    Periodic.Cert.cert_check_exact
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

end CenteredMaximal
