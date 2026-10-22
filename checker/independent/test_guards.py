"""positive controls for the fail-closed guards of the 47a audit checker (each guard must FIRE):
NaN-safe Bernstein minimum, fin(), NaN-safe APsi_lower_const, subcell_lower with a NaN A Psi bound, apow on NaN,
Spec class-key check, quad_A series-truncation check (ctx.cap too small)."""
import os
import sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb, arb_mat, ctx
import hl_core
from hl_core import Spec, A, apow
import hl_check as H

SPEC = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'v15fix.r1.json')
res = []

def check(name, cond):
    res.append(cond)
    print('%-60s %s' % (name, 'FIRES (ok)' if cond else 'DOES NOT FIRE (BAD)'))

# 1 bern_min with a NaN coefficient in the last position (all others finite and positive)
P = arb_mat(4, 4); P[0, 0] = arb(5)
P[3, 3] = arb('nan')
check('bern_min: NaN coefficient -> -inf', not H.bern_min(P).is_finite() and H.bern_min(P) < 0)
# 2 fin
check('fin(nan) -> -inf', H.fin(arb('nan')) < 0 and not H.fin(arb('nan')).is_finite())
# 3 APsi_lower_const with a NaN I-value
sp = Spec(SPEC)
orig_I = sp.I_
sp.I_ = lambda d: arb('nan')
v = sp.APsi_lower_const(Fr(1, 2), Fr(1, 8), Fr(17, 32), Fr(5, 32))
check('APsi_lower_const: NaN bound -> -inf', (not v.is_finite()) and v < 0)
sp.I_ = orig_I
# 4 subcell_lower with A Psi constant bound NaN on a sub-cell straddling r = R (no Taylor model there)
ak = H.AKChecker(sp)
sp.APsi_lower_const = lambda *a: arb('nan')
lo, mode = ak.subcell_lower(27, 0, Fr(3, 4), Fr(7, 8), Fr(1, 8), Fr(1, 4))     # u+v from 1.734 to 1.75+: straddles
check('subcell_lower: NaN const bound, no Taylor -> not > 0', not (lo > 0))
del sp.APsi_lower_const
# 5 apow on NaN
try:
    apow(arb('nan'), arb(1.8)); check('apow(nan) raises', False)
except ValueError:
    check('apow(nan) raises', True)
# 6 Spec with a non-canonical class key (J > I)
d = json.load(open(SPEC)); d['a']['3,5'] = '1'
bad = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'G3_bad_key.json')
json.dump(d, open(bad, 'w'))
try:
    Spec(bad); check('Spec rejects key 3,5 (J > I)', False)
except ValueError:
    check('Spec rejects key 3,5 (J > I)', True)
# 7 quad_A: series truncation guard with ctx.cap too small
import quad_A as Q
ctx.prec = 160
ctx.cap = 16
try:
    Q.L1(Q.line_piecewise('pow', Fr(1, 2), Fr(6, 5)), Fr(3, 10), Fr(6, 5))
    check('quad_A L1 raises on truncated series (cap 16)', False)
except RuntimeError:
    check('quad_A L1 raises on truncated series (cap 16)', True)
ctx.cap = 200
print('ALL GUARDS FIRE' if all(res) else 'SOME GUARD DID NOT FIRE')
