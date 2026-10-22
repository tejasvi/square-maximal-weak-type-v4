# Local minima of A K near given start points for a certificate, by point evaluation with the closed forms of the
# release copy of the second program (hl_core) and a coarse-to-fine pattern search. usage: localmin.py REPO CERT u v
import sys, os
R, CERT = sys.argv[1], sys.argv[2]
sys.path.insert(0, os.path.join(R, 'checker', 'independent'))
from fractions import Fraction as Fr
from hl_core import Spec
sp = Spec(CERT)
def AK(u, v):
    a1, a2 = sp.AS_point(u, v)
    return a1 + a2 + sp.cA * sp.APsi_point(u, v)
u0, v0 = Fr(sys.argv[3]), Fr(sys.argv[4])
step = Fr(1, 2048)
val0 = AK(u0, v0)
print('start (%s, %s): %s' % (u0, v0, val0.str(10)), flush=True)
for it in range(7):
    cands = []
    for i in range(-8, 9):
        for j in range(-8, 9):
            u = u0 + i * step; v = v0 + j * step
            if v <= 0 or u <= 0 or u + v == sp.R:
                continue
            val = AK(u, v)
            cands.append((float(val.mid()), u, v, val))
    cands.sort(key=lambda t: t[0])
    _, u0, v0, val = cands[0]
    print('step %s: min %s at (%s, %s) = (%.7f, %.7f)' % (step, val.str(10), u0, v0, float(u0), float(v0)), flush=True)
    step = step / 4
