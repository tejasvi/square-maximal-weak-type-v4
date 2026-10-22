"""tests for hl_check.py models: (1) I^(k) closed form vs finite differences / quadrature of the defining integral;
(2) A S polynomial model + remainder contains the exact point values (AS_point) at random points of random sub-cells;
(3) A Psi Taylor model + remainder contains APsi_inside at random points; (4) Bernstein min <= polynomial values."""
import os
import sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb, acb, arb_mat, ctx
from hl_core import Spec, A, pw
import hl_check as H

ctx.prec = 128
SPEC = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'v15fix.r1.json')
sp = Spec(SPEC)
print('spec', SPEC, 'alpha', sp.alpha, 'R', sp.R, 'h', sp.h)
PMAX = sp.maxidx + 1
ak = H.AKChecker(sp)
a = sp.a_; Rr = sp.RA

# (1) I^(k)(d) vs direct quadrature of (-1)^k (1+a)_k int_0^inf g(s) (d+s)^{-1-a-k} ds, g = R^-a - (R+s)^-a
def Iquad(k, d):
    D = A(d)
    poch = arb(1)
    for t in range(1, k + 1):
        poch *= (t + a)
    f = lambda s, an: (acb(Rr.mid()) ** (-acb(a)) - (acb(Rr) + s) ** (-acb(a))) * (acb(D) + s) ** (-1 - acb(a) - k)
    # split [0,1], [1, 1e6] + tail bound
    v = acb.integral(lambda s, an: (pw(Rr, -a) - (Rr + s).pow(-a, analytic=an)) * (D + s).pow(-1 - a - k, analytic=an) if False else
                     (acb(pw(Rr, -a)) - (acb(Rr) + s).pow(acb(-a), analytic=an)) * (acb(D) + s).pow(acb(-1 - a - k), analytic=an), 0, 1)
    v += acb.integral(lambda s, an: (acb(pw(Rr, -a)) - (acb(Rr) + s).pow(acb(-a), analytic=an)) * (acb(D) + s).pow(acb(-1 - a - k), analytic=an), 1, 10**6)
    tail = pw(Rr, -a) * pw(A(10**6) + D, -a - k) / (a + k)       # 0 <= integrand <= R^-a (d+s)^{-1-a-k}
    return (-1) ** k * poch * (v.real + arb(0).union(tail))

bad = 0
for d in [Fr(1, 100), Fr(1, 7), sp.R * Fr(3, 7), sp.R, sp.R * Fr(10, 7), sp.R * Fr(12, 7)]:
    for k in range(5):
        cf = ak.Ik(k, d); qd = Iquad(k, d)
        ok = (cf - qd).contains(0) or abs((cf - qd).mid()) < 1e-25 * max(1, abs(cf.mid()))
        if not ok: bad += 1
        print('I^(%d)(%s): closed %s quad %s %s' % (k, d, cf.str(12), qd.str(12), 'OK' if ok else 'MISMATCH'))
print('(1) mismatches:', bad)

# (2) A S model
rnd = random.Random(5)
def rnd_sub():
    p = rnd.randint(0, PMAX); q = rnd.randint(0, p)
    i = rnd.randint(0, len(H.GRID) - 2); j = rnd.randint(0, len(H.GRID) - 2)
    return p, q, H.GRID[i], H.GRID[i + 1], H.GRID[j], H.GRID[j + 1]
bad = 0; worst = 0
for trial in range(60):
    p, q, x0, x1, y0, y1 = rnd_sub()
    P, rem = ak.AS_model(p, q, x0, x1, y0, y1)
    for _ in range(4):
        xi = Fr(rnd.randint(-1000, 1000), 1000); eta = Fr(rnd.randint(-1000, 1000), 1000)
        if trial % 5 == 0:
            xi = Fr(rnd.choice([-1, 1])); eta = Fr(rnd.choice([-1, 1]))
        x = (x0 + x1) / 2 + (x1 - x0) / 2 * xi; y = (y0 + y1) / 2 + (y1 - y0) / 2 * eta
        u = sp.h * (p + x); v = sp.h * (q + y)
        A1, A2 = sp.AS_point(u, v)
        true = A1 + A2
        mod = sum(P[k, l] * A(xi) ** k * A(eta) ** l for k in range(4) for l in range(4))
        diff = abs(mod - true)
        if not (diff.upper() <= rem.upper()):
            bad += 1
            print('AS model violation', p, q, x0, x1, y0, y1, xi, eta, diff, rem)
        worst = max(worst, float(diff.mid()) / max(1e-300, float(rem.mid())))
print('(2) A S model violations:', bad, ' max |model-true|/rem = %.3g' % worst)

# (3) A Psi Taylor model
bad = 0; worst = 0; n = 0
while n < 40:
    p, q, x0, x1, y0, y1 = rnd_sub()
    z0 = sp.h * (p + q + x0 + y0); z1 = sp.h * (p + q + x1 + y1)
    if not (z0 > 0 and z1 < sp.R):
        continue
    n += 1
    P, rem = ak.APsi_taylor(p, q, x0, x1, y0, y1)
    for _ in range(4):
        xi = Fr(rnd.randint(-1000, 1000), 1000); eta = Fr(rnd.randint(-1000, 1000), 1000)
        x = (x0 + x1) / 2 + (x1 - x0) / 2 * xi; y = (y0 + y1) / 2 + (y1 - y0) / 2 * eta
        u = sp.h * (p + x); v = sp.h * (q + y)
        true = sp.APsi_inside(A(u), A(v))
        mod = sum(P[k, l] * A(xi) ** k * A(eta) ** l for k in range(4) for l in range(4))
        diff = abs(mod - true)
        if not (diff.upper() <= rem.upper()):
            bad += 1
            print('APsi model violation', p, q, x0, x1, y0, y1, xi, eta, diff, rem)
        worst = max(worst, float(diff.mid()) / max(1e-300, float(rem.mid())))
print('(3) A Psi model violations:', bad, ' max |model-true|/rem = %.3g' % worst)

# (4) Bernstein min <= values
bad = 0
for _ in range(200):
    P = arb_mat([[arb(rnd.uniform(-3, 3)) for _ in range(4)] for _ in range(4)])
    lo = H.bern_min(P)
    for _ in range(20):
        xi = rnd.uniform(-1, 1); eta = rnd.uniform(-1, 1)
        val = sum(P[k, l] * arb(xi) ** k * arb(eta) ** l for k in range(4) for l in range(4))
        if val < lo:
            bad += 1
print('(4) Bernstein violations:', bad)
