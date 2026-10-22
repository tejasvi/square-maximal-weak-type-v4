"""tests of the outside A Psi pieces: M_{p,q} vs quadrature; J derivatives vs finite differences; the quadratic model
+ remainder contains APsi_outside at random points of random outside sub-cells."""
import os
import sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb, acb, ctx
from hl_core import Spec, A, pw
import hl_check as H
ctx.prec = 128
SPEC = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'v15fix.r1.json')
sp = Spec(SPEC)
print('spec', SPEC, 'alpha', sp.alpha, 'R', sp.R, 'h', sp.h)
RR = sp.R
PTS = [(RR * Fr(7, 10), RR * Fr(4, 10)), (RR * Fr(99, 100), RR * Fr(1, 20)), (RR * Fr(3, 10), RR * Fr(9, 10)),
       (RR * Fr(11, 20), RR * Fr(11, 20)), (RR * Fr(68, 100), RR * Fr(36, 100))]
ak = H.AKChecker(sp)
a = sp.a_; Rr = sp.RA
def Mquad(x, y, p, q):
    X = acb(A(x)); Y = acb(A(y)); L = acb(Rr) - Y
    f = lambda t, an: (t + Y).pow(acb(-p), analytic=an) * ((X - t).pow(acb(-q), analytic=an) + (X + t).pow(acb(-q), analytic=an))
    return acb.integral(f, 0, L).real
bad = 0
for (x, y) in PTS:
    for (p_, q_) in [(a, 1 + a), (a, 4 + a), (a + 1, 3 + a), (a + 2, 2 + a), (a + 3, 1 + a)]:
        cf = ak.Mpq(A(x), A(y), p_, q_); qd = Mquad(x, y, p_, q_)
        ok = abs((cf - qd).mid()) <= 1e-20 * max(1, abs(qd.mid())) + qd.rad() + cf.rad()
        bad += (not ok)
        print('M(%s,%s) p=%.1f q=%.1f closed %s quad %s %s' % (x, y, float(p_.mid()), float(q_.mid()), cf.str(12), qd.str(12), 'OK' if ok else 'MISMATCH'))
print('M mismatches', bad)
# J derivatives vs FD (central differences, step 1e-6)
bad = 0
for (x, y) in PTS[:2] + PTS[2:3] + PTS[4:]:
    X = A(x); Y = A(y); eps = A(Fr(1, 10**6))
    J0, Jx, Jy, Jxx, Jxy, Jyy = ak.J_derivs(X, Y)
    J = lambda X_, Y_: ak.Jq(X_, Y_, 1 + a)
    fdx = (J(X + eps, Y) - J(X - eps, Y)) / (2 * eps)
    fdy = (J(X, Y + eps) - J(X, Y - eps)) / (2 * eps)
    fdxx = (J(X + eps, Y) - 2 * J0 + J(X - eps, Y)) / eps ** 2
    fdyy = (J(X, Y + eps) - 2 * J0 + J(X, Y - eps)) / eps ** 2
    fdxy = (J(X + eps, Y + eps) - J(X + eps, Y - eps) - J(X - eps, Y + eps) + J(X - eps, Y - eps)) / (4 * eps ** 2)
    J0b = sp.J(X, Y)
    for nm, v1, v2 in [('J', J0, J0b), ('Jx', Jx, fdx), ('Jy', Jy, fdy), ('Jxx', Jxx, fdxx), ('Jyy', Jyy, fdyy), ('Jxy', Jxy, fdxy)]:
        rel = abs(float((v1 - v2).mid())) / max(1e-12, abs(float(v1.mid())))
        ok = rel < 1e-6
        bad += (not ok)
        print('  (%s,%s) %s: %s vs %s rel %.2e %s' % (x, y, nm, v1.str(10), v2.str(10), rel, 'OK' if ok else 'BAD'))
print('J derivative mismatches', bad)
# model containment
rnd = random.Random(7)
bad = 0; worst = 0; n = 0
while n < 400:
    p = rnd.randint(int(sp.R / sp.h / 2), sp.maxidx + 2); q = rnd.randint(0, p)
    i = rnd.randint(0, len(H.GRID) - 2); j = rnd.randint(0, len(H.GRID) - 2)
    x0, x1, y0, y1 = H.GRID[i], H.GRID[i + 1], H.GRID[j], H.GRID[j + 1]
    h = sp.h
    u0 = h * (p + x0); u1 = h * (p + x1); v0 = h * (q + y0); v1 = h * (q + y1)
    if not (u0 + v0 > sp.R and v0 > 0 and u0 > 0 and (u1 < sp.R or u0 >= sp.R) and (v1 < sp.R or v0 >= sp.R)):
        continue
    n += 1
    P, rem = ak.APsi_out_taylor(p, q, x0, x1, y0, y1)
    for _ in range(4):
        xi = Fr(rnd.randint(-1000, 1000), 1000); eta = Fr(rnd.randint(-1000, 1000), 1000)
        if _ < 3:
            xi, eta = [(Fr(-1), Fr(-1)), (Fr(1), Fr(-1)), (Fr(-1), Fr(1))][_]
        u = (u0 + u1) / 2 + (u1 - u0) / 2 * xi; v = (v0 + v1) / 2 + (v1 - v0) / 2 * eta
        true = sp.APsi_outside(A(u), A(v))
        mod = sum(P[k, l] * A(xi) ** k * A(eta) ** l for k in range(4) for l in range(4))
        diff = abs(mod - true)
        if not (diff.upper() <= rem.upper()):
            bad += 1
            print('violation', p, q, x0, x1, y0, y1, xi, eta, diff.str(5), rem.str(5))
        worst = max(worst, float(diff.mid()) / max(1e-300, float(rem.mid())))
print('outside model violations:', bad, ' max |model-true|/rem = %.3g' % worst)
