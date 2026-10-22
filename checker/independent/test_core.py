"""unit tests for hl_core against independent definitions (exact B-spline sums, F1 double sum, rigorous quadrature)."""
import os
import sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb, acb
import hl_core as H
import quad_A as Q

S = H.Spec(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'v15fix.r1.json'))
h = S.h
random.seed(5)

def Bdef(x):            # DEFS.md definition
    ax = abs(x)
    if ax <= 1: return (4 - 6 * x * x + 3 * ax ** 3) / 6
    if ax <= 2: return (2 - ax) ** 3 / 6
    return Fr(0)

def S_direct(u, v):
    tot = Fr(0)
    for i in range(-S.N, S.N + 1):
        bi = Bdef(u / h - i)
        if bi == 0: continue
        for j in range(-S.N, S.N + 1):
            bj = Bdef(v / h - j)
            if bj: tot += S.coef(i, j) * bi * bj
    return tot

print("(a) S_point vs DEFS definition, (b) Bezier net evaluation")
for _ in range(6):
    u = Fr(random.randint(0, 2400), 1000) + Fr(1, 9973); v = Fr(random.randint(0, 2400), 1000) + Fr(1, 9967)
    s1 = S.S_point(u, v); s2 = S_direct(u, v)
    p = int((u / h) // 1); q = int((v / h) // 1); x = u / h - p; y = v / h - q
    bz = S.S_bezier(p, q)
    from math import comb
    s3 = sum(bz[k][l] * comb(3, k) * x ** k * (1 - x) ** (3 - k) * comb(3, l) * y ** l * (1 - y) ** (3 - l) for k in range(4) for l in range(4))
    print(f"  ({float(u):.4f},{float(v):.4f}): S_point==direct {s1 == s2}, bezier==direct {s3 == s2}, value {float(s2):.6f}")

print("(c) AS_point vs F1 double sum")
for _ in range(4):
    u = Fr(random.randint(0, 2400), 1000) + Fr(1, 9973); v = Fr(random.randint(0, 2400), 1000) + Fr(1, 9967)
    A1, A2 = S.AS_point(u, v)
    d1 = arb(0); d2 = arb(0)
    hA = H.A(h)
    for i in range(-S.N, S.N + 1):
        for j in range(-S.N, S.N + 1):
            cij = S.coef(i, j)
            if cij == 0: continue
            bj = Bdef(v / h - j); bi = Bdef(u / h - i)
            if bj: d1 += H.A(cij) * Q.F1(u / h - i, S.alpha) * H.A(bj)
            if bi: d2 += H.A(cij) * Q.F1(v / h - j, S.alpha) * H.A(bi)
    d1 *= H.pw(hA, -S.a_); d2 *= H.pw(hA, -S.a_)
    print(f"  ({float(u):.4f},{float(v):.4f}): A1S {A1.str(12)} vs {d1.str(12)} | A2S {A2.str(12)} vs {d2.str(12)}")

print("(d) A1S vs rigorous quadrature of the definition on the slice S(., v)")
def slice_piecewise(v):
    q = int((v / h) // 1); y = v / h - q
    by = H.basis(y)
    bps = [Fr(k) * h for k in range(-S.maxidx - 3, S.maxidx + 4)]
    branches = []
    def mkpoly(p):
        # S(u, v) on u-interval [p h, (p+1) h] as a polynomial in u (exact coefficients via local x = u/h - p)
        cs = [sum(S.coef(p - 1 + i, q - 1 + j) * H.NPOLY[i][d] * by[j] for i in range(4) for j in range(4)) for d in range(4)]
        def f(z, an=None, cs=cs, p=p):
            x = z / H.A(h) - p
            return H.A(cs[0]) + x * (H.A(cs[1]) + x * (H.A(cs[2]) + x * H.A(cs[3])))
        return f
    branches.append(lambda z, an=None: z * 0)
    for k in range(len(bps) - 1):
        p = -S.maxidx - 3 + k
        branches.append(mkpoly(p))
    branches.append(lambda z, an=None: z * 0)
    return Q.Piecewise(bps, branches, lambda i, s0: Fr(10), lambda x0, Aend: arb(0))
for _ in range(3):
    u = Fr(random.randint(0, 2400), 1000) + Fr(1, 9973); v = Fr(random.randint(0, 2400), 1000) + Fr(1, 9967)
    A1, A2 = S.AS_point(u, v)
    qv = Q.L1(slice_piecewise(v), u, S.alpha)
    print(f"  ({float(u):.4f},{float(v):.4f}): A1S formula {A1.str(14)}  quad {qv.str(14)}  diff {(A1 - qv).str(3)}", flush=True)

print("(e) A Psi closed forms vs rigorous quadrature")
for (u, v) in [(Fr(4, 10) + Fr(1, 997), Fr(1, 10) + Fr(1, 991)), (Fr(13, 10) + Fr(1, 997), Fr(2, 10) + Fr(1, 991)),
               (Fr(19, 10) + Fr(1, 997), Fr(3, 10) + Fr(1, 991)), (Fr(12, 10) + Fr(1, 997), Fr(11, 10) + Fr(1, 991)),
               (Fr(23, 10) + Fr(1, 997), Fr(1, 100) + Fr(1, 991))]:
    cf = S.APsi_point(u, v)
    qd = Q.A2('psi', u, v, S.alpha, S.R)
    print(f"  ({float(u):.4f},{float(v):.4f}) r={float(u+v):.3f}: closed {cf.str(14)}  quad {qd.str(14)}  diff {(cf - qd).str(3)}", flush=True)
