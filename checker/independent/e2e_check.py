#!/usr/bin/env python3
"""End-to-end spot check (47a audit): A K(u,v) by rigorous quadrature of the DEFINITION of A applied to the actual kernel
K = c Psi + S of a spec (1D quadrature of the spline lines S(., v), S(u, .) and of the Psi lines, quad_A.L1), compared with
the closed-form evaluation used by hl_check.py (delta-form of F1 for A S, F3/F4 for A Psi).
usage: e2e_check.py SPEC u1,v1 u2,v2 ...   (u, v rationals, e.g. 19.277/16)"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb, acb, arb_series, ctx
import hl_core as HC                      # sets prec 128 / cap 16 ...
import quad_A as Q                        # ... then prec 160 / cap 200 (needed by the Taylor part of L1)
ctx.prec = 160
ctx.cap = 200


def spline_line(sp, which, w):
    """S(., w) (which='u': S(s, w)) or S(w, .) as a quad_A.Piecewise in the free variable s."""
    h = sp.h
    k0 = int((w / h) // 1); y = w / h - k0
    by = HC.basis(y)
    N = sp.N
    b = {}
    for i in range(-N - 2, N + 3):
        val = sum(sp.coef(i, k0 - 1 + jj) * by[jj] for jj in range(4))     # D4 symmetry: S(s,w) and S(w,s) same lines
        if val != 0:
            b[i] = val
    if not b:
        return Q.Piecewise([0], [lambda z, an=None: z * 0] * 2, lambda i, s0: Fr(10), lambda x0, Aend: arb(0))
    kmin = min(b) - 2; kmax = max(b) + 2
    bps = [h * k for k in range(kmin, kmax + 1)]
    branches = [lambda z, an=None: z * 0]
    for k in range(kmin, kmax):
        # power coefficients in local x = s/h - k
        co = [sum(b.get(k - 1 + ii, Fr(0)) * HC.NPOLY[ii][d] for ii in range(4)) for d in range(4)]
        def br(z, an=None, co=co, k=k):
            x = z / Q.A(h) - k
            return ((Q.A(co[3]) * x + Q.A(co[2])) * x + Q.A(co[1])) * x + Q.A(co[0])
        branches.append(br)
    branches.append(lambda z, an=None: z * 0)
    return Q.Piecewise(bps, branches, lambda i, s0: Fr(10), lambda x0, Aend: arb(0))


def AK_quad(sp, u, v):
    alpha = sp.alpha
    AS = Q.L1(spline_line(sp, 'u', v), u, alpha) + Q.L1(spline_line(sp, 'v', u), v, alpha)
    APsi = Q.A2('psi', u, v, alpha, sp.R)
    return AS, APsi


def main():
    sp = HC.Spec(sys.argv[1])
    for pt in sys.argv[2:]:
        us, vs = pt.split(',')
        u = Fr(us.split('/')[0]) / (Fr(us.split('/')[1]) if '/' in us else 1)
        v = Fr(vs.split('/')[0]) / (Fr(vs.split('/')[1]) if '/' in vs else 1)
        AS_q, APsi_q = AK_quad(sp, u, v)
        a1, a2 = sp.AS_point(u, v)
        AS_c = a1 + a2
        APsi_c = sp.APsi_point(u, v)
        AKq = AS_q + sp.cA * APsi_q
        AKc = AS_c + sp.cA * APsi_c
        print('(u,v)=(%.6f,%.6f) r=%.6f' % (float(u), float(v), float(u + v)))
        print('   A S   quad %s  closed %s  diff %s' % (AS_q.str(15), AS_c.str(15), (AS_q - AS_c).str(3)))
        print('   A Psi quad %s  closed %s  diff %s' % (APsi_q.str(15), APsi_c.str(15), (APsi_q - APsi_c).str(3)))
        print('   A K   quad %s  closed %s  agree: %s  positive: %s' % (AKq.str(12), AKc.str(12),
              (AKq - AKc).contains(0) or abs(float((AKq - AKc).mid())) < 1e-15, AKq > 0), flush=True)


if __name__ == '__main__':
    main()
