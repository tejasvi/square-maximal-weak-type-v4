#!/usr/bin/env python3
"""Audit (47a): rigorous quadrature of the jump operator from its DEFINITION, for spot checks of F1-F4.

For a 1D function phi given by analytic pieces (breakpoints s_1 < ... < s_n, an analytic branch on each interval),
    L[phi](x0) := int_R [phi(x0+t) + phi(x0-t) - 2 phi(x0)] |t|^{-1-alpha} dt = 2 int_0^inf g(t) t^{-1-alpha} dt.
  [0, delta]  : g = sum_k c_2k t^2k from the Taylor series of the branch at x0 (arb_series), tail bounded by Cauchy:
                |c_2k| <= M rho^-2k, M = sup_{|t| <= rho} |g(t)| (acb ball), integrated termwise exactly;
  [delta, A]  : acb.integral (rigorous; branch-aware powers) on segments where x0 +- t cross no breakpoint;
  [A, inf)    : exact -2 phi(x0) A^-alpha/alpha plus [0, bound] for the nonnegative remainder (0 if phi has compact support).
The 2D operator is A f(u,v) = L[f(., v)](u) + L[f(u, .)](v).
Usage: quad_A.py spotcheck SPEC.json NPTS SEED
"""
import json, math, random, sys
from fractions import Fraction as Fr

from flint import arb, acb, arb_series, ctx

ctx.prec = 160
ctx.cap = 200      # IMPORTANT: python-flint silently caps power-series lengths at ctx.cap (default 10)


def A(x):
    x = Fr(x)
    return arb(x.numerator) / x.denominator


class Piecewise:
    """phi on R: sorted breakpoints bps, branches[i] valid on (bps[i-1], bps[i]) (i = 0..n), each a function
    br(z, analytic) -> acb for complex z, plus sing[i] = distance-to-singularity function for the Cauchy radius,
    and 'decay' = None (compact support beyond the outer breakpoints, branch 0 there) or a callable tail bound."""

    def __init__(self, bps, branches, radius, tail):
        self.bps = bps
        self.branches = branches
        self.radius = radius        # radius(i, s0) -> arb lower bound of the analyticity radius of branch i around s0
        self.tail = tail            # tail(x0, A) -> (exact_part_coefficient flag, upper bound of int_A^inf [phi(x0+t)+phi(x0-t)] t^{-1-a})

    def idx(self, s):
        """index of the piece containing the real number s (s must not be a breakpoint)."""
        i = 0
        while i < len(self.bps) and s > self.bps[i]:
            i += 1
        return i


def L1(phi, x0, alpha, eps=Fr(1, 10**30)):
    """rigorous enclosure of int_R [phi(x0+t)+phi(x0-t)-2phi(x0)] |t|^{-1-alpha} dt.  x0 rational (Fraction), not a breakpoint."""
    a = A(alpha)
    x0f = Fr(x0)
    X0 = A(x0f)
    i0 = phi.idx(x0f)
    br0 = phi.branches[i0]
    f0 = br0(acb(X0), False).real
    # breakpoints in t
    tb = sorted(set(abs(Fr(b) - x0f) for b in phi.bps if Fr(b) != x0f))
    dmin = tb[0] if tb else Fr(1)
    rho = phi.radius(i0, x0f)                      # Fraction
    rho = min(rho, Fr(4))
    delta = min(dmin, rho) / 3
    # --- [0, delta]: Taylor ---
    K = 60
    T = arb_series([X0, 1], prec=2 * K + 2)
    Tm = arb_series([X0, -1], prec=2 * K + 2)
    sp = br0(T, None)
    sm = br0(Tm, None)
    cp = sp.coeffs(); cm = sm.coeffs()
    # a polynomial branch may legitimately have fewer coefficients; a transcendental one must have all 2K+2
    if len(cp) < 2 * K + 1 or len(cm) < 2 * K + 1:
        poly = all(c.is_zero() for c in (cp[4:] + cm[4:])) and len(cp) <= 4 and len(cm) <= 4
        if not poly:
            raise RuntimeError("series truncated: %d %d" % (len(cp), len(cm)))
    near = arb(0)
    for k in range(1, K + 1):
        c2k = (cp[2 * k] if 2 * k < len(cp) else arb(0)) + (cm[2 * k] if 2 * k < len(cm) else arb(0))
        near += c2k * pw(A(delta), 2 * k - a) / (2 * k - a)
    # Cauchy bound on the disc |t| <= rho2 (rho2 = 2 delta... use rho' = (rho + delta)/2 > delta)
    rho2 = (rho + 2 * delta) / 3 if rho > 2 * delta else rho * Fr(9, 10)
    disc = acb(X0, 0) + acb(arb(0, float(rho2)), arb(0, float(rho2)))
    M = abs(br0(disc, True)) + abs(br0(acb(2 * X0) - disc, True)) + 2 * abs(f0)     # analytic=True: nan if a cut is touched
    q = A(delta) / A(rho2)
    tailT = M.upper() * pw(A(delta), -a) * q ** (2 * K + 2) / ((2 * K + 2 - a) * (1 - q * q))
    near += arb(0, tailT.upper())
    # --- [delta, A_end]: acb.integral segments ---
    Aend = (tb[-1] if tb else Fr(0)) + 4
    if phi.tail(x0f, Aend) > 0:          # non-compact support: push the cut far out (crude tail bound is then tiny)
        Aend = Fr(10 ** 8)
    pts = [delta] + [b for b in tb if b > delta] + [Aend]
    mid = arb(0)
    for ta, tbnd in zip(pts[:-1], pts[1:]):
        tm = (ta + tbnd) / 2
        ip = phi.idx(x0f + tm)
        im = phi.idx(x0f - tm)
        bp, bm = phi.branches[ip], phi.branches[im]

        def integrand(z, analytic, bp=bp, bm=bm):
            return (bp(acb(X0) + z, analytic) + bm(acb(X0) - z, analytic) - 2 * f0) * z.pow(-1 - a, analytic=analytic)
        val = acb.integral(integrand, A(ta), A(tbnd), rel_tol=arb(2) ** (-100), abs_tol=arb(2) ** (-120))
        mid += val.real
    # --- [A_end, inf) ---
    exact = -2 * f0 * pw(A(Aend), -a) / a
    tb_hi = phi.tail(x0f, Aend)
    tail = exact + arb(0, tb_hi / 2) + tb_hi / 2 if tb_hi > 0 else exact
    return 2 * (near + mid + tail)


def pw(x, e):
    """x^e for arb x > 0 (avoid ** with arb exponents)."""
    return (e * x.log()).exp()


# ---------------- concrete functions ----------------
def bspline_piecewise():
    """centred cubic B-spline, knots -2..2."""
    def p_out(z, an=None):
        return z * 0
    def p_m2(z, an=None):      # -2 <= s <= -1 : (2 + s)^3/6
        w = z + 2
        return w * w * w / 6
    def p_m1(z, an=None):      # -1 <= s <= 0 : (4 - 6 s^2 - 3 s^3)/6
        return (4 - 6 * z * z - 3 * z * z * z) / 6
    def p_p1(z, an=None):      # 0 <= s <= 1 : (4 - 6 s^2 + 3 s^3)/6
        return (4 - 6 * z * z + 3 * z * z * z) / 6
    def p_p2(z, an=None):      # 1 <= s <= 2 : (2 - s)^3/6
        w = 2 - z
        return w * w * w / 6
    br = [p_out, p_m2, p_m1, p_p1, p_p2, p_out]
    return Piecewise([-2, -1, 0, 1, 2], br, lambda i, s0: Fr(10), lambda x0, Aend: arb(0))


def line_piecewise(h_kind, c, alpha, R=None):
    """phi(s) = h(|s| + c), c > 0, h(r) = r^-alpha ('pow') or (r^-alpha - R^-alpha)_+ ('psi')."""
    a = A(alpha)
    C = A(c)

    def mk(sign, cut):
        if cut:
            return lambda z, an=None: z * 0
        def f(z, an=None):
            w = (z if sign > 0 else -z) + C
            if isinstance(w, arb_series):
                v = (w.log() * (-a)).exp()
            else:
                v = w.pow(-a, analytic=bool(an))
            if h_kind == 'psi':
                v = v - pw(A(R), -a)
            return v
        return f

    if h_kind == 'pow':
        bps = [0]
        br = [mk(-1, False), mk(1, False)]
        def tail(x0, Aend):
            a_ = A(alpha)
            return (2 * pw(A(Aend - abs(x0)), -a_) * pw(A(Aend), -a_) / a_).upper()
        return Piecewise(bps, br, lambda i, s0: abs(Fr(s0)) + Fr(c), tail)
    else:
        Rf = Fr(R)
        if Fr(c) >= Rf:
            return Piecewise([0], [lambda z, an=None: z * 0] * 2, lambda i, s0: Fr(10), lambda x0, Aend: arb(0))
        e = Rf - Fr(c)
        bps = [-e, 0, e]
        br = [mk(-1, True), mk(-1, False), mk(1, False), mk(1, True)]
        return Piecewise(bps, br, lambda i, s0: abs(Fr(s0)) + Fr(c), lambda x0, Aend: arb(0))


def A2(h_kind, u, v, alpha, R=None):
    """A f(u,v) for f = h(|u|+|v|): line in u (c = |v|) + line in v (c = |u|)."""
    return L1(line_piecewise(h_kind, abs(Fr(v)), alpha, R), Fr(u), alpha) + \
        L1(line_piecewise(h_kind, abs(Fr(u)), alpha, R), Fr(v), alpha)


# ---------------- closed forms (F1-F4) for comparison ----------------
def F1(s, alpha):
    a = A(alpha)
    kap = -2 / (a * (1 - a) * (2 - a) * (3 - a))
    w = [1, -4, 6, -4, 1]
    tot = arb(0)
    for k, wk in zip(range(-2, 3), w):
        d = abs(A(Fr(s) - k))
        tot += wk * (pw(d, 3 - a) if d > 0 else arb(0))
    return kap * tot


def Calpha(alpha):
    a = A(alpha)
    return -8 * (1 - a).gamma() * (2 * a).gamma() * (arb.pi() * a / 2).cos() ** 2 / (a + 1).gamma()


def Ifun(d, alpha, R):
    """I(d) = R^-a d^-a / a - d^-2a 2F1(a, 2a; 2a+1; -(R-d)/d) / (2a)."""
    a = A(alpha); Rr = A(R); D = A(d)
    z = -(Rr - D) / D
    F = acb(z).hypgeom_2f1(acb(a), acb(2 * a), acb(2 * a + 1), bc=True).real     # z.hypgeom_2f1(a, b, c); b - c = -1 exactly
    return pw(Rr, -a) * pw(D, -a) / a - pw(D, -2 * a) * F / (2 * a)


def F3(u, v, alpha, R):
    a = A(alpha)
    U, V, Rr = A(u), A(v), A(R)
    r = U + V
    return Calpha(alpha) * pw(r, -2 * a) + 4 * Ifun(Fr(R) - Fr(u) - Fr(v), alpha, R) + \
        2 * Ifun(Fr(R) + Fr(u) - Fr(v), alpha, R) + 2 * Ifun(Fr(R) + Fr(v) - Fr(u), alpha, R)


def main():
    mode = sys.argv[1]
    if mode == "spotcheck":
        spec = json.load(open(sys.argv[2]))
        n = int(sys.argv[3]); random.seed(int(sys.argv[4]))
        alpha = Fr(spec["alpha"]); R = Fr(spec["R"])
        print(f"alpha = {alpha}, R = {R}; C_alpha = {Calpha(alpha).str(15)}")
        # F1
        for _ in range(n):
            s = Fr(random.randint(-3000, 3000), 1000) + Fr(1, 7919)
            q = L1(bspline_piecewise(), s, alpha)
            c = F1(s, alpha)
            print(f"F1 s={float(s):+.4f}: quad {q.str(18)}  closed {c.str(18)}  diff {(q - c).str(3)}", flush=True)
        # F2 (r^-alpha)
        for _ in range(n):
            u = Fr(random.randint(50, 2500), 1000) + Fr(1, 7919); v = Fr(random.randint(5, 2500), 1000) + Fr(1, 6007)
            q = A2('pow', u, v, alpha)
            c = Calpha(alpha) * pw(A(u + v), -2 * A(alpha))
            print(f"F2 (u,v)=({float(u):.4f},{float(v):.4f}): quad {q.str(18)}  closed {c.str(18)}  diff {(q - c).str(3)}", flush=True)
        # F3 (Psi inside)
        cnt = 0
        while cnt < n:
            u = Fr(random.randint(20, 1700), 1000) + Fr(1, 7919); v = Fr(random.randint(5, 1700), 1000) + Fr(1, 6007)
            if u < v:
                u, v = v, u
            if u + v >= R - Fr(1, 100):
                continue
            cnt += 1
            q = A2('psi', u, v, alpha, R)
            c = F3(u, v, alpha, R)
            print(f"F3 (u,v)=({float(u):.4f},{float(v):.4f}): quad {q.str(18)}  closed {c.str(18)}  diff {(q - c).str(3)}", flush=True)
        # F4 (Psi outside): quad vs monotonicity (value decreasing in u and v)
        cnt = 0
        while cnt < n:
            u = Fr(random.randint(100, 2500), 1000) + Fr(1, 7919); v = Fr(random.randint(5, 1700), 1000) + Fr(1, 6007)
            if u < v:
                u, v = v, u
            if u + v <= R + Fr(1, 100):
                continue
            cnt += 1
            q0 = A2('psi', u, v, alpha, R)
            qu = A2('psi', u + Fr(1, 50), v, alpha, R)
            qv = A2('psi', u, v + Fr(1, 50), alpha, R)
            print(f"F4 (u,v)=({float(u):.4f},{float(v):.4f}): A Psi {q0.str(12)} >= 0: {q0 > 0}; decreasing in u: {qu < q0}, "
                  f"in v: {qv < q0}", flush=True)


if __name__ == "__main__":
    main()
