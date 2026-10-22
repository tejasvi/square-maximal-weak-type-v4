"""Linear Bernstein constraints guaranteeing K >= 0 everywhere and K >= 1 on D (float rows for the LP).
K = c Psi(r) + S;  on a (sub)cell: S >= min Bernstein coeff; Psi >= Psi(r_max) (decreasing).  Rows: (coeffs over LP
variables, lower bound). Anti-diagonal cells (cut by u+v = 1): degree-6 BB coefficients on the D-triangle >= 1 - c Psi(1)."""
import math
import numpy as np
from math import comb, factorial

_BP = {-2: [8, 12, 6, 1], -1: [4, 0, -6, -3], 0: [4, 0, -6, 3], 1: [8, -12, 6, -1]}


def piece_power(off, t0, t1):
    """power coeffs in local tau (x = t0 + (t1-t0) tau) of B(x - off) on [0,1] local knot interval."""
    m = -off
    p = [c / 6.0 for c in _BP[m]]
    cx = [0.0] * 4
    for k, pk in enumerate(p):
        for j in range(k + 1):
            cx[j] += pk * comb(k, j) * (-off) ** (k - j)
    cs = [0.0] * 4
    dd = t1 - t0
    for k, ck in enumerate(cx):
        for j in range(k + 1):
            cs[j] += ck * comb(k, j) * t0 ** (k - j) * dd ** j
    return np.array(cs)


def power_to_bern3(cs):
    return np.array([sum(comb(i, j) / comb(3, j) * cs[j] for j in range(i + 1)) for i in range(4)])


# triangle BB conversion matrix: tensor power coeffs (x,y) -> BB(6) coefficients on {tau+sigma <= 1}
def _tri_matrix():
    n = 6
    keys = [(a, b, n - a - b) for a in range(n + 1) for b in range(n - a + 1)]
    idx = {k: t for t, k in enumerate(keys)}
    M = np.zeros((len(keys), 4, 4))
    for i in range(4):
        for j in range(4):
            m = n - i - j
            for a in range(m + 1):
                for b in range(m - a + 1):
                    c = m - a - b
                    coef = factorial(m) / (factorial(a) * factorial(b) * factorial(c))
                    key = (a, b + i, c + j)
                    M[idx[key], i, j] += coef
    for t, (a, b, c) in enumerate(keys):
        M[t] /= factorial(n) / (factorial(a) * factorial(b) * factorial(c))
    return M


TRI = _tri_matrix()


_TAU = np.array([0.0, 1 / 3, 2 / 3, 1.0])
_MB = np.array([[comb(3, k) * t ** k * (1 - t) ** (3 - k) for k in range(4)] for t in _TAU])
_MBinv = np.linalg.inv(_MB)


def psi_taylor_bern(alpha, R, u0, u1, v0, v1):
    """tensor Bernstein (3,3) coefficients of the cubic Taylor polynomial of r^-alpha - R^-alpha at the cell centre
    (a LOWER bound of Psi on the cell when u0+v0 > 0, since the 4th derivative of r^-alpha is positive)."""
    uc, vc = (u0 + u1) / 2, (v0 + v1) / 2; du, dv = (u1 - u0) / 2, (v1 - v0) / 2
    rc = uc + vc
    t = [rc ** (-alpha) - R ** (-alpha), -alpha * rc ** (-alpha - 1), alpha * (alpha + 1) * rc ** (-alpha - 2) / 2,
         -alpha * (alpha + 1) * (alpha + 2) * rc ** (-alpha - 3) / 6]
    V = np.zeros((4, 4))
    for i, ta in enumerate(_TAU):
        for j, sg in enumerate(_TAU):
            rho = du * (2 * ta - 1) + dv * (2 * sg - 1)
            V[i, j] = t[0] + t[1] * rho + t[2] * rho ** 2 + t[3] * rho ** 3
    return _MBinv @ V @ _MBinv.T


def rows(P, h, N, R, alpha, U, sub=1):
    """returns list of (dict var->coef, rhs). Variables: class indices (spline) and ncls (singular coefficient)."""
    out = []
    nk = int(round(U / h))
    for i0 in range(nk):
        for j0 in range(i0 + 1):
            for su in range(sub):
                for sv in range(sub):
                    t0, t1 = su / sub, (su + 1) / sub
                    q0, q1 = sv / sub, (sv + 1) / sub
                    u0 = (i0 + t0) * h; u1 = (i0 + t1) * h; v0 = (j0 + q0) * h; v1 = (j0 + q1) * h
                    if v0 > u1:
                        continue
                    rmin, rmax = u0 + v0, u1 + v1
                    psiB = psi_taylor_bern(alpha, R, u0, u1, v0, v1) if (rmin > 0 and rmin < R) else None
                    psi = max(rmax ** (-alpha) - R ** (-alpha), 0.0) if rmax < R else 0.0
                    pu = {i0 + off: piece_power(off, t0, t1) for off in (-1, 0, 1, 2)}
                    pv = {j0 + off: piece_power(off, q0, q1) for off in (-1, 0, 1, 2)}
                    bu = {i: power_to_bern3(c) for i, c in pu.items()}
                    bv = {j: power_to_bern3(c) for j, c in pv.items()}
                    straddle = rmin < 1 - 1e-12 and rmax > 1 + 1e-12
                    target = 1.0 if rmax <= 1 + 1e-12 else 0.0
                    patB = _patch_bern(P, u0, u1, v0, v1)     # list of (column index, 4x4 Bernstein array)
                    for x in range(4):
                        for y in range(4):
                            coef = {}
                            for i, b1 in bu.items():
                                if not -N <= i <= N:
                                    continue
                                for j, b2 in bv.items():
                                    if not -N <= j <= N:
                                        continue
                                    cl = P.clsidx[i + N, j + N]
                                    coef[cl] = coef.get(cl, 0.0) + b1[x] * b2[y]
                            for (col, Bp) in patB:
                                if Bp[x, y] != 0.0:
                                    coef[col] = coef.get(col, 0.0) + Bp[x, y]
                            if psiB is not None:
                                coef[P.ncls] = psiB[x, y]
                            elif psi > 0:
                                coef[P.ncls] = psi
                            out.append((coef, target))
                    if straddle and abs(rmin + (u1 - u0) - 1) < 1e-12 and abs((u1 - u0) - (v1 - v0)) < 1e-12:
                        # Taylor cubic of r^-alpha - R^-alpha in power form of (tau, sigma)
                        uc, vc = (u0 + u1) / 2, (v0 + v1) / 2; du, dv = (u1 - u0) / 2, (v1 - v0) / 2
                        rc = uc + vc
                        tt = [rc ** (-alpha) - R ** (-alpha), -alpha * rc ** (-alpha - 1), alpha * (alpha + 1) * rc ** (-alpha - 2) / 2,
                              -alpha * (alpha + 1) * (alpha + 2) * rc ** (-alpha - 3) / 6]
                        # rho = (-du - dv) + 2 du tau + 2 dv sigma
                        PS = np.zeros((4, 4))
                        base = np.zeros((4, 4)); base[0, 0] = -du - dv; base[1, 0] = 2 * du; base[0, 1] = 2 * dv
                        powk = np.zeros((4, 4)); powk[0, 0] = 1.0
                        for n_ in range(4):
                            PS += tt[n_] * powk
                            # powk *= base (polynomial product, truncated to degree 3 per variable)
                            newp = np.zeros((4, 4))
                            for a_ in range(4):
                                for b_ in range(4):
                                    if powk[a_, b_] == 0:
                                        continue
                                    for c_ in range(2):
                                        for d_ in range(2):
                                            if base[c_, d_] != 0 and a_ + c_ < 4 and b_ + d_ < 4:
                                                newp[a_ + c_, b_ + d_] += powk[a_, b_] * base[c_, d_]
                            powk = newp
                        for t in range(TRI.shape[0]):
                            coef = {}
                            for i, c1 in pu.items():
                                if not -N <= i <= N:
                                    continue
                                for j, c2 in pv.items():
                                    if not -N <= j <= N:
                                        continue
                                    cl = P.clsidx[i + N, j + N]
                                    coef[cl] = coef.get(cl, 0.0) + float(np.sum(TRI[t] * np.outer(c1, c2)))
                            coef[P.ncls] = float(np.sum(TRI[t] * PS))
                            out.append((coef, 1.0))
    return out


def _patch_bern(P, u0, u1, v0, v1):
    """Bernstein (3,3) coefficients on the cell of every B-spline patch column (cell must be aligned to the patch grid)."""
    out = []
    if not getattr(P, 'npatch', 0):
        return out
    from patches import Patches
    off = P.ncls + P.nsing
    for part in P.patches.parts:
        if not isinstance(part, Patches):
            off += part.n
            continue
        for k_, (orb, hh) in enumerate(part.cols):
            Bsum = None
            for (cu, cv) in orb:
                su0, su1 = (u0 - cu) / hh, (u1 - cu) / hh
                sv0, sv1 = (v0 - cv) / hh, (v1 - cv) / hh
                if su1 <= -2 or su0 >= 2 or sv1 <= -2 or sv0 >= 2:
                    continue
                ku, kv = int(np.floor(su0 + 1e-9)), int(np.floor(sv0 + 1e-9))
                # B(s) on [ku, ku+1] is the piece with off = -ku ... B(x - off) with x local in [0,1]: off = -ku
                if not (-2 <= ku <= 1 and -2 <= kv <= 1):
                    continue
                bu_ = power_to_bern3(piece_power(-ku, su0 - ku, su1 - ku))
                bv_ = power_to_bern3(piece_power(-kv, sv0 - kv, sv1 - kv))
                Bt = np.outer(bu_, bv_)
                Bsum = Bt if Bsum is None else Bsum + Bt
            if Bsum is not None:
                out.append((off + k_, Bsum))
        off += part.n
    return out
