"""Exact (rational) lower bound for the weak-type ratio of a periodic point-mass configuration.

For any finite set S of mass points and rho_S <= sqrt(mu(S)/(4 lam)), every x in the rectangle
R_S = intersection over p in S of the closed squares Q(p, rho_S) has Q(x, rho_S) containing S, hence
mu(Q(x, rho_S)) >= mu(S) >= 4 lam rho_S^2, i.e. M mu(x) >= lam. So the union of the R_S is contained in
{M mu >= lam}, and lam * |union inside one period cell| / mu(cell) is a lower bound for the ratio of the periodic
measure (and for c_2, after the standard truncation and smoothing limits).

Here every rho_S is a rational number strictly below sqrt(mu(S)/(4 lam)) (integer square root at denominator D, minus
1/D), S runs over
the configuration points inside axis boxes whose bounds are point coordinates and whose sides are <= reach, and the
area of the union inside the cell is computed exactly with fractions.
Usage: python -I check_exact.py CONFIG.json [--reach R] [--D 2^40]
CONFIG: {"lam": "1", "Px": "a/b", "Py": "a/b", "pts": [["x", "y", "m"], ...]} (rationals as strings), cell [0,Px)x[0,Py).
"""
import sys, json, math, argparse
from fractions import Fraction as F


def isqrt_frac_lower(q, D):
    """largest k/D with (k/D)^2 <= q (q >= 0 rational)."""
    num = q.numerator * D * D
    den = q.denominator
    k = math.isqrt(num // den)
    while (k + 1) * (k + 1) * den <= num:
        k += 1
    while k * k * den > num:
        k -= 1
    return F(k, D)


def union_area_exact(rects):
    """exact area of a union of axis rectangles: integer coordinates over a common denominator, sweep line in x and
    a segment tree with coverage counts on the compressed y coordinates (O(R log R))."""
    if not rects:
        return F(0)
    L = 1
    for r in rects:
        for v in r:
            L = L * v.denominator // math.gcd(L, v.denominator)
    R = [tuple(v.numerator * (L // v.denominator) for v in r) for r in rects]
    ys = sorted({r[2] for r in R} | {r[3] for r in R})
    yi = {v: i for i, v in enumerate(ys)}
    ev = []
    for (x0, x1, y0, y1) in R:
        ev.append((x0, 1, yi[y0], yi[y1])); ev.append((x1, -1, yi[y0], yi[y1]))
    ev.sort()
    n = len(ys) - 1
    cnt = [0] * (4 * n + 4); ln = [0] * (4 * n + 4)

    def upd(node, l, r, a, b, d):
        if b <= l or r <= a:
            return
        if a <= l and r <= b:
            cnt[node] += d
        else:
            m = (l + r) // 2
            upd(2 * node, l, m, a, b, d); upd(2 * node + 1, m, r, a, b, d)
        if cnt[node] > 0:
            ln[node] = ys[r] - ys[l]
        elif r - l == 1:
            ln[node] = 0
        else:
            ln[node] = ln[2 * node] + ln[2 * node + 1]

    area = 0; px = ev[0][0]
    for (x, d, a, b) in ev:
        area += ln[1] * (x - px)
        px = x
        if n > 0:
            upd(1, 0, n, a, b, d)
    return F(area, L * L)


def union_area_exact_slow(rects):
    if not rects:
        return F(0)
    xs = sorted({r[0] for r in rects} | {r[1] for r in rects})
    area = F(0)
    for i in range(len(xs) - 1):
        xl, xr = xs[i], xs[i + 1]
        segs = sorted((r[2], r[3]) for r in rects if r[0] <= xl and r[1] >= xr)
        cov = F(0); cur0 = cur1 = None
        for (a, b) in segs:
            if cur1 is None or a > cur1:
                if cur1 is not None:
                    cov += cur1 - cur0
                cur0, cur1 = a, b
            elif b > cur1:
                cur1 = b
        if cur1 is not None:
            cov += cur1 - cur0
        area += cov * (xr - xl)
    return area


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('config'); ap.add_argument('--reach', default=None); ap.add_argument('--D', type=int, default=2 ** 40)
    ap.add_argument('--margin', type=int, default=None)
    a = ap.parse_args()
    cfg = json.load(open(a.config))
    lam = F(cfg['lam']); Px = F(cfg['Px']); Py = F(cfg['Py'])
    pts = [(F(x), F(y), F(m)) for (x, y, m) in cfg['pts']]
    for (x, y, m) in pts:
        if not (0 <= x < Px and 0 <= y < Py and m > 0):
            raise ValueError('points must lie in [0,Px) x [0,Py) with positive mass')
    mcell = sum(m for (_, _, m) in pts)
    reach = F(a.reach) if a.reach is not None else F(cfg.get('reach', str(3 * max(Px, Py))))
    # window: all copies whose boxes of side <= reach can produce a rectangle meeting the cell
    rho_max = math.sqrt(float((reach / Px + 2) * (reach / Py + 2) * mcell / (4 * lam)))
    mx = a.margin or int(math.ceil((float(reach) + rho_max) / float(Px))) + 1
    my = a.margin or int(math.ceil((float(reach) + rho_max) / float(Py))) + 1
    W = [(x + i * Px, y + j * Py, m) for i in range(-mx, mx + 1) for j in range(-my, my + 1) for (x, y, m) in pts]
    X = sorted({p[0] for p in W}); Y = sorted({p[1] for p in W})
    xi = {v: i for i, v in enumerate(X)}; yi = {v: i for i, v in enumerate(Y)}
    G = [[F(0)] * (len(Y) + 1) for _ in range(len(X) + 1)]
    for (x, y, m) in W:
        G[xi[x] + 1][yi[y] + 1] += m
    for i in range(1, len(X) + 1):
        row, prev = G[i], G[i - 1]
        for j in range(1, len(Y) + 1):
            row[j] += prev[j] + row[j - 1] - prev[j - 1]
    rects = []
    for ia in range(len(X)):
        for ib in range(ia, len(X)):
            if X[ib] - X[ia] > reach:
                break
            for ja in range(len(Y)):
                for jb in range(ja, len(Y)):
                    if Y[jb] - Y[ja] > reach:
                        break
                    m = G[ib + 1][jb + 1] - G[ia][jb + 1] - G[ib + 1][ja] + G[ia][ja]
                    if m <= 0:
                        continue
                    rho = isqrt_frac_lower(m / (4 * lam), a.D) - F(1, a.D)     # strictly below sqrt(m/(4 lam))
                    if rho <= 0:
                        continue
                    x0, x1, y0, y1 = X[ib] - rho, X[ia] + rho, Y[jb] - rho, Y[ja] + rho
                    x0, x1, y0, y1 = max(x0, F(0)), min(x1, Px), max(y0, F(0)), min(y1, Py)
                    if x1 > x0 and y1 > y0:
                        rects.append((x0, x1, y0, y1))
    A = union_area_exact(rects)
    ratio = lam * A / mcell
    print('points per cell', len(pts), 'window points', len(W), 'rectangles', len(rects))
    print('area in cell', float(A), 'of', float(Px * Py))
    print('EXACT ratio lower bound', ratio if len(str(ratio)) < 200 else '(long fraction)')
    print('ratio >= %.12f (rounded down: %s)' % (float(ratio) - 1e-15, str(math.floor(ratio * 10 ** 10) / 10 ** 10)))


if __name__ == '__main__':
    main()
