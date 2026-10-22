#!/usr/bin/env python3
"""Second checker for periodic point-mass lower bounds of c_2 (weak (1,1) constant of the centred maximal operator over
closed squares in R^2), written from NOTE_lower_bound.md (Lemmas 1 and 2) before reading the first checker's code.

Mathematics (NOTE, Lemma 2): for a periodic measure mu (lattice P_x Z x P_y Z, finitely many atoms per cell C), lam > 0
and finitely many atom sets S with 0 < rho_S < sqrt(mu(S)/(4 lam)), let U be the union of all lattice translates of the
rectangles R_S(rho_S) = intersection over p in S of Q(p, rho_S). Then c_2 >= lam |U cap C| / mu(C).

This program
 * reads lam, P_x, P_y, the atoms of one cell (rational), D, reach and window;
 * forms every set S = (atoms in a box [x_a, x_b] x [y_a, y_b]) whose four sides pass through atom coordinates of the
   window and whose widths are <= reach, and takes rho_S = (k - 1)/D with k = isqrt(floor(D^2 mu(S)/(4 lam))), which is
   strictly below sqrt(mu(S)/(4 lam)); rectangles with rho_S <= 0 or empty R_S are dropped;
 * R_S is computed from the atoms of S themselves (not from the box corners): [max x - rho, min x + rho] x
   [max y - rho, min y + rho];
 * keeps the rectangles meeting the cell C = [0, P_x) x [0, P_y) (the window must contain every atom of any S whose
   rectangle meets C; the program verifies this sufficient condition: window margin >= reach + max rho), clips them to C,
   and computes the area of their union EXACTLY with integers by a 2-D difference array on the compressed coordinates
   (coverage counts by prefix sums, area = sum over covered grid cells of width x height);
 * prints the exact rational lam A / mu(C) and compares it with the claimed value.
Exit status 0 iff the input is valid and the computed value is >= the claimed value.
"""
import json
import sys
from fractions import Fraction as F
from math import gcd, isqrt

import numpy as np


def lcm(a, b):
    return a // gcd(a, b) * b


def fail(msg):
    print('FAIL:', msg, flush=True)
    print('RESULT: FAIL')
    sys.exit(1)


def to_frac(v, name):
    if isinstance(v, bool) or not isinstance(v, (str, int)):
        fail(f'{name} must be a rational string or an integer, got {type(v).__name__}')
    try:
        return F(v)
    except (ValueError, ZeroDivisionError):
        fail(f'{name} is not a rational: {v!r}')


def union_area_scaled(rects):
    """rects: list of (x0, x1, y0, y1) integers with x0 < x1, y0 < y1. Exact area of the union (integer)."""
    if not rects:
        return 0
    xs = sorted({r[0] for r in rects} | {r[1] for r in rects})
    ys = sorted({r[2] for r in rects} | {r[3] for r in rects})
    xi = {v: i for i, v in enumerate(xs)}
    yi = {v: i for i, v in enumerate(ys)}
    nx, ny = len(xs) - 1, len(ys) - 1
    wy = np.array([ys[j + 1] - ys[j] for j in range(ny)], dtype=object)
    wx = [xs[i + 1] - xs[i] for i in range(nx)]
    # widths fit in int64 only if the coordinates do; use int64 for the coverage counts and Python ints for the sums
    area = 0
    # process in strips of rows to bound memory
    strip = max(1, min(nx, 20_000_000 // max(1, ny + 1)))
    by_row = sorted(rects, key=lambda r: xi[r[0]])
    for s0 in range(0, nx, strip):
        s1 = min(nx, s0 + strip)
        diff = np.zeros((s1 - s0 + 1, ny + 1), dtype=np.int64)
        for (x0, x1, y0, y1) in by_row:
            a, b = xi[x0], xi[x1]
            if b <= s0 or a >= s1:
                continue
            a, b = max(a, s0) - s0, min(b, s1) - s0
            c, d = yi[y0], yi[y1]
            diff[a, c] += 1
            diff[a, d] -= 1
            diff[b, c] -= 1
            diff[b, d] += 1
        cov = np.cumsum(np.cumsum(diff, axis=0), axis=1)[: s1 - s0, :ny] > 0
        for i in range(s1 - s0):
            row = cov[i]
            if row.any():
                area += wx[s0 + i] * int(sum(wy[row]))
    return area


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    cert = json.load(open(sys.argv[1]))
    lam = to_frac(cert['lam'], 'lam')
    Px = to_frac(cert['P_x'], 'P_x')
    Py = to_frac(cert['P_y'], 'P_y')
    D = cert['D']
    reach = to_frac(cert['reach'], 'reach')
    window = cert['window']
    claimed = to_frac(cert['claimed'], 'claimed')
    if not (isinstance(D, int) and not isinstance(D, bool) and D >= 1):
        fail('D must be an integer >= 1')
    if not (isinstance(window, int) and not isinstance(window, bool) and window >= 1):
        fail('window must be an integer >= 1')
    if not (lam > 0 and Px > 0 and Py > 0 and reach >= 0):
        fail('need lam > 0, P_x > 0, P_y > 0, reach >= 0')
    atoms = []
    for i, a in enumerate(cert['atoms']):
        if not (isinstance(a, list) and len(a) == 3):
            fail(f'atom {i} must be [x, y, m]')
        x, y, m = (to_frac(v, f'atom {i}') for v in a)
        if not (0 <= x < Px and 0 <= y < Py):
            fail(f'atom {i} outside the cell')
        if not m > 0:
            fail(f'atom {i} has mass <= 0')
        atoms.append((x, y, m))
    if not atoms:
        fail('no atoms')
    if len({(x, y) for x, y, _ in atoms}) != len(atoms):
        fail('two atoms at the same point (merge them)')
    muC = sum(m for _, _, m in atoms)
    # common integer grid: unit 1/G with G = lcm of all coordinate denominators and D
    G = D
    for v in [Px, Py, reach] + [x for x, _, _ in atoms] + [y for _, y, _ in atoms]:
        G = lcm(G, v.denominator)
    gx = int(Px * G); gy = int(Py * G); greach = int(reach * G)
    # periodic atoms in the window (cells -window..window around C)
    W = []
    for ci in range(-window, window + 1):
        for cj in range(-window, window + 1):
            for (x, y, m) in atoms:
                W.append((int(x * G) + ci * gx, int(y * G) + cj * gy, m))
    # sufficient-window test: every atom of an S whose rectangle meets C is within reach + rho of C; rho <= sqrt(mu(S)/4lam)
    # and mu(S) <= (atoms in a reach-box) -- bound mu(S) by the mass of the heaviest reach x reach box (computed below)
    xsort = sorted(set(p[0] for p in W)); ysort = sorted(set(p[1] for p in W))
    # index atoms by x for box queries
    W.sort()
    seen = {}
    nboxes = 0
    rects = []
    max_rho_scaled = 0
    four_lam = 4 * lam
    for ia, xa in enumerate(xsort):
        for xb in xsort[ia:]:
            if xb - xa > greach:
                break
            col = [p for p in W if xa <= p[0] <= xb]
            if not col:
                continue
            ycand = sorted(set(p[1] for p in col))
            for ja, ya in enumerate(ycand):
                for yb in ycand[ja:]:
                    if yb - ya > greach:
                        break
                    S = tuple(sorted((p[0], p[1]) for p in col if ya <= p[1] <= yb))
                    if not S or S in seen:
                        continue
                    nboxes += 1
                    muS = sum(p[2] for p in col if ya <= p[1] <= yb)
                    q = (muS / four_lam) * D * D                  # D^2 mu(S)/(4 lam)
                    k = isqrt(q.numerator // q.denominator)
                    rho = F(k - 1, D)
                    seen[S] = True
                    if rho <= 0:
                        continue
                    r = int(rho * G)
                    max_rho_scaled = max(max_rho_scaled, r)
                    sx = [p[0] for p in S]; sy = [p[1] for p in S]
                    x0, x1 = max(sx) - r, min(sx) + r
                    y0, y1 = max(sy) - r, min(sy) + r
                    if x0 >= x1 or y0 >= y1:
                        continue
                    # meets C = [0, gx) x [0, gy)?  clip
                    cx0, cx1 = max(x0, 0), min(x1, gx)
                    cy0, cy1 = max(y0, 0), min(y1, gy)
                    if cx0 < cx1 and cy0 < cy1:
                        rects.append((cx0, cx1, cy0, cy1))
    # window sufficiency: (i) every box with its lower-left corner in C lies in the window, so by periodicity the
    # enumeration sees every S up to translation and max_rho is the global maximum; (ii) every atom of an S whose
    # rectangle meets C is within reach + max rho of C (S lies within rho of a point of its rectangle).
    margin = window * min(gx, gy)
    if margin < greach + max(gx, gy):
        fail(f'window too small for (i): margin {F(margin, G)} < reach + max(P_x, P_y)')
    if margin < greach + max_rho_scaled:
        fail(f'window too small for (ii): margin {F(margin, G)} < reach + max rho = {F(greach + max_rho_scaled, G)}')
    A = F(union_area_scaled(rects), G * G)
    value = lam * A / muC
    print(f'atoms per cell {len(atoms)}, mu(C) = {muC}, lam = {lam}, D = {D}, reach = {reach}, window = {window}')
    print(f'distinct S {nboxes}, rectangles meeting C {len(rects)}, max rho = {float(F(max_rho_scaled, G)):.6f}')
    print(f'A = |U cap C| = {A} ({float(A):.12f}); cell area {Px * Py}')
    print(f'lam A / mu(C) = {value}')
    print(f'             ~= {float(value):.12f}; claimed {claimed} ~= {float(claimed):.12f}')
    ok = value >= claimed
    print('RESULT:', 'PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
