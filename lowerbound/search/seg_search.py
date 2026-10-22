"""Lin's symmetric frame plus horizontal segments of equally spaced equal atoms (orbits under x -> -x, x -> 2h - x,
y -> -y). Parameters: log h, log V, log w, then per segment: a/h, b/h (x-range inside [0, h], sorted), y/V in [0, 1/2],
log tau (mass per unit length). Each segment carries n atoms at x = a + (i + 1/2)(b - a)/n, mass tau (b - a)/n.
Usage: seg_search.py START.json|lin OUT.json SEED --segs S --n N [--trials T] [--maxit M]"""
import sys, os, json, math, time, argparse
import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hleval import periodic_ratio


def decode(p, n):
    h, V, w = math.exp(p[0]), math.exp(p[1]), math.exp(p[2])
    Px, Py = 2 * h, V
    pts = [(0.0, 0.0, 1.0), (h, 0.0, w)]
    ns = (len(p) - 3) // 4
    for s in range(ns):
        a, b, fy, lt = p[3 + 4 * s: 7 + 4 * s]
        a, b = sorted((min(max(a, 0.0), 1.0), min(max(b, 0.0), 1.0)))
        fy = min(max(fy, 0.0), 0.5)
        if b - a < 1e-6:
            continue
        L = (b - a) * h; m = math.exp(lt) * L / n
        y = fy * V
        for i in range(n):
            x = (a + (i + 0.5) * (b - a) / n) * h
            orbit = {(round(x, 13) % Px, round(y, 13) % Py), (round(2 * h - x, 13) % Px, round(y, 13) % Py),
                     (round(x, 13) % Px, round(-y, 13) % Py), (round(2 * h - x, 13) % Px, round(-y, 13) % Py)}
            for (u, v) in sorted(orbit):
                pts.append((u, v, m))
    return Px, Py, pts


def objective(p, n):
    try:
        Px, Py, pts = decode(p, n)
        if not (0.2 < Px < 40 and 0.2 < Py < 40) or any(not (1e-8 < q[2] < 1e3) for q in pts):
            return 0.0
        return periodic_ratio(Px, Py, pts, lam=1.0)[0]
    except Exception:
        return 0.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('start'); ap.add_argument('out'); ap.add_argument('seed', type=int)
    ap.add_argument('--segs', type=int, default=1); ap.add_argument('--n', type=int, default=8)
    ap.add_argument('--trials', type=int, default=10); ap.add_argument('--maxit', type=int, default=600)
    ap.add_argument('--init2', type=int, default=0)   # 1: segment 1 near the heavy column (y = 0.393 V), segment 2 near the light column (y = 0.2007 V)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    s22 = math.sqrt(22.0); h0 = (5 + s22) / 6
    base = np.array([math.log(h0), math.log(h0 + 1), math.log((17 + 4 * s22) / 9)])
    if a.start != 'lin':
        d = json.load(open(a.start)); base = np.array(d['params'][:3])
    if a.init2:
        base = np.array([math.log(1.609145), math.log(2.677264), math.log(3.828662)])
    best = (0.0, None); t0 = time.time()
    for trial in range(a.trials):
        p = list(base + 0.01 * rng.standard_normal(3))
        for s in range(a.segs):
            if a.init2 and s == 0:
                seg = [0.72 + 0.03 * rng.standard_normal(), 0.90 + 0.02 * rng.standard_normal(), 0.393 + 0.003 * rng.standard_normal(),
                       math.log(0.09) + 0.3 * rng.standard_normal()]
            elif a.init2 and s == 1:
                seg = [0.0 + abs(0.03 * rng.standard_normal()), 0.24 + 0.03 * rng.standard_normal(), 0.2007 + 0.003 * rng.standard_normal(),
                       math.log(0.035) + 0.3 * rng.standard_normal()]
            elif s == 0 and trial % 2 == 0:
                seg = [0.74 + 0.05 * rng.standard_normal(), 0.93 + 0.03 * rng.standard_normal(), 0.39 + 0.01 * rng.standard_normal(),
                       math.log(0.046) + 0.3 * rng.standard_normal()]
            else:
                c, L = rng.uniform(0, 1), rng.uniform(0.05, 0.5)
                seg = [max(0.0, c - L / 2), min(1.0, c + L / 2), rng.uniform(0.05, 0.5), math.log(0.05) + rng.standard_normal()]
            p += seg
        x = np.array(p)
        for rep in range(3):
            x = minimize(lambda q: -objective(q, a.n), x, method='Nelder-Mead',
                         options=dict(maxiter=a.maxit * len(x), xatol=1e-12, fatol=1e-14, adaptive=True)).x
        v = objective(x, a.n)
        if v > best[0]:
            best = (v, x)
            Px, Py, pts = decode(x, a.n)
            json.dump(dict(ratio=v, segs=a.segs, n=a.n, params=list(map(float, x)), Px=Px, Py=Py, pts=pts, trial=trial),
                      open(a.out, 'w'), indent=1)
        print('trial %d segs=%d n=%d ratio %.10f best %.10f t=%.0fs' % (trial, a.segs, a.n, v, best[0], time.time() - t0),
              flush=True)


if __name__ == '__main__':
    main()
