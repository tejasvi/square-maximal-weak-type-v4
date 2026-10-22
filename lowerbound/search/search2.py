"""Massive multi-start local search over periodic point-mass configurations (rectangular cell, k points, lam = 1).
Start modes: rand (uniform positions), grid (points on a kx x ky product grid with random gaps), linp (Lin's lattice plus
k-2 extra random points with small masses), sym (configurations mirror-symmetric in x and y).
Usage: search2.py SEED K TRIALS OUT.json [--modes rand,grid,linp,sym] [--maxit 1500]"""
import sys, os, json, math, time, argparse
import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from search import objective, decode, encode
from hleval import lin_config


def start(mode, k, rng):
    if mode == 'rand':
        Px, Py = math.exp(rng.uniform(0.2, 1.8)), math.exp(rng.uniform(0.2, 1.8))
        pts = [(0.0, 0.0, 1.0)] + [(rng.uniform(0, Px), rng.uniform(0, Py), math.exp(rng.normal(0, 0.9))) for _ in range(k - 1)]
        return encode(Px, Py, pts)
    if mode == 'grid':
        divs = [d for d in range(1, k + 1) if k % d == 0]
        kx = int(rng.choice(divs)); ky = k // kx
        gx = np.exp(rng.normal(0.3, 0.4, kx)); gy = np.exp(rng.normal(0.3, 0.4, ky))
        xs = np.concatenate([[0], np.cumsum(gx)[:-1]]); ys = np.concatenate([[0], np.cumsum(gy)[:-1]])
        pts = []
        for i in range(kx):
            for j in range(ky):
                pts.append((float(xs[i]), float(ys[j]), 1.0 if (i == 0 and j == 0) else math.exp(rng.normal(0, 0.9))))
        return encode(float(gx.sum()), float(gy.sum()), pts)
    if mode == 'linp':
        Px, Py, pts = lin_config()
        f = float(rng.choice([1, 1, 2]))       # optionally double the cell in y
        P = [(x, y + j * Py, m) for j in range(int(f)) for (x, y, m) in pts]
        Py2 = Py * f
        while len(P) < k:
            P.append((rng.uniform(0, Px), rng.uniform(0, Py2), math.exp(rng.normal(-1.5, 1.0))))
        P = P[:k]
        p = encode(Px, Py2, P)
        return p + 0.02 * rng.standard_normal(len(p))
    if mode == 'sym':
        # mirror symmetry x -> Px - x, y -> Py - y (generated in a quarter cell, then reflected), point 0 at the origin
        Px, Py = math.exp(rng.uniform(0.3, 1.8)), math.exp(rng.uniform(0.3, 1.8))
        pts = [(0.0, 0.0, 1.0)]
        while len(pts) < k:
            x, y, m = rng.uniform(0, Px / 2), rng.uniform(0, Py / 2), math.exp(rng.normal(0, 0.9))
            orbit = {(round(x, 12), round(y, 12)), (round(Px - x, 12) % Px, round(y, 12)), (round(x, 12), round(Py - y, 12) % Py),
                     (round(Px - x, 12) % Px, round(Py - y, 12) % Py)}
            for (a, b) in orbit:
                if len(pts) < k:
                    pts.append((a, b, m))
        return encode(Px, Py, pts)
    raise ValueError(mode)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('seed', type=int); ap.add_argument('k', type=int); ap.add_argument('trials', type=int); ap.add_argument('out')
    ap.add_argument('--modes', default='rand,grid,linp,sym'); ap.add_argument('--maxit', type=int, default=1500)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    modes = a.modes.split(',')
    k = a.k
    best = None; t0 = time.time(); good = []
    for trial in range(a.trials):
        mode = modes[trial % len(modes)]
        p0 = start(mode, k, rng)
        x = p0
        for rep in range(2):
            res = minimize(lambda p: -objective(p, k), x, method='Nelder-Mead',
                           options=dict(maxiter=a.maxit * len(x), xatol=1e-10, fatol=1e-13, adaptive=True))
            x = res.x
        val = objective(x, k)
        if val > 1.680:
            good.append((val, mode, list(map(float, x))))
        if best is None or val > best['ratio']:
            Px, Py, pts = decode(x, k)
            best = dict(ratio=val, k=k, params=list(map(float, x)), Px=Px, Py=Py, pts=pts, trial=trial, mode=mode)
        if trial % 10 == 9 or val > 1.6855:
            good.sort(key=lambda t: -t[0])
            json.dump(dict(best=best, good=good[:50], trials=trial + 1, time=time.time() - t0), open(a.out, 'w'), indent=1)
        print('trial %d (%s) k=%d ratio %.10f best %.10f t=%.0fs' % (trial, mode, k, val, best['ratio'], time.time() - t0),
              flush=True)
    good.sort(key=lambda t: -t[0])
    json.dump(dict(best=best, good=good[:50], trials=a.trials, time=time.time() - t0), open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
