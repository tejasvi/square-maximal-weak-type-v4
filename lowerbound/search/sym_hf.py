"""Symmetric greedy hole filling. Configuration: cell [0, 2h) x [0, V), light mass 1 at (0,0), heavy mass w at (h,0),
plus orbits of extra masses under the symmetries x -> -x, x -> 2h - x, y -> -y (orbit of (x, y): (x, +-y), (2h - x, +-y)
mod the cell). Parameters: log h, log V, log w, then per orbit: x/h in [0,1], y/V in [0, 1/2], log m.
Usage: sym_hf.py START.json|lin OUT.json SEED [--rounds 20] [--n 600] [--maxit 600] [--tries 6]"""
import sys, os, json, math, time, argparse
import numpy as np
from scipy.optimize import minimize
from scipy.ndimage import label

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hleval import periodic_ratio, periodic_uncovered


def decode(p):
    h, V, w = math.exp(p[0]), math.exp(p[1]), math.exp(p[2])
    Px, Py = 2 * h, V
    pts = [(0.0, 0.0, 1.0), (h, 0.0, w)]
    no = (len(p) - 3) // 3
    for i in range(no):
        fx, fy, lm = p[3 + 3 * i: 6 + 3 * i]
        fx = min(max(fx, 0.0), 1.0); fy = min(max(fy, 0.0), 0.5)
        x, y, m = fx * h, fy * V, math.exp(lm)
        orbit = {(round(x, 13) % Px, round(y, 13) % Py), (round(2 * h - x, 13) % Px, round(y, 13) % Py),
                 (round(x, 13) % Px, round(-y, 13) % Py), (round(2 * h - x, 13) % Px, round(-y, 13) % Py)}
        for (a, b) in sorted(orbit):
            pts.append((a, b, m))
    return Px, Py, pts


def objective(p):
    try:
        Px, Py, pts = decode(p)
        if not (0.2 < Px < 40 and 0.2 < Py < 40) or any(not (1e-6 < q[2] < 1e3) for q in pts):
            return 0.0
        return periodic_ratio(Px, Py, pts, lam=1.0)[0]
    except Exception:
        return 0.0


def polish(x, maxit, reps=2):
    for _ in range(reps):
        x = minimize(lambda p: -objective(p), x, method='Nelder-Mead',
                     options=dict(maxiter=maxit * len(x), xatol=1e-12, fatol=1e-14, adaptive=True)).x
    return x, objective(x)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('start'); ap.add_argument('out'); ap.add_argument('seed', type=int)
    ap.add_argument('--rounds', type=int, default=20); ap.add_argument('--n', type=int, default=600)
    ap.add_argument('--maxit', type=int, default=600); ap.add_argument('--tries', type=int, default=6)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    if a.start == 'lin':
        s22 = math.sqrt(22.0); h = (5 + s22) / 6; V = h + 1; w = (17 + 4 * s22) / 9
        x = np.array([math.log(h), math.log(V), math.log(w)])
    else:
        x = np.array(json.load(open(a.start))['params'])
    x, val = polish(x, a.maxit)
    print('start orbits=%d ratio %.10f' % ((len(x) - 3) // 3, val), flush=True)
    t0 = time.time()
    for rnd in range(a.rounds):
        Px, Py, pts = decode(x)
        h, V = Px / 2, Py
        gx, gy, unc = periodic_uncovered(Px, Py, pts, n=a.n)
        # restrict to the fundamental quarter 0 <= x <= h, 0 <= y <= V/2
        q = unc.copy(); q[gx > h, :] = False; q[:, gy > V / 2] = False
        lab, nl = label(q)
        H = []
        for kk in range(1, nl + 1):
            idx = np.argwhere(lab == kk)
            H.append((len(idx) * (Px / a.n) * (Py / a.n), gx[idx[:, 0]].mean(), gy[idx[:, 1]].mean(),
                      gx[idx[:, 0]].min(), gx[idx[:, 0]].max(), gy[idx[:, 1]].min(), gy[idx[:, 1]].max()))
        H.sort(key=lambda t: -t[0])
        print('round %d: %d holes in the quarter, uncovered %.5f, largest %s' % (rnd, len(H), unc.mean(),
              ['%.3g' % t[0] for t in H[:5]]), flush=True)
        if not H:
            break
        improved = False
        for t in range(a.tries):
            hh = H[t % len(H)] if t < 2 * len(H) else H[int(rng.integers(len(H)))]
            if t < len(H):
                px_, py_ = hh[1], hh[2]
            else:
                px_, py_ = rng.uniform(hh[3], hh[4]), rng.uniform(hh[5], hh[6])
            m0 = max(1e-5, min(0.05, hh[0] * rng.uniform(0.05, 0.3)))
            x2 = np.concatenate([x, [px_ / h, py_ / V, math.log(m0)]])
            x2, v2 = polish(x2, a.maxit)
            print('  try %d: hole %.3g at (%.4f, %.4f) m0 %.3g -> %.10f' % (t, hh[0], px_, py_, m0, v2), flush=True)
            if v2 > val + 1e-9:
                x, val = x2, v2
                improved = True
                break
        Px, Py, pts = decode(x)
        json.dump(dict(ratio=val, orbits=(len(x) - 3) // 3, params=list(map(float, x)), Px=Px, Py=Py, pts=pts,
                       round=rnd, time=time.time() - t0), open(a.out, 'w'), indent=1)
        print('round %d done: orbits=%d npts=%d ratio %.10f (t=%.0fs)' % (rnd, (len(x) - 3) // 3, len(pts), val,
              time.time() - t0), flush=True)
        if not improved:
            break


if __name__ == '__main__':
    main()
