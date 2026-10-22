"""tests for the general-h C1/C2 code of hl_check.py:
(T2) tri_lower / rect_lower <= K at sampled points (random cells, random rational triangles, random sub-rectangles);
(T3) synthetic kernels with 1/h = 31/2 (not an integer, u + v = 1 cuts cells in general position): S = 1 on a box,
     c = 1/2; DIP_OUT lowers K below 1 just OUTSIDE D (must PASS C2), DIP_IN lowers K below 1 just INSIDE D (must FAIL)."""
import os
import sys, json, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb
from hl_core import Spec, A
import hl_check as H

def Kval(sp, u, v):
    return sp.cA * sp.Psi(A(abs(u) + abs(v))) + A(sp.S_point(u, v))

# (T2)
sp = Spec(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'v15fix.r1.json'))
kc = H.KChecker(sp)
rnd = random.Random(11)
bad = 0; n = 0
for trial in range(150):
    p = rnd.randint(0, 20); q = rnd.randint(0, p)
    pts = [(Fr(rnd.randint(0, 64), 64), Fr(rnd.randint(0, 64), 64)) for _ in range(3)]
    tri = tuple(pts)
    s0 = Fr(rnd.randint(0, 3), 4); s1 = s0 + Fr(1, 4); t0 = Fr(rnd.randint(0, 3), 4); t1 = t0 + Fr(1, 4)
    lo = kc.tri_lower(p, q, tri, s0, s1, t0, t1)
    P0, P1, P2 = tri
    for _ in range(6):
        s_ = s0 + (s1 - s0) * Fr(rnd.randint(0, 100), 100); t_ = t0 + (t1 - t0) * Fr(rnd.randint(0, 100), 100)
        x = P0[0] + s_ * ((1 - t_) * (P1[0] - P0[0]) + t_ * (P2[0] - P0[0]))
        y = P0[1] + s_ * ((1 - t_) * (P1[1] - P0[1]) + t_ * (P2[1] - P0[1]))
        u = sp.h * (p + x); v = sp.h * (q + y)
        if u + v == 0:
            continue
        k = Kval(sp, u, v)
        n += 1
        if not (lo <= k.lower()):
            bad += 1; print('T2 tri violation', p, q, tri, s_, t_, lo, k)
    x0 = Fr(rnd.randint(0, 7), 8); y0 = Fr(rnd.randint(0, 7), 8)
    lo = kc.rect_lower(p, q, x0, x0 + Fr(1, 8), y0, y0 + Fr(1, 8))
    for _ in range(6):
        x = x0 + Fr(rnd.randint(0, 100), 800); y = y0 + Fr(rnd.randint(0, 100), 800)
        u = sp.h * (p + x); v = sp.h * (q + y)
        if u + v == 0:
            continue
        k = Kval(sp, u, v); n += 1
        if not (lo <= k.lower()):
            bad += 1; print('T2 rect violation', p, q, x, y, lo, k)
print('(T2) bound <= sampled K: %d samples, %d violations' % (n, bad))

# (T3) synthetic kernels, h = 2/31
base = {"alpha": "6/5", "R": "7/4", "h": "2/31", "N": 30, "c": "1/2", "a": {}}
for I in range(0, 27):
    for J in range(0, I + 1):
        base["a"]["%d,%d" % (I, J)] = "1"
out = {}
for name, key, delta in (("SYN_OK", None, None), ("DIP_OUT", "9,7", Fr(-55, 100)), ("DIP_IN", "8,7", Fr(-70, 100))):
    d = json.loads(json.dumps(base))
    if key:
        d["a"][key] = str(Fr(d["a"][key]) + delta)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'testdata', 'synth', '%s.json' % name)
    json.dump(d, open(path, 'w'))
    s2 = Spec(path)
    # witnesses: K at the dip knot and the min of K on D near it (sampled)
    if key:
        I, J = (int(z) for z in key.split(','))
        u, v = s2.h * I, s2.h * J
        kmin_in = None
        for a_ in range(-40, 41):
            for b_ in range(-40, 41):
                uu = u + s2.h * Fr(a_, 20); vv = v + s2.h * Fr(b_, 20)
                if uu < 0 or vv < 0 or uu + vv > 1:
                    continue
                k = Kval(s2, uu, vv)
                if kmin_in is None or k < kmin_in[0]:
                    kmin_in = (k, uu, vv)
        print('%s: knot (%d,%d) r = %s: K = %s ; sampled min of K on D near it = %s at (%s,%s)' % (
            name, I, J, u + v, Kval(s2, u, v).str(6), kmin_in[0].str(6), kmin_in[1], kmin_in[2]))
    o = H.check_c12(s2, maxdepth=6)
    print('%s: C1 cells %d fails %d | C2 cells %d leaves %d fails %d min %s' % (
        name, o['c1_cells'], len(o['c1_fail']), o['c2_cells'], o['c2_leaves'], len(o['c2_fail']),
        o['c2_min'].str(6) if o['c2_min'] is not None else None))
    out[name] = len(o['c2_fail'])
print('(T3) expected: SYN_OK pass, DIP_OUT pass, DIP_IN FAIL ->', 'OK' if out['SYN_OK'] == 0 and out['DIP_OUT'] == 0 and out['DIP_IN'] > 0 else 'UNEXPECTED')
