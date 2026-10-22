"""Rationalize a segment configuration (seg_search.py JSON) exactly: h, V, w, segment ends a/h, b/h, heights y/V and
linear densities rounded to multiples of 1/D; atoms and orbits generated with exact rational arithmetic.
Usage: rationalize_seg.py IN.json OUT.json [D]"""
import sys, json, math
from fractions import Fraction as F

d = json.load(open(sys.argv[1]))
D = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 12
p = d['params']; n = d['n']
fr = lambda v: F(round(v * D), D)
h, V, w = fr(math.exp(p[0])), fr(math.exp(p[1])), fr(math.exp(p[2]))
Px, Py = 2 * h, V
pts = [(F(0), F(0), F(1)), (h, F(0), w)]
for s in range((len(p) - 3) // 4):
    a, b, fy, lt = p[3 + 4 * s: 7 + 4 * s]
    a, b = sorted((min(max(a, 0.0), 1.0), min(max(b, 0.0), 1.0)))
    fy = min(max(fy, 0.0), 0.5)
    if b - a < 1e-6:
        continue
    a, b, fy, tau = fr(a), fr(b), fr(fy), fr(math.exp(lt))
    L = (b - a) * h
    m = tau * L / n
    y = fy * V
    for i in range(n):
        x = (a + (i + F(1, 2)) * (b - a) / n) * h
        orbit = {(x % Px, y % Py), ((2 * h - x) % Px, y % Py), (x % Px, (-y) % Py), ((2 * h - x) % Px, (-y) % Py)}
        for (u, v) in sorted(orbit):
            pts.append((u, v, m))
mcell = sum(q[2] for q in pts)
reach = F(round((4.0 * math.sqrt(float(mcell) / 4) + 2 * float(max(Px, Py))) * 1000), 1000)
cfg = dict(lam='1', Px=str(Px), Py=str(Py), pts=[[str(a_), str(b_), str(c_)] for (a_, b_, c_) in pts], reach=str(reach),
           source=sys.argv[1], float_ratio=d['ratio'])
json.dump(cfg, open(sys.argv[2], 'w'), indent=1)
print('atoms', len(pts), 'reach', float(reach))
