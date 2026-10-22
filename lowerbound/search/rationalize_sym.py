"""Rationalize a symmetric configuration (sym_hf.py JSON) exactly: h, V, w and orbit parameters rounded to multiples of
1/D, orbit points generated with exact rational arithmetic (so the symmetry is exact). Writes a check_exact.py config.
Usage: rationalize_sym.py IN.json OUT.json [D]"""
import sys, json, math
from fractions import Fraction as F

d = json.load(open(sys.argv[1]))
D = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 12
p = d['params']
fr = lambda v: F(round(v * D), D)
h, V, w = fr(math.exp(p[0])), fr(math.exp(p[1])), fr(math.exp(p[2]))
Px, Py = 2 * h, V
pts = [(F(0), F(0), F(1)), (h, F(0), w)]
for i in range((len(p) - 3) // 3):
    fx, fy, lm = p[3 + 3 * i: 6 + 3 * i]
    fx = min(max(fx, 0.0), 1.0); fy = min(max(fy, 0.0), 0.5)
    x, y, m = fr(fx) * h, fr(fy) * V, fr(math.exp(lm))
    orbit = {(x % Px, y % Py), ((2 * h - x) % Px, y % Py), (x % Px, (-y) % Py), ((2 * h - x) % Px, (-y) % Py)}
    for (a, b) in sorted(orbit):
        pts.append((a, b, m))
mcell = sum(q[2] for q in pts)
reach = F(round((4.0 * math.sqrt(float(mcell) / 4) + 2 * float(max(Px, Py))) * 1000), 1000)
cfg = dict(lam='1', Px=str(Px), Py=str(Py), pts=[[str(a), str(b), str(c)] for (a, b, c) in pts], reach=str(reach),
           source=sys.argv[1], float_ratio=d['ratio'])
json.dump(cfg, open(sys.argv[2], 'w'), indent=1)
print('points', len(pts), 'reach', float(reach))
