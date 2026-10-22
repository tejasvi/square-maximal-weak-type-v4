"""Tests for lb_check2.py (the checker used on the certificate):
(1) its union_area against inclusion-exclusion on random rectangle sets and large coordinates;
(2) lb_check2.py and lb_check.py (unpruned enumeration) give the same exact value on small periodic configurations
    (random rational atoms, several lam, reach and D), so the pruning loses nothing;
(3) rc 1 on a claim above the value. Writes its inputs to tests2/ (run on a writable copy)."""
import itertools, json, os, random, subprocess, sys
from fractions import Fraction as F
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
from lb_check2 import union_area

def incl_excl(rects):
    tot = 0
    for r in range(1, len(rects) + 1):
        for comb in itertools.combinations(rects, r):
            x0 = max(c[0] for c in comb); x1 = min(c[1] for c in comb)
            y0 = max(c[2] for c in comb); y1 = min(c[3] for c in comb)
            if x0 < x1 and y0 < y1:
                tot += (-1) ** (r + 1) * (x1 - x0) * (y1 - y0)
    return tot

ok = True
rng = random.Random(11)
bad = 0
for _ in range(400):
    n = rng.randint(1, 10)
    rects = []
    for _ in range(n):
        x0 = rng.randint(0, 40); y0 = rng.randint(0, 40)
        rects.append((x0, x0 + rng.randint(1, 25), y0, y0 + rng.randint(1, 25)))
    if union_area(rects) != incl_excl(rects):
        bad += 1
big = [(0, 2**70, 0, 2**70), (2**69, 3 * 2**69, 2**69, 3 * 2**69), (5, 2**71, 7, 9)]
big_ok = union_area(big) == incl_excl(big)
print('(1) union_area vs inclusion-exclusion, 400 random sets + large coordinates:', 'PASS' if bad == 0 and big_ok else 'FAIL')
ok &= bad == 0 and big_ok

os.makedirs(os.path.join(here, 'tests2'), exist_ok=True)
def value_of(out):
    for line in out.splitlines():
        if line.startswith('lam A / mu(C) = '):
            return F(line.split('= ', 1)[1].strip())
    return None
nagree = 0; ntot = 0
for t in range(12):
    Px = F(rng.randint(8, 16), 4); Py = F(rng.randint(8, 16), 4)
    na = rng.randint(1, 3)
    atoms = []
    while len(atoms) < na:
        a = (F(rng.randrange(0, 64), 64) * Px, F(rng.randrange(0, 64), 64) * Py, F(rng.randint(1, 12), 4))
        if (a[0], a[1]) not in {(b[0], b[1]) for b in atoms}:
            atoms.append(a)
    lam = F(rng.choice([1, 3, 1, 2]), rng.choice([1, 2, 4]))
    D = rng.choice([64, 1024, 2**20])
    reach = F(rng.randint(2, 10), 2)
    c1 = {'lam': str(lam), 'P_x': str(Px), 'P_y': str(Py), 'D': D, 'reach': str(reach), 'window': 6, 'claimed': '0',
          'atoms': [[str(x), str(y), str(m)] for x, y, m in atoms]}
    c2 = {'lam': str(lam), 'Px': str(Px), 'Py': str(Py), 'reach': str(reach), 'pts': [[str(x), str(y), str(m)] for x, y, m in atoms]}
    p1 = os.path.join(here, 'tests2', f'c{t}_lb.json'); p2 = os.path.join(here, 'tests2', f'c{t}_lb2.json')
    json.dump(c1, open(p1, 'w')); json.dump(c2, open(p2, 'w'))
    r1 = subprocess.run([sys.executable, '-I', os.path.join(here, 'lb_check.py'), p1], capture_output=True, text=True)
    r2 = subprocess.run([sys.executable, '-I', os.path.join(here, 'lb_check2.py'), p2, str(D)], capture_output=True, text=True)
    v1, v2 = value_of(r1.stdout), value_of(r2.stdout)
    if 'window too small' in r1.stdout:
        continue
    ntot += 1
    if v1 is not None and v1 == v2:
        nagree += 1
    else:
        print('   mismatch', t, v1, v2, r1.stdout[-200:], r2.stdout[-200:])
print(f'(2) lb_check2 == lb_check (exact) on {ntot} random small configurations: {nagree}/{ntot}', 'PASS' if nagree == ntot and ntot >= 6 else 'FAIL')
ok &= nagree == ntot and ntot >= 6
v = v2
r3 = subprocess.run([sys.executable, '-I', os.path.join(here, 'lb_check2.py'), p2, str(D), str(v + F(1, 10**20))], capture_output=True, text=True)
r4 = subprocess.run([sys.executable, '-I', os.path.join(here, 'lb_check2.py'), p2, str(D), str(v)], capture_output=True, text=True)
c3 = r3.returncode == 1 and 'RESULT: FAIL' in r3.stdout and r4.returncode == 0 and 'RESULT: PASS' in r4.stdout
print('(3) claim above the value -> rc 1, claim equal -> rc 0:', 'PASS' if c3 else 'FAIL')
ok &= c3
print('ALL PASS' if ok else 'SOME FAIL')
sys.exit(0 if ok else 1)
