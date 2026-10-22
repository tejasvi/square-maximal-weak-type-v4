"""Tests for lb_check.py: (1) union_area_scaled against inclusion-exclusion on random rectangle sets; (2) toy
certificates with known answers; (3) input validation."""
import itertools, json, os, random, subprocess, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lb_check import union_area_scaled

def incl_excl(rects):
    tot = 0
    for r in range(1, len(rects) + 1):
        for comb in itertools.combinations(rects, r):
            x0 = max(c[0] for c in comb); x1 = min(c[1] for c in comb)
            y0 = max(c[2] for c in comb); y1 = min(c[3] for c in comb)
            if x0 < x1 and y0 < y1:
                tot += (-1) ** (r + 1) * (x1 - x0) * (y1 - y0)
    return tot

random.seed(7)
bad = 0
for trial in range(400):
    n = random.randint(1, 10)
    rects = []
    for _ in range(n):
        x0 = random.randint(0, 40); y0 = random.randint(0, 40)
        rects.append((x0, x0 + random.randint(1, 25), y0, y0 + random.randint(1, 25)))
    if union_area_scaled(rects) != incl_excl(rects):
        bad += 1
print('union area vs inclusion-exclusion, 400 random sets:', 'PASS' if bad == 0 else f'FAIL ({bad})')
big = [(random.randint(0, 2**45), 0, 0, 0) for _ in range(0)]
# large coordinates (2^44 scale) to exercise Python-int sums
rects = [(0, 2**44, 0, 2**44), (2**43, 3 * 2**43, 2**43, 3 * 2**43)]
print('large-coordinate case:', 'PASS' if union_area_scaled(rects) == incl_excl(rects) else 'FAIL')

here = os.path.dirname(os.path.abspath(__file__))
def run(cert, name):
    path = os.path.join(here, 'tests', name + '.json')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    json.dump(cert, open(path, 'w'))
    r = subprocess.run([sys.executable, '-I', os.path.join(here, 'lb_check.py'), path], capture_output=True, text=True)
    return r.returncode, r.stdout
# toy 1: one unit atom per unit cell, lam = 1/4: rho -> 1 - 1/D, rectangles of side ~2 cover everything: A = 1, value 1/4
rc, out = run({'lam': '1/4', 'P_x': '1', 'P_y': '1', 'D': 1024, 'reach': '0', 'window': 3, 'claimed': '1/4',
               'atoms': [['0', '0', '1']]}, 'toy1')
print('toy1 (value 1/4):', 'PASS' if rc == 0 and 'lam A / mu(C) = 1/4' in out else 'FAIL', out.strip().splitlines()[-3:])
# toy 2: same lattice, lam = 1: rho = 1/2 - 1/D, single-atom squares of side 1 - 2/D: A = (1 - 2/D)^2
D = 1024
rc, out = run({'lam': '1', 'P_x': '1', 'P_y': '1', 'D': D, 'reach': '0', 'window': 3, 'claimed': '0',
               'atoms': [['0', '0', '1']]}, 'toy2')
want = F(D - 2, D) ** 2
print('toy2 (reach 0, A = (1-2/D)^2):', 'PASS' if f'lam A / mu(C) = {want}' in out else 'FAIL', out.strip().splitlines()[-3])
# toy 3: claim above the value must FAIL with rc 1
rc, out = run({'lam': '1', 'P_x': '1', 'P_y': '1', 'D': D, 'reach': '0', 'window': 3, 'claimed': '1',
               'atoms': [['0', '0', '1']]}, 'toy3')
print('toy3 (claim too high -> FAIL, rc 1):', 'PASS' if rc == 1 and 'RESULT: FAIL' in out else 'FAIL')
# toy 4: validation: D = 0, window = 0, mass 0, atom outside cell, duplicate atom, bool D
for nm, cert in (('D0', {'D': 0}), ('win0', {'window': 0}), ('mass0', {'atoms': [['0', '0', '0']]}),
                 ('outside', {'atoms': [['1', '0', '1']]}), ('dup', {'atoms': [['0', '0', '1'], ['0', '0', '1']]}),
                 ('Dbool', {'D': True}), ('noatoms', {'atoms': []}), ('lamneg', {'lam': '-1'})):
    base = {'lam': '1', 'P_x': '1', 'P_y': '1', 'D': D, 'reach': '0', 'window': 3, 'claimed': '0', 'atoms': [['0', '0', '1']]}
    base.update(cert)
    rc, out = run(base, 'val_' + nm)
    print(f'validation {nm}:', 'PASS' if rc == 1 and 'RESULT: FAIL' in out else 'FAIL', out.strip().splitlines()[0][:80])
# toy 5: window too small must FAIL
rc, out = run({'lam': '1/16', 'P_x': '1', 'P_y': '1', 'D': D, 'reach': '3', 'window': 1, 'claimed': '0',
               'atoms': [['0', '0', '1']]}, 'toy5')
print('toy5 (window too small -> FAIL):', 'PASS' if rc == 1 and 'window too small' in out else 'FAIL', out.strip().splitlines()[0][:90])
