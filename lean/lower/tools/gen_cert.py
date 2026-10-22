"""Generate the Lean certificate (CenteredMaximal/Periodic/Data*.lean) for a periodic point-mass configuration.

Input: a configuration JSON (lam = 1, Px, Py, pts = [[x, y, m], ...] as rational strings, reach), as in the
certificate package of the configuration. Rectangles R_S(rho) are built exactly as in that package's exact checker
check_exact2.py (rho = (isqrt(floor(Ms Dr^2/(4 Dm))) - 1)/Dr with Dr = 2^40, boxes with bounds at window atom
coordinates, clipped to the cell); a slab sweep with minimal per-slab interval
covers gives disjoint half-open pieces, each inside one rectangle; consecutive slabs with identical piece lists are
merged. Only rectangles used by some piece are kept. A Python mirror of the Lean checker (checkCert) re-checks the
emitted data. Usage:
  python3 -I gen_cert.py CONFIG.json OUTDIR [--Dr 2^40] [--ellinv 16] [--rnum N --rden D] [--name NAME]
writes OUTDIR/Data.lean and OUTDIR/Data/*.lean (the Lean data modules, at most 1500 lines each) and OUTDIR/cert.json
(the same data).
"""
import os, sys, json, math, argparse
from fractions import Fraction as F


def lcm(a, b):
    return a * b // math.gcd(a, b)


def build(cfg, Dr):
    if F(cfg['lam']) != 1:
        raise ValueError('lam must be 1')
    Px, Py = F(cfg['Px']), F(cfg['Py'])
    pts = [(F(x), F(y), F(m)) for (x, y, m) in cfg['pts']]
    for (x, y, m) in pts:
        if not (0 <= x < Px and 0 <= y < Py and m > 0):
            raise ValueError('atoms must lie in [0,Px) x [0,Py) with positive mass')
    reach = F(cfg['reach'])
    Dx = 1
    for v in [Px, Py, reach] + [p[0] for p in pts] + [p[1] for p in pts]:
        Dx = lcm(Dx, v.denominator)
    Dm = 1
    for p in pts:
        Dm = lcm(Dm, p[2].denominator)
    L = lcm(Dx, Dr)
    sx, sr = L // Dx, L // Dr
    PxI, PyI, reachI = int(Px * Dx), int(Py * Dx), int(reach * Dx)
    P = [(int(x * Dx), int(y * Dx), int(m * Dm)) for (x, y, m) in pts]
    mcellI = sum(p[2] for p in P)
    nb = (int(reach / Px) + 2) * (int(reach / Py) + 2)
    rho_max = F(math.isqrt(nb * mcellI * Dr * Dr // (4 * Dm)) + 1, Dr)
    rmI = int(math.ceil(rho_max * Dx)) + 1
    ext = reachI + rmI
    mx = ext // PxI + 2; my = ext // PyI + 2
    W = [(x + i * PxI, y + j * PyI, m, k, i, j) for i in range(-mx, mx + 1) for j in range(-my, my + 1)
         for k, (x, y, m) in enumerate(P)]
    W = [w for w in W if -rmI - reachI <= w[0] <= PxI + rmI + reachI and -rmI - reachI <= w[1] <= PyI + rmI + reachI]
    X = sorted({w[0] for w in W}); Y = sorted({w[1] for w in W})
    xi = {v: i for i, v in enumerate(X)}; yi = {v: i for i, v in enumerate(Y)}
    nx, ny = len(X), len(Y)
    G = [[0] * (ny + 1) for _ in range(nx + 1)]
    for w in W:
        G[xi[w[0]] + 1][yi[w[1]] + 1] += w[2]
    for i in range(1, nx + 1):
        row, prev = G[i], G[i - 1]
        acc = 0
        for j in range(1, ny + 1):
            acc += row[j]
            row[j] = prev[j] + acc
    R = []
    four_dm = 4 * Dm
    for ia in range(nx):
        xa = X[ia]
        if xa < -rmI:
            continue
        for ib in range(ia, nx):
            xb = X[ib]
            if xb - xa > reachI or xb > PxI + rmI:
                break
            Gb, Ga = G[ib + 1], G[ia]
            for ja in range(ny):
                ya = Y[ja]
                if ya < -rmI:
                    continue
                for jb in range(ja, ny):
                    yb = Y[jb]
                    if yb - ya > reachI or yb > PyI + rmI:
                        break
                    Ms = Gb[jb + 1] - Ga[jb + 1] - Gb[ja] + Ga[ja]
                    if Ms <= 0:
                        continue
                    k = math.isqrt(Ms * Dr * Dr // four_dm) - 1
                    if k <= 0:
                        continue
                    rho = k * sr
                    x0 = max(xb * sx - rho, 0); x1 = min(xa * sx + rho, PxI * sx)
                    if x1 <= x0:
                        continue
                    y0 = max(yb * sx - rho, 0); y1 = min(ya * sx + rho, PyI * sx)
                    if y1 <= y0:
                        continue
                    R.append(dict(x0=x0, x1=x1, y0=y0, y1=y1, rho=rho, box=(xa, xb, ya, yb), Ms=Ms))
    meta = dict(L=L, Dx=Dx, Dm=Dm, Dr=Dr, sx=sx, PxI=PxI, PyI=PyI, P=P, W=W)
    return R, meta


def pieces_of(R):
    """slab sweep; per slab a minimal cover of the union of active y-intervals by pieces inside single rectangles."""
    xs = sorted({r['x0'] for r in R} | {r['x1'] for r in R})
    rows = []
    for s, t in zip(xs, xs[1:]):
        act = sorted((r['y0'], r['y1'], idx) for idx, r in enumerate(R) if r['x0'] <= s and t <= r['x1'])
        n = len(act); i = 0; row = []
        while i < n:
            pos = act[i][0]
            while True:
                best = None
                while i < n and act[i][0] <= pos:
                    if best is None or act[i][1] > best[1]:
                        best = act[i]
                    i += 1
                if best is None or best[1] <= pos:
                    break
                row.append((pos, best[1], best[2]))
                pos = best[1]
                if i >= n or act[i][0] > pos:
                    break
        if row:
            rows.append((s, t, row))
    # merge consecutive slabs with identical piece lists
    groups = []
    for (s, t, row) in rows:
        if groups and groups[-1][1] == s and groups[-1][2] == row:
            groups[-1] = (groups[-1][0], t, row)
        else:
            groups.append((s, t, row))
    return groups


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('config'); ap.add_argument('out')
    ap.add_argument('--Dr', type=int, default=2 ** 40)
    ap.add_argument('--ellinv', type=int, default=16)
    ap.add_argument('--rnum', type=int, default=None); ap.add_argument('--rden', type=int, default=None)
    ap.add_argument('--name', default='cert')
    ap.add_argument('--module', default='CenteredMaximal.Periodic.Data')
    ap.add_argument('--chunk', type=int, default=1400, help='data lines per generated module')
    a = ap.parse_args()
    cfg = json.load(open(a.config))
    R, meta = build(cfg, a.Dr)
    groups = pieces_of(R)
    L, Dm, sx = meta['L'], meta['Dm'], meta['sx']
    Px, Py = meta['PxI'] * sx, meta['PyI'] * sx
    atoms = [(x * sx, y * sx, m) for (x, y, m) in meta['P']]
    used = sorted({k for g in groups for (_, _, k) in g[2]})
    newidx = {k: i for i, k in enumerate(used)}
    W = meta['W']
    rects = []
    for k in used:
        r = R[k]
        xa, xb, ya, yb = r['box']
        S = [w for w in W if xa <= w[0] <= xb and ya <= w[1] <= yb]
        assert sum(w[2] for w in S) == r['Ms']
        codes = []
        for w in S:
            if not (-1 <= w[4] <= 1 and -1 <= w[5] <= 1):
                raise ValueError('witness atom outside the neighbouring cells')
            codes.append(9 * w[3] + 3 * (w[4] + 1) + (w[5] + 1))
        codes.sort()
        rects.append(dict(x0=r['x0'], x1=r['x1'], y0=r['y0'], y1=r['y1'], rho=r['rho'], codes=codes))
    pieces = [(s, t, ya, yb, newidx[k]) for (s, t, row) in groups for (ya, yb, k) in row]
    area = sum((p[1] - p[0]) * (p[3] - p[2]) for p in pieces)
    mcell = sum(m for (_, _, m) in atoms)
    ratio = F(area * Dm, L * L * mcell)
    if a.rnum is None:
        rden = 10 ** 10; rnum = math.floor(ratio * rden)
    else:
        rnum, rden = a.rnum, a.rden
    print('atoms', len(atoms), 'rects', len(rects), 'codes', sum(len(r['codes']) for r in rects),
          'slab groups', len(groups), 'pieces', len(pieces))
    print('ratio %.15f  stated %d/%d' % (float(ratio), rnum, rden))
    # ---- Python mirror of checkCert ----
    ok = mirror_check(L, Dm, Px, Py, a.ellinv, atoms, rects, pieces, rnum, rden)
    print('mirror checkCert:', ok)
    if not ok:
        sys.exit(1)
    data = dict(Q=L, Dm=Dm, Px=Px, Py=Py, ellInv=a.ellinv, atoms=atoms, rects=rects, pieces=pieces,
                rNum=rnum, rDen=rden, config=a.config, Dr=a.Dr)
    os.makedirs(os.path.join(a.out, 'Data'), exist_ok=True)
    json.dump(data, open(os.path.join(a.out, 'cert.json'), 'w'))
    write_lean(a.out, a.module, a.name, data, a.chunk)


def mirror_check(Q, Dm, Px, Py, ellInv, atoms, rects, pieces, rnum, rden):
    if not (Q > 0 and Dm > 0 and Px > 0 and Py > 0 and ellInv > 0 and rden > 0):
        return False
    mcell = sum(m for (_, _, m) in atoms)
    if mcell <= 0:
        return False
    for r in rects:
        cs = r['codes']
        if any(cs[i] >= cs[i + 1] for i in range(len(cs) - 1)):
            return False
        if not Q <= 2 * r['rho'] * ellInv:
            return False
        s = 0
        for t in cs:
            i = t // 9
            if i >= len(atoms):
                return False
            ax, ay, am = atoms[i]
            X = ax + (t % 9 // 3) * Px; Y = ay + (t % 3) * Py
            if not (X <= r['x0'] + Px + r['rho'] and r['x1'] + Px <= X + r['rho'] and
                    Y <= r['y0'] + Py + r['rho'] and r['y1'] + Py <= Y + r['rho']):
                return False
            s += am
        if not 4 * r['rho'] * r['rho'] * Dm <= s * Q * Q:
            return False
    prev = None
    for p in pieces:
        xa, xb, ya, yb, k = p
        if not (xa < xb <= Px and ya < yb <= Py and k < len(rects)):
            return False
        r = rects[k]
        if not (r['x0'] <= xa and xb <= r['x1'] and r['y0'] <= ya and yb <= r['y1']):
            return False
        if prev is not None:
            if not (prev[1] <= xa or (prev[0] == xa and prev[1] == xb and prev[3] <= ya)):
                return False
        prev = p
    area = sum((p[1] - p[0]) * (p[3] - p[2]) for p in pieces)
    return rnum * Q * Q * mcell <= area * Dm * rden


def wrap(tokens, first, indent, last, width=99):
    """Join tokens with ', ' into lines of at most `width` characters (99, so that the separator after a list
    element still fits in 100): `first` opens the first line, later lines start with `indent`, and `last` closes
    the last line."""
    lines, cur = [], first
    for i, tok in enumerate(tokens):
        piece = tok + (',' if i < len(tokens) - 1 else last)
        sep = '' if cur in (first, indent) else ' '
        if len(cur) + len(sep) + len(piece) > width and cur not in (first, indent):
            lines.append(cur)
            cur = indent + piece
        else:
            cur = cur + sep + piece
    lines.append(cur)
    return '\n'.join(lines)


HEADER = ('/-\nCopyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.\n'
          'Released under Apache 2.0 license as described in the file LICENSE.\n'
          'Authors: Tejasvi Singh Tomar\n-/\n')


def chunks(items, limit):
    """Split a list of multi-line strings into groups of at most `limit` lines."""
    groups, cur, n = [], [], 0
    for it in items:
        k = it.count('\n') + 1
        if cur and n + k > limit:
            groups.append(cur); cur, n = [], 0
        cur.append(it); n += k
    if cur:
        groups.append(cur)
    return groups


def write_list_module(path, module, name, defname, typ, doc, items, config):
    out = [HEADER, 'module\n\npublic import CenteredMaximal.Periodic.Cert\n',
           '/-!\n# Certificate data: %s\n\nGenerated by `tools/gen_cert.py` from the configuration file `%s`.\n-/\n'
           % (doc, config),
           '@[expose] public section\n\nnoncomputable section\n\nset_option maxRecDepth 100000\n\n'
           'namespace CenteredMaximal.Periodic.Cert\n',
           '/-- %s -/' % doc.capitalize(),
           'def %s : List %s := [' % (defname, typ),
           ',\n'.join(items) + ']\n',
           'end CenteredMaximal.Periodic.Cert\n\nend\n']
    open(path, 'w').write('\n'.join(out))


def write_lean(outdir, module, name, d, limit):
    config = d['config'].split('/')[-1]
    atoms = [wrap([str(v) for v in t], '  ⟨', '    ', '⟩') for t in d['atoms']]
    rects = []
    for r in d['rects']:
        head = wrap([str(r[k]) for k in ('x0', 'x1', 'y0', 'y1', 'rho')], '  ⟨', '    ', ',')
        codes = wrap([str(t) for t in r['codes']], '    [', '     ', ']⟩')
        rects.append(head + '\n' + codes)
    pieces = [wrap([str(v) for v in p], '  ⟨', '    ', '⟩') for p in d['pieces']]
    mods = []
    write_list_module(os.path.join(outdir, 'Data', 'Atoms.lean'), module + '.Atoms', name, name + 'Atoms', 'Atom',
                      'the atoms of the period cell', atoms, config)
    mods.append(module + '.Atoms')
    rnames, pnames = [], []
    for i, g in enumerate(chunks(rects, limit)):
        write_list_module(os.path.join(outdir, 'Data', 'Rects%d.lean' % i), module + '.Rects%d' % i, name,
                          name + 'Rects%d' % i, 'Rect', 'the witness rectangles, part %d' % i, g, config)
        mods.append(module + '.Rects%d' % i); rnames.append(name + 'Rects%d' % i)
    for i, g in enumerate(chunks(pieces, limit)):
        write_list_module(os.path.join(outdir, 'Data', 'Pieces%d.lean' % i), module + '.Pieces%d' % i, name,
                          name + 'Pieces%d' % i, 'Piece', 'the pieces, part %d' % i, g, config)
        mods.append(module + '.Pieces%d' % i); pnames.append(name + 'Pieces%d' % i)
    out = [HEADER, 'module\n\n' + '\n'.join('public import %s' % m for m in mods) + '\n',
           '/-!\n# Certificate data\n\nGenerated by `tools/gen_cert.py` from the configuration file `%s`.\n-/\n'
           % config,
           '@[expose] public section\n\nnoncomputable section\n\nnamespace CenteredMaximal.Periodic.Cert\n',
           '/-- The certificate. -/',
           'def %s : Cert where\n  Q := %d\n  Dm := %d\n  Px := %d\n  Py := %d\n  ellInv := %d\n'
           '  atoms := %sAtoms\n  rects := %s\n  pieces := %s\n'
           % (name, d['Q'], d['Dm'], d['Px'], d['Py'], d['ellInv'], name, ' ++ '.join(rnames), ' ++ '.join(pnames)),
           'end CenteredMaximal.Periodic.Cert\n\nend\n']
    open(os.path.join(outdir, 'Data.lean'), 'w').write('\n'.join(out))


if __name__ == '__main__':
    main()
