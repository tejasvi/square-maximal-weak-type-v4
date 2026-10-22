"""hl47a cutting-plane LP, version 3: two-level spline basis (numerical exploration, NOT a certificate).

The kernel is a single cubic tensor spline at the fine spacing h (plus the singular part), exactly as in DEFS.md, but the
LP variables are
  - coarse classes at spacing h_c = 2h (all classes with centre radius <= r_supp), expanded exactly into fine coefficients by
    the two-scale relation B(x) = sum_k p_k B(2x - k), p = (1, 4, 6, 4, 1)/8;
  - fine classes whose centre radius (I + J) h lies in one of the given bands (local refinement);
  - the singular coefficients.
The map M (fine variables x LP variables) is applied to every row, to the objective and to every evaluation, so all checks
are done on the fine spline that is exported. K >= 0 / K >= 1 on D are imposed by lazily added Bernstein rows on the fine
cells (no K rows at points). Candidate points: level-1 grid at h_c/4 everywhere and h/4 inside the bands (+- 2 h_c).
"""
import sys, os, time, json, argparse
import numpy as np
import scipy.sparse as sp
import highspy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cp_lp2 import Problem, grid_points, eta_profile, probe, sing_mass  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
PK = np.array([1.0, 4.0, 6.0, 4.0, 1.0]) / 8.0


def build_map(P, h_c, bands, r_supp):
    """h_c = 0: plain fine basis (every fine class with centre radius <= r_supp, no coarse variables)."""
    hf, Nf = P.h, P.N
    if h_c == 0:
        h_c = 2 * hf
        coarse = []
        bands = [(0.0, r_supp)]
    else:
        assert abs(h_c - 2 * hf) < 1e-15, 'h_c must be 2 h'
        coarse = None
    Nc = Nf // 2
    if coarse is None:
        coarse = [(I, J) for I in range(Nc + 1) for J in range(I + 1) if (I + J) * h_c <= r_supp + 1e-12]
    cvar = {k: t for t, k in enumerate(coarse)}
    fine = [(I, J) for I in range(Nf + 1) for J in range(I + 1)
            if any(b0 - 1e-12 <= (I + J) * hf <= b1 + 1e-12 for (b0, b1) in bands)]
    nc, nf = len(coarse), len(fine)
    rr, cc, vv = [], [], []
    for m in range(Nf + 1):
        for n in range(m + 1):
            fc = P.clsidx[m + Nf, n + Nf]
            acc = {}
            for i in range(-((2 - m) // 2), (m + 2) // 2 + 1):
                for j in range(-((2 - n) // 2), (n + 2) // 2 + 1):
                    if abs(m - 2 * i) > 2 or abs(n - 2 * j) > 2:
                        continue
                    key = (max(abs(i), abs(j)), min(abs(i), abs(j)))
                    t = cvar.get(key)
                    if t is None:
                        continue
                    acc[t] = acc.get(t, 0.0) + PK[m - 2 * i + 2] * PK[n - 2 * j + 2]
            for t, w in acc.items():
                rr.append(fc); cc.append(t); vv.append(w)
    for k, (I, J) in enumerate(fine):
        rr.append(P.clsidx[I + Nf, J + Nf]); cc.append(nc + k); vv.append(1.0)
    for s in range(P.nsing):
        rr.append(P.ncls + s); cc.append(nc + nf + s); vv.append(1.0)
    M = sp.coo_matrix((vv, (rr, cc)), shape=(P.ncls + P.nsing, nc + nf + P.nsing)).tocsr()
    # mass check: a refined coarse class keeps its integral
    cobj_f = np.concatenate([hf * hf * P.mult, [sing_mass(b, R) for (b, R) in P.sings]])
    cobj = M.T @ cobj_f
    multc = np.array([1 if I == 0 else (4 if (J == 0 or I == J) else 8) for (I, J) in coarse], float)
    if nc:
        err = np.abs(cobj[:nc] - h_c * h_c * multc).max()
        assert err < 1e-12, f'mass check failed {err}'
    return M, coarse, fine, cobj


def bern_matrix(P, R, alpha, sub=1):
    import bernK
    Ub = (P.N + 2) * P.h
    brs = bernK.rows(P, P.h, P.N, R, alpha, Ub, sub=sub)
    rr, cc, vv, lo = [], [], [], []
    for t, (coef, rhs) in enumerate(brs):
        for k_, v_ in coef.items():
            rr.append(t); cc.append(k_); vv.append(v_)
        lo.append(rhs + getattr(P, 'etaK', 0.0) if rhs > 0 else 0.0)
    G = sp.coo_matrix((vv, (rr, cc)), shape=(len(brs), P.ncls + P.nsing)).tocsr()
    return G, np.array(lo)


class LP:
    def __init__(self, P, M, cobj, nspl, threads=1):
        self.P, self.M, self.nspl = P, M, nspl
        self.nvar = M.shape[1]
        hs = highspy.Highs()
        hs.setOptionValue('output_flag', False)
        hs.setOptionValue('threads', threads)
        hs.setOptionValue('solver', 'simplex')
        hs.setOptionValue('simplex_strategy', 1)
        lb = np.concatenate([np.full(nspl, -1e4), np.zeros(self.nvar - nspl)])
        ub = np.full(self.nvar, 1e4)
        hs.addVars(self.nvar, lb, ub)
        hs.changeColsCost(self.nvar, np.arange(self.nvar, dtype=np.int32), cobj)
        self.hs = hs
        self.activeA = set(); self.activeB = set()
        self.B = None; self.Blo = None

    def set_bern(self, G, lo):
        B = (G @ self.M).tocsr()
        B.eliminate_zeros()
        keep = np.nonzero(np.diff(B.indptr) > 0)[0]
        self.B = B[keep]; self.Blo = lo[keep]
        print(f'  Bernstein rows available: {self.B.shape[0]} (of {G.shape[0]})', flush=True)

    def add_bern(self, ids):
        ids = [i for i in ids if i not in self.activeB]
        if not ids:
            return 0
        G = self.B[np.array(ids)]
        self.hs.addRows(G.shape[0], self.Blo[ids], np.full(len(ids), highspy.kHighsInf), G.nnz,
                        G.indptr[:-1].astype(np.int32), G.indices.astype(np.int32), G.data)
        self.activeB.update(ids)
        return len(ids)

    def add_A(self, idx):
        idx = [i for i in idx if i not in self.activeA]
        if not idx:
            return 0
        idx = np.array(idx)
        _, GAf = self.P.rows(idx)
        GA = (GAf @ self.M).tocsr()
        sc = 1.0 / np.maximum(1e-12, abs(GA[:, :self.nspl]).max(axis=1).toarray().ravel())
        GA = (sp.diags(sc) @ GA).tocsr()
        lowA = eta_profile(self.P, self.P.u[idx], self.P.v[idx]) * sc
        self.hs.addRows(GA.shape[0], lowA, np.full(len(idx), highspy.kHighsInf), GA.nnz,
                        GA.indptr[:-1].astype(np.int32), GA.indices.astype(np.int32), GA.data)
        self.activeA.update(idx.tolist())
        return len(idx)

    def xf(self, x):
        return self.M @ x

    def solve(self):
        hs = self.hs
        hs.run()
        st = hs.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal:
            print('status', hs.modelStatusToString(st), '-> retry with IPM + crossover', flush=True)
            hs.setOptionValue('solver', 'ipm'); hs.setOptionValue('run_crossover', 'on')
            hs.run()
            hs.setOptionValue('solver', 'simplex')
            st = hs.getModelStatus()
            if st != highspy.HighsModelStatus.kOptimal:
                print('status after IPM', hs.modelStatusToString(st), flush=True)
                return None, None
        x = np.array(hs.getSolution().col_value)
        return x, hs.getInfo().objective_function_value / 2

    def run(self, max_iter=60, tolA=3e-5, tolK=1e-9, add_per_iter=3000, verbose=True):
        t0 = time.time(); x = val = None
        P = self.P
        for it in range(max_iter):
            x, val = self.solve()
            if x is None:
                break
            _, Ac = P.evaluate(self.xf(x))
            vA = eta_profile(P, P.u, P.v) - Ac
            badA = np.nonzero(vA > tolA)[0]
            newA = [i for i in badA[np.argsort(-vA[badA])] if i not in self.activeA][:add_per_iter]
            sl = self.B @ x - self.Blo
            badB = np.nonzero(sl < -tolK)[0]
            newB = [i for i in badB[np.argsort(sl[badB])] if i not in self.activeB][:4 * add_per_iter]
            if verbose:
                print(f'  it {it} val {val:.6f} ncand {len(P.u)} violB {len(badB)} ({-sl.min():.2e}) violA {len(badA)} '
                      f'({vA.max():.3e}) new {len(newB)}/{len(newA)} rows {self.hs.getNumRow()} t {time.time()-t0:.1f}',
                      flush=True)
            if not newA and not newB:
                break
            self.add_A(newA); self.add_bern(newB)
        return x, val


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--alpha', type=float, default=1.175)
    ap.add_argument('--alpha_str', type=str, default='47/40')
    ap.add_argument('--h', type=float, default=1 / 64)
    ap.add_argument('--h_c', type=float, default=1 / 32)
    ap.add_argument('--bands', type=str, default='0.8:1.25')   # 'r0:r1,r0:r1' (diamond radius of fine centres)
    ap.add_argument('--box', type=float, default=2.5)
    ap.add_argument('--sings', type=str, default='1.175:1.65')
    ap.add_argument('--procs', type=int, default=16)
    ap.add_argument('--levels', type=int, default=3)
    ap.add_argument('--out', type=str, default='')
    ap.add_argument('--batch', type=int, default=2000)
    ap.add_argument('--tolA', type=float, default=3e-5)
    ap.add_argument('--init_from', type=str, default='')
    ap.add_argument('--init_Athr', type=float, default=0.5)
    ap.add_argument('--init_Bthr', type=float, default=0.05)
    ap.add_argument('--etaA', type=float, default=0.0)
    ap.add_argument('--r_marg', type=float, default=0.0)
    ap.add_argument('--etaA2', type=float, default=0.0)
    ap.add_argument('--r_marg2', type=float, default=0.0)
    ap.add_argument('--mu0', type=float, default=0.0)
    ap.add_argument('--r0', type=float, default=0.4)
    ap.add_argument('--etaK', type=float, default=0.0)
    ap.add_argument('--r_supp', type=float, default=2.25)
    ap.add_argument('--certloop', type=int, default=0)
    ap.add_argument('--clip', type=float, default=1e-7)
    ap.add_argument('--cert_depth', type=int, default=6)
    ap.add_argument('--knotpts', type=int, default=0)   # also probe points ON coarse/fine knot lines at the levels
    ap.add_argument('--bsub', type=int, default=2)      # Bernstein K rows on sub x sub subcells of the fine cells
    a = ap.parse_args()
    h, hc = a.h, a.h_c
    N = int(round(a.box / h)); U = (N + 2) * h
    sings = [tuple(float(z) for z in s.split(':')) for s in a.sings.split(',')]
    bands = [tuple(float(z) for z in b.split(':')) for b in a.bands.split(',')] if a.bands else []
    P = Problem(a.alpha, h, N, sings, procs=a.procs)
    P.etaA = a.etaA; P.etaK = a.etaK; P.r_marg = a.r_marg
    P.etaA2 = a.etaA2; P.r_marg2 = a.r_marg2; P.mu0 = a.mu0; P.r0 = a.r0
    t0 = time.time()
    M, coarse, fine, cobj = build_map(P, hc, bands, a.r_supp)
    nspl = len(coarse) + len(fine)
    print(f'map: {len(coarse)} coarse (h_c={hc}) + {len(fine)} fine (h={h}) classes in bands {bands if hc > 0 else "all (plain)"}; '
          f'fine problem classes {P.ncls}; t={time.time()-t0:.1f}', flush=True)
    # level-1 candidates: grid at hg/4 everywhere (hg = h_c, or h in the plain mode), fine grid near the bands
    hg = hc if hc > 0 else h
    uc, vc = grid_points(hg / 4, U, lambda u, v: np.ones_like(u, bool))
    inb = (lambda u, v: np.any([(u + v >= b0 - 2 * hg) & (u + v <= b1 + 2 * hg) for (b0, b1) in bands], axis=0)) \
        if (bands and hc > 0) else (lambda u, v: np.zeros_like(u, bool))
    uf, vf = grid_points(h / 4, U, inb, off=0.37)
    uo, vo = [], []
    for k in range(1, 9):
        r = (hg / 4) * 2.0 ** (-k)
        for th in (0.5, 0.3, 0.15, 0.05, 0.01):
            uo.append(r * (1 - th)); vo.append(r * th)
    idx1 = P.add_points(np.concatenate([uc, uf, uo]), np.concatenate([vc, vf, vo]))
    print(f'level-1 candidates {len(idx1)} ({len(uc)} global, {len(uf)} band); t={time.time()-t0:.1f}', flush=True)
    lp = LP(P, M, cobj, nspl, threads=int(os.environ.get('HL_HIGHS_THREADS', '1')))
    G, lo = bern_matrix(P, sings[0][1], a.alpha, sub=a.bsub)
    lp.set_bern(G, lo)
    print(f'  Bernstein matrix built (sub={a.bsub}) t={time.time()-t0:.1f}', flush=True)
    initA = idx1[::2]
    initB = list(range(lp.B.shape[0]))
    if a.init_from:
        zc = np.load(a.init_from, allow_pickle=True)
        ic = json.loads(str(zc['info']))
        if abs(ic['alpha'] - a.alpha) > 1e-12 or [tuple(t) for t in ic['sings']] != sings:
            print(f"  note: init_from has alpha {ic['alpha']}, sings {ic['sings']} (used only as a starting point)", flush=True)
        Nz = ic['N']
        Pz = Problem(ic['alpha'], ic['h'], Nz, [tuple(t) for t in ic['sings']], procs=1)
        zval = lambda I, J: zc['x'][Pz.clsidx[I + Nz, J + Nz]] if I <= Nz else 0.0
        x0 = np.zeros(lp.nvar)
        if abs(ic['h'] - h) < 1e-15:
            # same spacing: fine classes of the map take the stored values; coarse variables (if any) stay 0
            for k, (I, J) in enumerate(fine):
                x0[len(coarse) + k] = zval(I, J)
            if coarse:
                raise SystemExit('init_from at the fine spacing needs --h_c 0')
        elif abs(ic['h'] - 2 * h) < 1e-15:
            if coarse:
                for t, (I, J) in enumerate(coarse):
                    x0[t] = zval(I, J)
            else:
                # plain fine basis: refine the coarse solution exactly
                Mc, coarse2, _, _ = build_map(P, 2 * h, [], a.r_supp)
                xc = np.zeros(Mc.shape[1])
                for t, (I, J) in enumerate(coarse2):
                    xc[t] = zval(I, J)
                xf_ = Mc @ xc
                for k, (I, J) in enumerate(fine):
                    x0[k] = xf_[P.clsidx[I + N, J + N]]
        else:
            raise SystemExit('init_from spacing must be h or 2h')
        x0[nspl:] = zc['x'][Pz.ncls:Pz.ncls + Pz.nsing]
        _, A0 = P.evaluate(lp.xf(x0))
        near = np.nonzero(A0 < a.init_Athr)[0]
        initA = np.unique(np.concatenate([near, idx1[::8]]))
        sl0 = lp.B @ x0 - lp.Blo
        initB = np.nonzero(sl0 < a.init_Bthr)[0].tolist()
        print(f'init_from {a.init_from}: {len(near)} near-active A + stride -> {len(initA)} A rows; '
              f'{len(initB)} near-active Bernstein rows; start value {cobj @ x0 / 2:.6f}, '
              f'min Bernstein slack {sl0.min():.2e}, min A on candidates {A0.min():.3e}', flush=True)
    lp.add_A(initA); lp.add_bern(initB)
    print(f'  initial rows {lp.hs.getNumRow()} t={time.time()-t0:.1f}', flush=True)
    x, val = lp.run(add_per_iter=a.batch, tolA=a.tolA)
    hist = [(1, val, len(P.u))]
    print(f'LEVEL 1 val {val:.6f}', flush=True)
    df1 = hg / 4
    for lev in range(2, a.levels + 1):
        df = df1 / 2 ** (lev - 1)
        grids = [grid_points(df, U, lambda u, v: np.ones_like(u, bool), off=off) for off in (0.5, 1.0 / 3 + 0.01 * lev)]
        if bands and hc > 0:
            grids.append(grid_points(h / 4 / 2 ** (lev - 1), U, inb, off=0.5))
        if a.knotpts:
            # points on knot lines u = m h (fine) at spacing df in v, and the mirror v = m h
            mm = np.arange(1, int(U / h) + 1) * h
            ss = (np.arange(0, int(U / df) + 1) + 0.29) * df
            Uk, Vk = np.meshgrid(mm, ss, indexing='ij')
            uk, vk = Uk.ravel(), Vk.ravel()
            u2 = np.concatenate([uk, vk]); v2 = np.concatenate([vk, uk])
            sel = (v2 <= u2) & (u2 + v2 > 0)
            grids.append((u2[sel], v2[sel]))
        for (ul, vl) in grids:
            Kl, Al, tmp = probe(P, lp.xf(x), ul, vl)
            etal = eta_profile(P, ul, vl)
            bad = np.nonzero(Al < etal - a.tolA)[0]
            print(f'level {lev} df={df:.6f}: probed {len(ul)} pts, violators {len(bad)}, minA {Al.min():.3e}', flush=True)
            rounds = 0
            while len(bad) > 0 and rounds < 30:
                viol = (etal - Al)[bad]
                pick = bad[np.argsort(-viol)[:a.batch]]
                newidx = P.add_points(ul[pick], vl[pick], pre=(tmp.Kpsi[pick], tmp.Apsi[pick]))
                lp.add_A(newidx)
                x, val = lp.run(add_per_iter=a.batch, tolA=a.tolA)
                Kl, Al = tmp.evaluate(lp.xf(x))
                bad = np.nonzero(Al < etal - a.tolA)[0]
                rounds += 1
                print(f'    round {rounds}: val {val:.6f} remaining violators {len(bad)} minA {Al.min():.3e}', flush=True)
        hist.append((lev, val, len(P.u)))
        print(f'LEVEL {lev} val {val:.6f} ncand {len(P.u)}', flush=True)
    xfin = lp.xf(x)
    if a.certloop:
        import subprocess
        from fractions import Fraction
        cdir = os.path.join(os.path.dirname(HERE), 'cert')
        for crnd in range(a.certloop):
            D_ = 2 ** 40
            aa = {}
            for I_ in range(P.N + 1):
                for J_ in range(I_ + 1):
                    vv_ = xfin[P.clsidx[I_ + P.N, J_ + P.N]]
                    if abs(vv_) < a.clip:
                        vv_ = 0.0
                    fr = Fraction(int(round(float(vv_) * D_)), D_)
                    if fr != 0:
                        aa[f'{I_},{J_}'] = str(fr)
            spec = dict(alpha=a.alpha_str, R=str(Fraction(sings[0][1]).limit_denominator(1000)),
                        h=str(Fraction(h).limit_denominator(1 << 20)), N=P.N,
                        c=str(Fraction(int(round(float(xfin[P.ncls]) * D_)), D_)), a=aa)
            sfn = (a.out or 'runs/tmp') + f'.cert{crnd}.json'
            json.dump(spec, open(sfn, 'w'))
            rfn = sfn.replace('.json', '.report.json')
            cmd = [sys.executable, '-I', os.path.join(cdir, 'cert_run.py'), sfn, '--only', 'MKA', '--Q', '8',
                   '--maxdepth', str(a.cert_depth), '--Kdepth', '4', '--procs', str(a.procs), '--out', rfn]
            t0c = time.time()
            subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            rep = json.load(open(rfn))
            fa = rep.get('A_fail', []); fk = rep.get('K_fail', [])
            print(f'CERTLOOP {crnd}: val {val:.6f} mass {rep.get("mass_half")} A-fail {len(fa)} K-fail {len(fk)} '
                  f't={time.time()-t0c:.0f}s', flush=True)
            if not fa and not fk:
                print('CERTIFIED (search-side verifier):', sfn, flush=True)
                break
            if fk and not fa:
                delta = 1e-7
                bump = set()
                for f in fk:
                    u0_, u1_, v0_, v1_ = [float(Fraction(z)) for z in f[:4]]
                    for i_ in range(int(np.floor(u0_ / h)) - 1, int(np.floor(u1_ / h)) + 3):
                        for j_ in range(int(np.floor(v0_ / h)) - 1, int(np.floor(v1_ / h)) + 3):
                            if abs(i_) <= P.N and abs(j_) <= P.N:
                                I_, J_ = max(abs(i_), abs(j_)), min(abs(i_), abs(j_))
                                bump.add(P.clsidx[I_ + P.N, J_ + P.N])
                xfin = xfin.copy()
                for cl in bump:
                    xfin[cl] += delta
                print(f'  K-fix: raised {len(bump)} classes by {delta}', flush=True)
                continue
            nu, nv = [], []
            for f in fa + fk:
                u0_, u1_, v0_, v1_ = [float(Fraction(z)) for z in f[:4]]
                for (tu, tv) in ((0.5, 0.5), (0.25, 0.25), (0.75, 0.25), (0.25, 0.75), (0.75, 0.75), (0.0, 0.5), (0.5, 0.0)):
                    uu_ = u0_ + tu * (u1_ - u0_); vv2 = v0_ + tv * (v1_ - v0_)
                    if vv2 <= uu_ and uu_ + vv2 > 0:
                        nu.append(uu_); nv.append(vv2)
            nu = np.array(nu); nv = np.array(nv)
            Kl, Al, tmp = probe(P, xfin, nu, nv)
            newidx = P.add_points(nu, nv, pre=(tmp.Kpsi, tmp.Apsi))
            lp.add_A(newidx)
            x, val = lp.run(add_per_iter=a.batch, tolA=a.tolA)
            xfin = lp.xf(x)
    Kc, Ac = P.evaluate(xfin)
    res = dict(alpha=a.alpha, h=h, N=N, box=a.box, sings=sings, val=val, hist=hist, U=U,
               c=xfin[P.ncls:P.ncls + P.nsing].tolist(), patches='', ncand=len(P.u), minA_cand=float(Ac.min()),
               h_c=hc, bands=bands, ncoarse=len(coarse), nfine=len(fine))
    print(json.dumps(res), flush=True)
    if a.out:
        np.savez(a.out, x=xfin, xlp=x, info=json.dumps(res), clsidx=P.clsidx, mult=P.mult)


if __name__ == '__main__':
    main()
