"""hl47a cutting-plane LP, version 2 (numerical exploration, NOT a certificate).

Differences from cp_lp.py: closed-form L_alpha B (bspl_closed), offset multi-level candidate grids
(no candidate exactly on an axis or on a circle r = R_k), adaptive refinement: after convergence on the current
candidate set, a finer level is evaluated and violators are added.
K(u,v) = sum_k c_k (r^-alpha - R_k^-alpha)_+ + sum_ij a_ij B(u/h - i) B(v/h - j).
"""
import sys, os, time, json, argparse
import numpy as np
import scipy.sparse as sp
from multiprocessing import Pool
import highspy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bspl_closed import LBv, Bv

HERE = os.path.dirname(os.path.abspath(__file__))


def sing_mass(beta, R):
    return 2 * beta * R ** (2 - beta) / (2 - beta)


def _apsi_job(args):
    alpha, R, pts = args
    import warnings; warnings.simplefilter('ignore')
    import sing2
    out = np.empty(len(pts))
    for k, (u, v) in enumerate(pts):
        val = sing2.A_psi(alpha, R, u, v)
        out[k] = val if np.isfinite(val) else 1e8
    return out


def grid_points(df, U, region, off=1.0 / 3):
    """offset grid u=(m+off)df, v=(n+off)df, 0<=n<=m, u<=U, filtered by region(u,v)."""
    M = int(np.floor(U / df))
    m, n = np.meshgrid(np.arange(M + 1), np.arange(M + 1), indexing='ij')
    sel = n <= m
    u = (m[sel] + off) * df; v = (n[sel] + off) * df
    keep = (u <= U) & region(u, v)
    return u[keep], v[keep]


class Problem:
    def __init__(self, alpha, h, N, sings, procs=24, patches=None):
        self.alpha, self.h, self.N, self.sings, self.procs = alpha, h, N, sings, procs
        self.patches = patches
        self.npatch = 0 if patches is None else patches.n
        self.I = np.arange(-N, N + 1)
        cls = {}; mult = []
        clsidx = np.zeros((2 * N + 1, 2 * N + 1), dtype=np.int64)
        for a in range(-N, N + 1):
            for b in range(-N, N + 1):
                key = (max(abs(a), abs(b)), min(abs(a), abs(b)))
                if key not in cls:
                    cls[key] = len(mult); mult.append(0)
                clsidx[a + N, b + N] = cls[key]; mult[cls[key]] += 1
        self.clsidx = clsidx; self.mult = np.array(mult, float); self.ncls = len(mult)
        self.nsing = len(sings); self.nvar = self.ncls + self.nsing + self.npatch
        self.u = np.zeros(0); self.v = np.zeros(0)
        self.Kpsi = np.zeros((0, self.nsing)); self.Apsi = np.zeros((0, self.nsing))
        self.Kpat = np.zeros((0, self.npatch)); self.Apat = np.zeros((0, self.npatch))

    def add_points(self, u, v, cache=None, pre=None):
        """append candidate points; compute singular parts (parallel) unless pre=(Kp, Ap) given."""
        n0 = len(self.u)
        if pre is not None:
            Kp, Ap = pre[0], pre[1]
            self.u = np.concatenate([self.u, u]); self.v = np.concatenate([self.v, v])
            self.Kpsi = np.vstack([self.Kpsi, Kp]); self.Apsi = np.vstack([self.Apsi, Ap])
            if self.npatch:
                KP, AP = (pre[2], pre[3]) if len(pre) > 2 else self.patches.values(u, v)
                self.Kpat = np.vstack([self.Kpat, KP]); self.Apat = np.vstack([self.Apat, AP])
            return np.arange(n0, n0 + len(u))
        r = u + v
        Kp = np.zeros((len(u), self.nsing)); Ap = np.zeros((len(u), self.nsing))
        import sing3
        for k, (beta, R) in enumerate(self.sings):
            assert abs(beta - self.alpha) < 1e-12
            Kp[:, k] = np.maximum(r ** (-beta) - R ** (-beta), 0.0)
            vals = np.empty(len(u))
            for s0 in range(0, len(u), 50000):
                vals[s0:s0 + 50000] = sing3.A_psi_vec(self.alpha, R, u[s0:s0 + 50000], v[s0:s0 + 50000])
            vals[~np.isfinite(vals)] = 1e8
            Ap[:, k] = vals
        self.u = np.concatenate([self.u, u]); self.v = np.concatenate([self.v, v])
        self.Kpsi = np.vstack([self.Kpsi, Kp]); self.Apsi = np.vstack([self.Apsi, Ap])
        if self.npatch:
            KP, AP = self.patches.values(u, v)
            self.Kpat = np.vstack([self.Kpat, KP]); self.Apat = np.vstack([self.Apat, AP])
        return np.arange(n0, n0 + len(u))

    def tables(self, x):
        h, a = self.h, self.alpha
        S = x[:, None] / h - self.I[None, :]
        return Bv(S), LBv(S, a) * h ** (-a)

    def rows(self, idx):
        u, v = self.u[idx], self.v[idx]
        Bu, Lu = self.tables(u); Bvv, Lv = self.tables(v)
        rK, cK, vK, rA, cA, vA = [], [], [], [], [], []
        for t in range(len(idx)):
            im = np.nonzero(Bu[t])[0]; jn = np.nonzero(Bvv[t])[0]
            blk = np.outer(Bu[t, im], Bvv[t, jn]); c = self.clsidx[np.ix_(im, jn)]
            rK.append(np.full(c.size, t)); cK.append(c.ravel()); vK.append(blk.ravel())
            b1 = np.outer(Lu[t], Bvv[t, jn]); c1 = self.clsidx[:, jn]
            b2 = np.outer(Bu[t, im], Lv[t]); c2 = self.clsidx[im, :]
            rA.append(np.full(c1.size + c2.size, t))
            cA.append(np.concatenate([c1.ravel(), c2.ravel()])); vA.append(np.concatenate([b1.ravel(), b2.ravel()]))
        n = len(idx)
        GK = sp.coo_matrix((np.concatenate(vK), (np.concatenate(rK), np.concatenate(cK))), shape=(n, self.ncls)).tocsr()
        GA = sp.coo_matrix((np.concatenate(vA), (np.concatenate(rA), np.concatenate(cA))), shape=(n, self.ncls)).tocsr()
        # caps (conservative: lowering a positive singular entry only makes the >= constraint harder)
        GK = sp.hstack([GK, sp.csr_matrix(np.minimum(self.Kpsi[idx], 1e3))]).tocsr()
        GA = sp.hstack([GA, sp.csr_matrix(self.apsi_eff(self.u[idx], self.v[idx], self.Apsi[idx]))]).tocsr()
        if self.npatch:
            GK = sp.hstack([GK, sp.csr_matrix(self.Kpat[idx])]).tocsr()
            GA = sp.hstack([GA, sp.csr_matrix(self.Apat[idx])]).tocsr()
        return GK, GA

    def evaluate_xy(self, x, u, v, Kpsi, Apsi, Kpat=None, Apat=None):
        a = x[:self.ncls][self.clsidx]; c = x[self.ncls:self.ncls + self.nsing]; p = x[self.ncls + self.nsing:]
        out_K = np.empty(len(u)); out_A = np.empty(len(u))
        for s in range(0, len(u), 20000):
            e = min(len(u), s + 20000)
            Bu, Lu = self.tables(u[s:e]); Bvv, Lv = self.tables(v[s:e])
            BA = Bu @ a; LA = Lu @ a
            out_K[s:e] = np.einsum('ij,ij->i', BA, Bvv) + Kpsi[s:e] @ c
            out_A[s:e] = np.einsum('ij,ij->i', LA, Bvv) + np.einsum('ij,ij->i', BA, Lv) + Apsi[s:e] @ c
            if self.npatch:
                out_K[s:e] += Kpat[s:e] @ p; out_A[s:e] += Apat[s:e] @ p
        return out_K, out_A

    def apsi_eff(self, u, v, Apsi):
        Ap_ = Apsi.copy()
        mu = getattr(self, 'mu0', 0.0)
        if mu > 0:
            import sing2
            rr_ = u + v
            Ap_[:, 0] -= np.where(rr_ < self.r0, mu * sing2.C_alpha(self.alpha) * rr_ ** (-2 * self.alpha), 0.0)
        return np.minimum(Ap_, 1e4)

    def evaluate(self, x):
        """K and the EFFECTIVE A K (singular entries as in the LP rows: mu-adjusted and capped; implies the true constraint)."""
        return self.evaluate_xy(x, self.u, self.v, self.Kpsi, self.apsi_eff(self.u, self.v, self.Apsi), self.Kpat, self.Apat)


def eta_profile(P, u, v):
    r = u + v
    e1 = getattr(P, 'etaA', 0.0); r1 = getattr(P, 'r_marg', 0.0)
    e2 = getattr(P, 'etaA2', 0.0); r2 = getattr(P, 'r_marg2', 0.0)
    return np.where(r <= r1, e1, np.where(r <= r2, e2, 0.0))


def run(P, init_idx, max_iter=60, tolA=1e-6, tolK=1e-9, add_per_iter=5000, verbose=True, hs=None, active=None):
    inf = highspy.kHighsInf
    if hs is None:
        hs = highspy.Highs()
        hs.setOptionValue('output_flag', False)
        hs.setOptionValue('threads', int(os.environ.get('HL_HIGHS_THREADS', '1')))
        hs.setOptionValue('solver', 'simplex')
        hs.setOptionValue('simplex_strategy', 1)
        plb = P.patches.lb if P.npatch else np.zeros(0)
        pub = P.patches.ub if P.npatch else np.zeros(0)
        lb = np.concatenate([np.full(P.ncls, -1e4), np.zeros(P.nsing), plb])
        ub = np.concatenate([np.full(P.ncls, 1e4), np.full(P.nsing, 1e4), pub])
        hs.addVars(P.nvar, lb, ub)
        pm = P.patches.mass if P.npatch else np.zeros(0)
        cobj = np.concatenate([P.h * P.h * P.mult, [sing_mass(b, R) for (b, R) in P.sings], pm])
        hs.changeColsCost(P.nvar, np.arange(P.nvar, dtype=np.int32), cobj)
        active = (set(), set())
    activeK, activeA = active
    rD = lambda idx: np.where(P.u[idx] + P.v[idx] <= 1 + 1e-12, 1.0 + getattr(P, 'etaK', 0.0), 0.0)

    def add_rows(idxK, idxA):
        if len(idxK):
            idxK = np.array(idxK)
            GK, _ = P.rows(idxK)
            hs.addRows(GK.shape[0], rD(idxK), np.full(len(idxK), inf), GK.nnz,
                       GK.indptr[:-1].astype(np.int32), GK.indices.astype(np.int32), GK.data)
            activeK.update(idxK.tolist())
        if len(idxA):
            idxA = np.array(idxA)
            _, GA = P.rows(idxA)
            sc = 1.0 / np.maximum(1e-12, np.maximum(abs(GA[:, :P.ncls]).max(axis=1).toarray().ravel(),
                                                    abs(GA[:, P.ncls + P.nsing:]).max(axis=1).toarray().ravel() if P.npatch else 0))
            GA = (sp.diags(sc) @ GA).tocsr()
            lowA = eta_profile(P, P.u[idxA], P.v[idxA]) * sc   # (mu-regularisation is applied inside P.rows)
            hs.addRows(GA.shape[0], lowA, np.full(len(idxA), inf), GA.nnz,
                       GA.indptr[:-1].astype(np.int32), GA.indices.astype(np.int32), GA.data)
            activeA.update(idxA.tolist())

    if getattr(P, 'amp', None) and not getattr(P, '_amp_added', False):
        # smoothness: |h^-alpha kappa (Delta^4_i a)_{m j}| <= amp for m >= 0, j >= 0 with |m h| + |j h| >= amp_r0
        N = P.N; al = P.alpha
        kap = -2.0 / (al * (1 - al) * (2 - al) * (3 - al)) if abs(al - 1) > 1e-12 else 1.0
        sc0 = P.h ** (-al) * abs(kap)
        w = [1.0, -4.0, 6.0, -4.0, 1.0]
        rr, cc, vv = [], [], []
        nr = 0
        for m in range(0, N + 3):
            for j in range(0, N + 1):
                if (m + j) * P.h < P.amp_r0:
                    continue
                coef = {}
                for k in range(5):
                    i = m - (k - 2)
                    if -N <= i <= N:
                        cidx = P.clsidx[i + N, j + N]
                        coef[cidx] = coef.get(cidx, 0.0) + w[k]
                coef = {c_: v_ for c_, v_ in coef.items() if v_ != 0.0}
                if not coef:
                    continue
                for c_, v_ in coef.items():
                    rr.append(nr); cc.append(c_); vv.append(v_)
                nr += 1
        G = sp.coo_matrix((vv, (rr, cc)), shape=(nr, P.nvar)).tocsr()
        bound = P.amp / sc0
        hs.addRows(nr, np.full(nr, -bound), np.full(nr, bound), G.nnz,
                   G.indptr[:-1].astype(np.int32), G.indices.astype(np.int32), G.data)
        P._amp_added = True
        print(f'  added {nr} smoothness rows, |D4 a| <= {bound:.4g} (amplitude {P.amp})', flush=True)
    if getattr(P, 'bernK', 0) and not getattr(P, '_bern_added', False):
        import bernK
        Ub = (P.N + 2) * P.h
        brs = bernK.rows(P, P.h, P.N, P.sings[0][1], P.alpha, Ub, sub=P.bernK)
        fixed = set()
        if getattr(P, 'r_supp', None):
            fixed = {P.clsidx[i + P.N, j + P.N] for i in range(0, P.N + 1) for j in range(0, i + 1) if (i + j) * P.h > P.r_supp}
        rr, cc, vv, lo = [], [], [], []
        t = 0
        for (coef, rhs) in brs:
            free = [k_ for k_ in coef if k_ < P.ncls and k_ not in fixed and coef[k_] != 0.0]
            if not free and P.ncls not in coef:
                continue                      # K = 0 identically there (all coefficients fixed to 0)
            for k_, v_ in coef.items():
                rr.append(t); cc.append(k_); vv.append(v_)
            lo.append(rhs + getattr(P, "etaK", 0.0) if rhs > 0 else 0.0)
            t += 1
        G = sp.coo_matrix((vv, (rr, cc)), shape=(t, P.nvar)).tocsr()
        hs.addRows(G.shape[0], np.array(lo), np.full(G.shape[0], inf), G.nnz,
                   G.indptr[:-1].astype(np.int32), G.indices.astype(np.int32), G.data)
        P._bern_added = True
        print(f'  added {G.shape[0]} Bernstein K rows (sub={P.bernK})', flush=True)
    if getattr(P, 'r_supp', None) and not getattr(P, '_supp_added', False):
        # zero spline coefficients for B-splines centred beyond r_supp (diamond radius of the centre)
        zero = sorted({P.clsidx[i + P.N, j + P.N] for i in range(0, P.N + 1) for j in range(0, i + 1)
                       if (i + j) * P.h > P.r_supp})
        hs.changeColsBounds(len(zero), np.array(zero, dtype=np.int32), np.zeros(len(zero)), np.zeros(len(zero)))
        P._supp_added = True
        print(f'  fixed {len(zero)} spline classes to 0 beyond r_supp = {P.r_supp}', flush=True)
    new0K = [i for i in init_idx if i not in activeK]
    new0A = [i for i in init_idx if i not in activeA]
    add_rows(new0K, new0A)
    t0 = time.time(); x = None; val = None
    for it in range(max_iter):
        hs.run()
        st = hs.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal:
            print('status', hs.modelStatusToString(st), '-> retry with IPM + crossover', flush=True)
            hs.setOptionValue('solver', 'ipm'); hs.setOptionValue('run_crossover', 'on')
            hs.run()
            hs.setOptionValue('solver', 'simplex')
            st = hs.getModelStatus()
            if st != highspy.HighsModelStatus.kOptimal:
                print('status after IPM', hs.modelStatusToString(st), flush=True); break
        x = np.array(hs.getSolution().col_value)
        val = hs.getInfo().objective_function_value / 2
        Kc, Ac = P.evaluate(x)
        rhs = np.where(P.u + P.v <= 1 + 1e-12, 1.0 + getattr(P, 'etaK', 0.0), 0.0)
        vK = rhs - Kc
        # A violation relative to the spline-part scale of the row (rows scaled that way in the LP)
        vA = eta_profile(P, P.u, P.v) - Ac
        badK = np.nonzero(vK > tolK)[0]; badA = np.nonzero(vA > tolA)[0]
        newK = [i for i in badK[np.argsort(-vK[badK])] if i not in activeK][:add_per_iter]
        newA = [i for i in badA[np.argsort(-vA[badA])] if i not in activeA][:add_per_iter]
        if verbose:
            print(f'  it {it} val {val:.6f} ncand {len(P.u)} violK {len(badK)} ({vK.max():.2e}) violA {len(badA)} '
                  f'({vA.max():.3e}) new {len(newK)}/{len(newA)} rows {hs.getNumRow()} t {time.time()-t0:.1f}', flush=True)
        if not newK and not newA:
            break
        add_rows(newK, newA)
    return x, val, hs, (activeK, activeA)


def probe(P, x, u, v):
    """evaluate K and A K at new points (computes singular parts)."""
    tmp = Problem.__new__(Problem)
    tmp.__dict__.update(P.__dict__)
    tmp.u = np.zeros(0); tmp.v = np.zeros(0)
    tmp.Kpsi = np.zeros((0, P.nsing)); tmp.Apsi = np.zeros((0, P.nsing))
    tmp.Kpat = np.zeros((0, P.npatch)); tmp.Apat = np.zeros((0, P.npatch))
    tmp.add_points(u, v)
    K, A = tmp.evaluate(x)
    return K, A, tmp


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--alpha', type=float, default=1.2)
    ap.add_argument('--h', type=float, default=0.0625)
    ap.add_argument('--box', type=float, default=2.75)
    ap.add_argument('--sings', type=str, default='')
    ap.add_argument('--procs', type=int, default=16)
    ap.add_argument('--levels', type=int, default=3)
    ap.add_argument('--out', type=str, default='')
    ap.add_argument('--batch', type=int, default=1500)
    ap.add_argument('--tolA', type=float, default=3e-5)
    ap.add_argument('--init_from', type=str, default='')
    ap.add_argument('--etaA', type=float, default=0.0)
    ap.add_argument('--bernK', type=int, default=0)
    ap.add_argument('--certloop', type=int, default=0)
    ap.add_argument('--clip', type=float, default=1e-7)
    ap.add_argument('--cert_depth', type=int, default=5)
    ap.add_argument('--alpha_str', type=str, default='6/5')
    ap.add_argument('--etaA2', type=float, default=0.0)
    ap.add_argument('--r_marg2', type=float, default=0.0)
    ap.add_argument('--mu0', type=float, default=0.0)
    ap.add_argument('--r0', type=float, default=0.4)
    ap.add_argument('--r_supp', type=float, default=0.0)
    ap.add_argument('--etaK', type=float, default=0.0)
    ap.add_argument('--r_marg', type=float, default=0.0)
    ap.add_argument('--amp', type=float, default=0.0)
    ap.add_argument('--amp_r0', type=float, default=0.25)
    ap.add_argument('--patches', type=str, default='')
    ap.add_argument('--radial', type=str, default='')  # "pu:pv:hh:P,..."
    a = ap.parse_args()
    h = a.h; N = int(round(a.box / h)); U = (N + 2) * h
    sings = [tuple(float(z) for z in s.split(':')) for s in a.sings.split(',')] if a.sings else \
        [(a.alpha, R) for R in (1.5, 1.75, 2.0)]
    os.makedirs(os.path.join(HERE, 'cache'), exist_ok=True)
    pat = None
    parts = []
    if a.patches:
        from patches import Patches
        pp = Patches([tuple(float(z) if k < 3 else int(z) for k, z in enumerate(sp_.split(':'))) for sp_ in a.patches.split(',')], a.alpha)
        pp.lb = np.full(pp.n, -1e4); pp.ub = np.full(pp.n, 1e4)
        parts.append(pp)
    if a.radial:
        from extras import RadialCols
        parts.append(RadialCols([float(z) for z in a.radial.split(',')], a.alpha))
    if parts:
        from extras import Combined
        pat = Combined(parts)
        print('extra columns', pat.n, flush=True)
    P = Problem(a.alpha, h, N, sings, procs=a.procs, patches=pat)
    P.amp = a.amp if a.amp > 0 else None; P.amp_r0 = a.amp_r0
    P.etaA = a.etaA; P.etaK = a.etaK; P.r_marg = a.r_marg
    P.bernK = a.bernK; P.r_supp = a.r_supp if a.r_supp > 0 else None
    P.etaA2 = a.etaA2; P.r_marg2 = a.r_marg2; P.mu0 = a.mu0; P.r0 = a.r0
    t0 = time.time()
    df1 = h / 4
    u1, v1 = grid_points(df1, U, lambda u, v: np.ones_like(u, bool))
    # near-origin and near-axis micro points
    uo, vo = [], []
    for k in range(1, 9):
        r = df1 * 2.0 ** (-k)
        for th in (0.5, 0.3, 0.15, 0.05, 0.01):
            uo.append(r * (1 - th)); vo.append(r * th)
    uo = np.array(uo); vo = np.array(vo)
    idx1 = P.add_points(np.concatenate([u1, uo]), np.concatenate([v1, vo]))
    print(f'setup alpha={a.alpha} h={h} N={N} U={U} level1 {len(idx1)} pts nvar={P.nvar} t={time.time()-t0:.1f}', flush=True)
    stride_sel = idx1[::2]
    if a.init_from:
        # choose initial rows where a coarser solution is nearly active (prolongation is implicit: evaluate it here)
        zc = np.load(a.init_from, allow_pickle=True)
        ic = json.loads(str(zc['info']))
        Pc = Problem(ic['alpha'], ic['h'], ic['N'], [tuple(t) for t in ic['sings']], procs=a.procs)
        Pc.add_points(P.u, P.v)
        Kc0, Ac0 = Pc.evaluate(zc['x'])
        rhs0 = np.where(P.u + P.v <= 1 + 1e-12, 1.0, 0.0)
        near = np.nonzero((Kc0 - rhs0 < 2e-2) | (Ac0 < 0.5))[0]
        coarse = idx1[::8]
        stride_sel = np.unique(np.concatenate([near, coarse]))
        print(f'init_from {a.init_from}: {len(near)} near-active + {len(coarse)} coarse -> {len(stride_sel)} initial points', flush=True)
    x, val, hs, active = run(P, stride_sel, add_per_iter=a.batch)
    hist = [(1, val, len(P.u))]
    print(f'LEVEL 1 val {val:.6f}', flush=True)
    for lev in range(2, a.levels + 1):
        df = df1 / 2 ** (lev - 1)
        for off in (0.5, 1.0 / 3 + 0.01 * lev):
            ul, vl = grid_points(df, U, lambda u, v: np.ones_like(u, bool), off=off)
            Kl, Al, tmp = probe(P, x, ul, vl)
            rhs = np.where(ul + vl <= 1 + 1e-12, 1.0 + a.etaK, 0.0)
            etal = eta_profile(P, ul, vl)
            bad = np.nonzero((Al < etal - a.tolA) | (Kl < rhs - 1e-7))[0]
            print(f'level {lev} off {off:.3f} df={df:.6f}: probed {len(ul)} pts, violators {len(bad)}, '
                  f'minA {Al.min():.3e}, minK-rhs {(Kl-rhs).min():.2e}', flush=True)
            rounds = 0
            while len(bad) > 0 and rounds < 30:
                # add the worst violators in modest batches (keeps dual-simplex re-solves short)
                viol = np.maximum((etal - Al)[bad], (rhs - Kl)[bad])
                pick = bad[np.argsort(-viol)[:a.batch]]
                pre = (tmp.Kpsi[pick], tmp.Apsi[pick]) + ((tmp.Kpat[pick], tmp.Apat[pick]) if P.npatch else ())
                newidx = P.add_points(ul[pick], vl[pick], pre=pre)
                x, val, hs, active = run(P, newidx, hs=hs, active=active, add_per_iter=a.batch)
                Kl, Al = tmp.evaluate(x)
                bad = np.nonzero((Al < etal - a.tolA) | (Kl < rhs - 1e-7))[0]
                rounds += 1
                print(f'    round {rounds}: val {val:.6f} remaining violators {len(bad)} minA {Al.min():.3e}', flush=True)
        hist.append((lev, val, len(P.u)))
        print(f'LEVEL {lev} val {val:.6f} ncand {len(P.u)}', flush=True)
    if a.certloop:
        import subprocess
        from fractions import Fraction
        cdir = os.path.join(os.path.dirname(HERE), 'cert')
        for crnd in range(a.certloop):
            D_ = 2 ** 40
            aa = {}
            for I_ in range(P.N + 1):
                for J_ in range(I_ + 1):
                    vv_ = x[P.clsidx[I_ + P.N, J_ + P.N]]
                    if abs(vv_) < a.clip:
                        vv_ = 0.0          # LP-tolerance noise -> exactly zero
                    fr = Fraction(int(round(float(vv_) * D_)), D_)
                    if fr != 0:
                        aa[f'{I_},{J_}'] = str(fr)
            spec = dict(alpha=a.alpha_str, R=str(Fraction(sings[0][1]).limit_denominator(1000)),
                        h=str(Fraction(h).limit_denominator(1 << 20)), N=P.N,
                        c=str(Fraction(int(round(float(x[P.ncls]) * D_)), D_)), a=aa)
            if P.npatch:
                # B-spline patches -> extra fine tensor-spline components (one per patch spacing)
                from patches import Patches
                off = P.ncls + P.nsing
                comps = {}
                for part in P.patches.parts:
                    if not isinstance(part, Patches):
                        raise SystemExit('certloop supports only B-spline patches as extra columns')
                    for k_, (orb, hh) in enumerate(part.cols):
                        val = x[off + k_]
                        if abs(val) < a.clip:
                            val = 0.0
                        fr = Fraction(int(round(float(val) * D_)), D_)
                        if fr == 0:
                            continue
                        cu, cv = orb[0]
                        I_, J_ = int(round(abs(cu) / hh)), int(round(abs(cv) / hh))
                        I_, J_ = max(I_, J_), min(I_, J_)
                        comps.setdefault(hh, {})[f'{I_},{J_}'] = str(fr)
                    off += part.n
                spec['extra'] = []
                for hh, dct in comps.items():
                    n2 = max(max(int(k.split(',')[0]) for k in dct) + 2, 1)
                    spec['extra'].append(dict(h=str(Fraction(hh).limit_denominator(1 << 20)), N=n2, a=dct))
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
                # K >= 0 deficits of LP-tolerance size (~1e-9): raise the coefficients of every B-spline overlapping a
                # failing cell by delta (changes A K by <= delta * max|A B| << margins) and re-verify
                delta = 1e-7
                bump = set()
                for f in fk:
                    u0_, u1_, v0_, v1_ = [float(Fraction(z)) for z in f[:4]]
                    for i_ in range(int(np.floor(u0_ / h)) - 1, int(np.floor(u1_ / h)) + 3):
                        for j_ in range(int(np.floor(v0_ / h)) - 1, int(np.floor(v1_ / h)) + 3):
                            if abs(i_) <= P.N and abs(j_) <= P.N:
                                I_, J_ = max(abs(i_), abs(j_)), min(abs(i_), abs(j_))
                                if (I_ + J_) * h <= (P.r_supp or 1e9):
                                    bump.add(P.clsidx[I_ + P.N, J_ + P.N])
                x = x.copy()
                for cl in bump:
                    x[cl] += delta
                print(f'  K-fix: raised {len(bump)} classes by {delta}', flush=True)
                continue
            nu, nv = [], []
            for f in fa + fk:
                u0_, u1_, v0_, v1_ = [float(Fraction(z)) for z in f[:4]]
                for (tu, tv) in ((0.5, 0.5), (0.25, 0.25), (0.75, 0.25), (0.25, 0.75), (0.75, 0.75)):
                    uu_ = u0_ + tu * (u1_ - u0_); vv2 = v0_ + tv * (v1_ - v0_)
                    if vv2 <= uu_:
                        nu.append(uu_); nv.append(vv2)
            nu = np.array(nu); nv = np.array(nv)
            Kl, Al, tmp = probe(P, x, nu, nv)
            newidx = P.add_points(nu, nv, pre=(tmp.Kpsi, tmp.Apsi) + ((tmp.Kpat, tmp.Apat) if P.npatch else ()))
            x, val, hs, active = run(P, newidx, hs=hs, active=active, add_per_iter=a.batch)
    Kc, Ac = P.evaluate(x)
    r = P.u + P.v
    res = dict(alpha=a.alpha, h=h, N=N, box=a.box, sings=sings, val=val, hist=hist, U=U, c=x[P.ncls:P.ncls + P.nsing].tolist(), patches=a.patches,
               ncand=len(P.u), minA_cand=float(Ac.min()))
    print(json.dumps(res), flush=True)
    if a.out:
        np.savez(a.out, x=x, info=json.dumps(res), clsidx=P.clsidx, mult=P.mult)
