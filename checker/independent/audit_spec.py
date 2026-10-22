#!/usr/bin/env python3
"""Audit pipeline (47a) for one kernel spec in the DEFS.md format.

usage: audit_spec.py SPEC CLAIM OUTDIR [--procs 8]

Steps (all logs/reports in OUTDIR):
  1. snapshot of the spec (spec.snapshot.json) + sha256 of the spec and of the checker files;
  2. F1-F4 spot checks by rigorous quadrature at the spec's (alpha, R) (quad_A.py spotcheck, 8 points per identity),
     and the model/closed-form tests test_check.py, test_out.py at this spec's (alpha, R, h);
  3. full check C1-C4 (hl_check.py) and a --tight C4 run (informative minima);
  4. true minima of A K on 33x33 point grids of the 6 knot cells with the smallest tight lower bounds (3 overall, 3 with
     u + v < R), and end-to-end quadrature of A K from the definition at those minima (e2e_check.py);
  4b. minima scan of A K over ALL knot cells of 0 <= q <= p (9 x 9 points per cell, parallel);
  5. controls: H1 claim = mass - 1e-5 (C3 must FAIL); H2 bump a_{knot nearest the global minimum} += delta, the smallest
     delta in a fixed list giving a negative grid minimum of A K (witness), then C4 at maxdepth 8, the depth of the full
     check (must FAIL; the full check is the unperturbed reference); C1 control (outermost nonzero class made negative,
     witness K < 0 at its knot) and C2 control (class of the knot at the corner (1,0) of D lowered, witness K < 1 there),
     each run at the same kdepth as an unperturbed reference run (6, else 8): the reference must PASS, the control FAIL.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from hl_core import Spec, A  # noqa: E402

PY = sys.executable


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def run(args, log):
    with open(log, "w") as f:
        r = subprocess.run(["nice", "-n", "10", PY, "-I"] + args, stdout=f, stderr=subprocess.STDOUT, cwd=HERE)
    return r.returncode


def start(args, log):
    f = open(log, "w")
    return subprocess.Popen(["nice", "-n", "10", PY, "-I"] + args, stdout=f, stderr=subprocess.STDOUT, cwd=HERE), f


def AK(sp, u, v):
    a1, a2 = sp.AS_point(u, v)
    return a1 + a2 + sp.cA * sp.APsi_point(u, v)


def grid_min(sp, p, q, n):
    best = None
    for a_ in range(n + 1):
        for b_ in range(n + 1):
            u = sp.h * (p + Fr(a_, n)); v = sp.h * (q + Fr(b_, n))
            if u + v == sp.R or u + v == 0:
                continue
            val = AK(sp, u, v)
            if not val.is_finite():
                raise ValueError("non-finite A K value at (%s, %s)" % (u, v))
            if best is None or val < best[0]:
                best = (val, u, v)
    return best


def _scan_cells(args):
    spec_path, cells, n = args
    sp = Spec(spec_path)
    out = []
    for (p, q) in cells:
        best = None
        for a_ in range(n + 1):
            for b_ in range(n + 1):
                u = sp.h * (p + Fr(a_, n)); v = sp.h * (q + Fr(b_, n))
                if u + v == sp.R or u + v == 0:
                    continue
                val = AK(sp, u, v)
                if val.is_finite() and (best is None or val < best[0]):
                    best = (val, u, v)
                elif not val.is_finite() and not (val > 0):
                    raise ValueError("non-finite, non-positive A K at (%s, %s)" % (u, v))
        if best is not None:
            out.append((float(best[0].mid()), best[0].str(10), str(best[1]), str(best[2]), p, q))
    return out


def full_minima_scan(spec_path, procs, n=8):
    """A K on an (n+1) x (n+1) point grid of every knot cell 0 <= q <= p where K is not identically 0."""
    import multiprocessing as mp
    sys.path.insert(0, HERE)
    import hl_check
    sp = Spec(spec_path)
    cells = hl_check.c4_cells(sp)
    chunks = [(spec_path, cells[k::procs], n) for k in range(procs)]
    with mp.Pool(procs) as pool:
        res = [r for part in pool.map(_scan_cells, chunks) for r in part]
    res.sort()
    return res, len(cells)


def discriminating_run(od, snap, ctl_path, claim):
    """run the unperturbed spec and the control at the SAME refinement depth; the first depth (6, then 8) at which the
    unperturbed spec passes is used. Returns (kdepth, unperturbed passes, control fails); (None, False, False) if the
    unperturbed spec does not pass at either depth (the control would not discriminate)."""
    tag = claim.upper()
    for kd in ("6", "8"):
        ref = os.path.join(od, "%sref_kd%s.log" % (tag, kd))
        run(["hl_check.py", snap, "--claim", "100", "--only", claim, "--kdepth", kd], ref)
        if "OVERALL (%s): PASS" % claim in open(ref).read():
            ctl = os.path.join(od, "%sctl_kd%s.log" % (tag, kd))
            run(["hl_check.py", ctl_path, "--claim", "100", "--only", claim, "--kdepth", kd], ctl)
            return int(kd), True, "OVERALL (%s): FAIL" % claim in open(ctl).read()
    return None, False, False


def kc_controls(od, snap, sp):
    """C1 control: the outermost nonzero class set to a negative value (witness K < 0 at its knot); C2 control: the class of
    the knot nearest the corner (1,0) of D (inside D) lowered (witness K < 1 there). Each checked with hl_check (C1 / C2)."""
    out = {}
    d0 = json.load(open(snap))

    def K(s2, u, v):
        return s2.cA * s2.Psi(A(u + v)) + A(s2.S_point(u, v))
    # C1
    nz = [(I + J, I, J) for (I, J), v in sp.acls.items() if v != 0]
    _, I, J = max(nz)
    key = "%d,%d" % (I, J)
    for val in (Fr(-1, 10**3), Fr(-1, 10**2), Fr(-1, 10)):
        d = json.loads(json.dumps(d0)); d["a"][key] = str(val)
        path = os.path.join(od, "C1ctl.json"); json.dump(d, open(path, "w"))
        s2 = Spec(path)
        w = K(s2, s2.h * I, s2.h * J)
        if w < 0:
            break
    kd, unp, ctl = discriminating_run(od, snap, path, "c1")
    out["C1"] = {"class": key, "new_value": str(val), "witness_K": w.str(8), "at": [str(s2.h * I), str(s2.h * J)],
                 "kdepth": kd, "unperturbed_passes": unp, "fails": ctl,
                 "logs": ["C1ref_kd%s.log" % kd, "C1ctl_kd%s.log" % kd]}
    # C2
    n = int(1 / sp.h)
    I2, J2 = n, 0                          # knot (n h, 0) = (1,0) if 1/h is an integer, else the last knot inside D
    u2 = sp.h * I2
    k0 = K(sp, u2, Fr(0))
    delta = max(Fr(3, 1000), Fr(9, 4) * 3 * Fr(float((k0 - 1).upper())).limit_denominator(10**9))
    key2 = "%d,%d" % (I2, J2)
    d = json.loads(json.dumps(d0)); d["a"][key2] = str(Fr(d["a"].get(key2, "0")) - delta)
    path2 = os.path.join(od, "C2ctl.json"); json.dump(d, open(path2, "w"))
    s3 = Spec(path2)
    w2 = K(s3, u2, Fr(0))
    kd2, unp2, ctl2 = discriminating_run(od, snap, path2, "c2")
    out["C2"] = {"class": key2, "delta": str(delta), "witness_K": w2.str(8), "orig_K": k0.str(8), "at": [str(u2), "0"],
                 "point_in_D": u2 <= 1, "witness_below_1": bool(w2 < 1), "kdepth": kd2, "unperturbed_passes": unp2,
                 "fails": ctl2, "logs": ["C2ref_kd%s.log" % kd2, "C2ctl_kd%s.log" % kd2]}
    return out


def parse_spotF(path):
    """F1-F3 lines: the quadrature-minus-closed-form ball must contain 0 (or |mid| <= 1e-15); F4 lines: A Psi >= 0 and
    non-increasing in u and v (A Psi printed as exactly 0 when u, v >= R counts as satisfied)."""
    import re
    n = 0; bad = []
    for line in open(path):
        if line.startswith(("F1", "F2", "F3")):
            n += 1
            d = re.search(r"diff \[([^\]]*)\]", line).group(1).strip()
            if not d.startswith("+/-"):
                mid, rad = (float(z) for z in d.split("+/-"))
                if abs(mid) > rad and abs(mid) > 1e-15:
                    bad.append(line.strip())
        elif line.startswith("F4"):
            n += 1
            if "True; decreasing in u: True, in v: True" not in line and "A Psi 0 >= 0" not in line:
                bad.append(line.strip())
    return {"lines": n, "bad": bad, "ok": n == 32 and not bad}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("spec")
    ap.add_argument("claim")
    ap.add_argument("outdir")
    ap.add_argument("--procs", type=int, default=16)
    args = ap.parse_args()
    od = os.path.abspath(args.outdir)
    os.makedirs(od, exist_ok=True)
    snap = os.path.join(od, "spec.snapshot.json")
    shutil.copyfile(args.spec, snap)
    summ = {"spec": os.path.abspath(args.spec), "spec_sha256": sha(snap), "claim": args.claim,
            "code_sha256": {f: sha(os.path.join(HERE, f)) for f in
                            ("hl_core.py", "hl_check.py", "quad_A.py", "e2e_check.py", "audit_spec.py",
                             "test_check.py", "test_out.py")}}
    print("spec sha256", summ["spec_sha256"], flush=True)
    sp = Spec(snap)
    # 2. F1-F4 spot checks and the model tests at this spec's (alpha, R, h): started in parallel with step 3
    side = [start(["quad_A.py", "spotcheck", snap, "8", "31"], os.path.join(od, "spotF.log")),
            start(["test_check.py", snap], os.path.join(od, "test_check.log")),
            start(["test_out.py", snap], os.path.join(od, "test_out.log"))]

    # 3. full + tight
    run(["hl_check.py", snap, "--claim", args.claim, "--procs", str(args.procs), "--maxdepth", "8",
         "--out", os.path.join(od, "check.json")], os.path.join(od, "check.log"))
    full = json.load(open(os.path.join(od, "check.json")))
    summ["full"] = {k: {kk: vv for kk, vv in full[k].items() if kk in ("ok", "half_mass", "cells", "leaves", "min")}
                    for k in ("c1", "c2", "c3", "c4")}
    print("full check:", json.dumps(summ["full"]), flush=True)
    run(["hl_check.py", snap, "--claim", args.claim, "--procs", str(args.procs), "--maxdepth", "8", "--only", "c4",
         "--tight", "--out", os.path.join(od, "tight.json")], os.path.join(od, "tight.log"))
    tight = json.load(open(os.path.join(od, "tight.json")))
    summ["tight_min"] = tight["c4"]["min"]
    summ["tight_ok"] = tight["c4"]["ok"]
    print("tight min lower bound", summ["tight_min"], flush=True)
    # 4. minima + e2e
    rs = sorted(tight["c4"]["results"], key=lambda r: r["min"])
    picks = [(r["p"], r["q"]) for r in rs[:3]]
    inside = [(r["p"], r["q"]) for r in rs if (r["p"] + r["q"] + 2) * sp.h < sp.R and (r["p"], r["q"]) not in picks]
    picks += inside[:3]
    mins = []
    for (p, q) in picks:
        val, u, v = grid_min(sp, p, q, 32)
        mins.append({"cell": [p, q], "AK": val.str(10), "AK_mid": float(val.mid()), "u": str(u), "v": str(v)})
        print("cell (%d,%d): grid min A K = %s at (%s, %s)" % (p, q, val.str(8), u, v), flush=True)
    summ["minima"] = mins
    pts = []
    for m in mins:
        u, v = Fr(m["u"]), Fr(m["v"])
        if (u / sp.h).denominator == 1:
            u += sp.h / 1000
        if (v / sp.h).denominator == 1:
            v += sp.h / 1000
        pts.append("%s,%s" % (u, v))
    procs_e2e = [start(["e2e_check.py", snap, pt], os.path.join(od, "e2e_%d.log" % i)) for i, pt in enumerate(pts)]
    for pr, f in procs_e2e:
        pr.wait(); f.close()
    with open(os.path.join(od, "e2e.log"), "w") as f:
        for i in range(len(pts)):
            f.write(open(os.path.join(od, "e2e_%d.log" % i)).read())
    agree = [l for l in open(os.path.join(od, "e2e.log")) if "A K   quad" in l]
    summ["e2e"] = {"points": pts, "all_agree": len(agree) == len(pts) and all("agree: True" in l for l in agree),
                   "all_positive": all("positive: True" in l for l in agree)}
    print("e2e:", summ["e2e"], flush=True)
    # 4b. minima scan of A K over ALL knot cells of 0 <= q <= p (9 x 9 points per cell)
    scan, ncells = full_minima_scan(snap, args.procs)
    summ["full_scan"] = {"cells": ncells, "points_per_cell": 81, "smallest": scan[:20]}
    with open(os.path.join(od, "full_scan.json"), "w") as f:
        json.dump(scan, f)
    print("full minima scan: %d knot cells x 81 points; smallest A K = %s at (%s, %s) cell (%d,%d)" % (
        ncells, scan[0][1], scan[0][2], scan[0][3], scan[0][4], scan[0][5]), flush=True)
    # 5. controls
    half = Fr(full["c3"]["half_mass"].split("+/-")[0].strip("[ ")) if "+/-" in full["c3"]["half_mass"] else None
    h1_claim = str((half - Fr(1, 10**5)).limit_denominator(10**9)) if half is not None else "0"
    run(["hl_check.py", snap, "--claim", h1_claim, "--only", "c3"], os.path.join(od, "H1.log"))
    h1 = open(os.path.join(od, "H1.log")).read()
    summ["H1"] = {"claim": h1_claim, "c3_fail": "FAIL" in h1}
    g = min(mins, key=lambda m: m["AK_mid"])
    gu, gv = Fr(g["u"]), Fr(g["v"])
    I, J = round(gu / sp.h), round(gv / sp.h)
    key = "%d,%d" % (max(I, J), min(I, J))
    d0 = json.load(open(snap))
    h2 = None
    for delta in (Fr(1, 10**7), Fr(3, 10**7), Fr(1, 10**6), Fr(3, 10**6), Fr(1, 10**5), Fr(3, 10**5), Fr(1, 10**4),
                  Fr(3, 10**4), Fr(1, 10**3)):
        d = json.loads(json.dumps(d0))
        d["a"][key] = str(Fr(d["a"].get(key, "0")) + delta)
        path = os.path.join(od, "H2_bump.json")
        json.dump(d, open(path, "w"))
        s2 = Spec(path)
        best = None
        for (p, q) in ((I - 1, J - 1), (I, J - 1), (I - 1, J), (I, J)):
            if p < 0 or q < 0:
                continue
            b = grid_min(s2, p, q, 16)
            if best is None or b[0] < best[0]:
                best = b
        print("H2 delta %s at class %s: grid min A K = %s" % (delta, key, best[0].str(6)), flush=True)
        if best[0] < 0:
            h2 = {"class": key, "delta": str(delta), "witness_AK": best[0].str(8), "at": [str(best[1]), str(best[2])]}
            break
    if h2 is not None:
        run(["hl_check.py", os.path.join(od, "H2_bump.json"), "--claim", "100", "--only", "c4", "--procs",
             str(args.procs), "--maxdepth", "8", "--out", os.path.join(od, "H2.json")], os.path.join(od, "H2.log"))
        r2 = json.load(open(os.path.join(od, "H2.json")))
        h2["c4_fail"] = not r2["c4"]["ok"]
        h2["maxdepth"] = 8                    # same depth as the full check, whose C4 PASS is the unperturbed reference
        h2["unperturbed_passes"] = bool(full["c4"]["ok"])
        h2["failing_cells"] = [[r["p"], r["q"]] for r in r2["c4"]["results"] if not r["ok"]]
    summ["H2"] = h2
    # 5b. C1 / C2 negative controls (K < 0 at a known point; K < 1 at a known point of D)
    kc = kc_controls(od, snap, sp)
    summ["C1C2_controls"] = kc
    print("C1/C2 controls:", kc, flush=True)
    for pr, f in side:
        pr.wait(); f.close()
    tc = open(os.path.join(od, "test_check.log")).read()
    to = open(os.path.join(od, "test_out.log")).read()
    summ["model_tests"] = {
        "Ik_mismatches_0": "(1) mismatches: 0" in tc,
        "AS_model_viol_0": "(2) A S model violations: 0" in tc,
        "APsi_in_viol_0": "(3) A Psi model violations: 0" in tc,
        "bern_viol_0": "(4) Bernstein violations: 0" in tc,
        "M_mismatches_0": "M mismatches 0" in to,
        "J_deriv_mismatches_0": "J derivative mismatches 0" in to,
        "APsi_out_viol_0": "outside model violations: 0" in to}
    print("model tests at this spec:", summ["model_tests"], flush=True)
    summ["spotF"] = parse_spotF(os.path.join(od, "spotF.log"))
    print("F1-F4 spot checks:", summ["spotF"], flush=True)
    ok = all(summ["full"][k]["ok"] for k in ("c1", "c2", "c3", "c4")) and summ["tight_ok"] and \
        summ["e2e"]["all_agree"] and summ["e2e"]["all_positive"] and summ["H1"]["c3_fail"] and h2 is not None and \
        h2["c4_fail"] and h2["unperturbed_passes"] and all(summ["model_tests"].values()) and summ["spotF"]["ok"] and \
        kc["C1"]["fails"] and kc["C1"]["unperturbed_passes"] and kc["C2"]["fails"] and kc["C2"]["unperturbed_passes"] and \
        kc["C2"]["witness_below_1"] and kc["C2"]["point_in_D"]
    summ["pipeline_ok"] = ok
    json.dump(summ, open(os.path.join(od, "summary.json"), "w"), indent=1)
    print("H1:", summ["H1"], "\nH2:", h2, "\nPIPELINE", "OK" if ok else "NOT OK", flush=True)


if __name__ == "__main__":
    main()
