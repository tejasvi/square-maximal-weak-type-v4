# Search programs and runs behind the certificate

Only the certificate `../cert/cert_h32_a4740_R3320_3p59123.json` enters the proof; the files here document how it was
found. `runs/r_R4.npz.cert2.json` is the certificate itself (identical bytes).

## Chain of runs

1. `runs/w11.npz`: the solution of an earlier run (at the same α, R and h), used as the starting point.
2. Run P2 (`launch_P2.sh`, driver `cp_lp3_P2.py`): Bernstein rows for K ≥ 0 and K ≥ 1 on D on 2 × 2 sub-cells, added
   lazily; margins for AK of 0.002 for r ≤ 1.65 and 0.0002 for r ≤ 2.6, and a larger margin near the origin. Its own
   certificate `runs/p_P2.npz.cert3.json` (bound 3.591224) has an isolated dip with AK about 6.5e-6 and was not used.
3. Run R4 (`launch_R4.sh`, driver `cp_lp3.py`): as P2, but with outer margin 0.0005 and a scan for narrow dips
   (AK ≥ half the margin on a grid of spacing 1/2048 for r ≤ 2.3), started from P2. Its loop with the first program:
   `cert0` had failures of (C4); `cert1` had failures of (C1) only, at the edge of the support (LP tolerance), and 396
   coefficient classes were raised by 1e-7; `cert2` is the certificate.

## Code

- `cp_lp3_P2.py` and `cp_lp3.py` are the drivers that ran P2 and R4. Both were rebuilt byte for byte from the edit
  history of the search code, and their SHA-256 digests match those recorded at the time of the runs.
- `cp_lp2.py` (problem setup and sampling grids), `bernK.py`, `bspl_closed.py`, `sing2.py` and `sing3.py` are imported
  by the drivers. They need NumPy, SciPy and HiGHS (`highspy`; HiGHS 1.15.1 with one thread was used).
- The loop with the first program calls `../cert/cert_run.py`; in this repository the first program is in
  `../checker/`, so copy or link it to `../cert/` before rerunning. A rerun can end at a slightly different certificate,
  because the path of the LP solver depends on its version and thread count; any certificate it prints has to pass the
  checkers on its own.
