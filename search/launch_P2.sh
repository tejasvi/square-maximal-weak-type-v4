#!/bin/bash
# Run P2 (h = 1/32, alpha 47/40, R 33/20; Bernstein K rows on 2 x 2 sub-cells), started from the solution runs/w11.npz.
# Command reconstructed from the original launch file: the P2 line with its common options; host paths removed.
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 MKL_NUM_THREADS=2 MALLOC_ARENA_MAX=2 HL_HIGHS_THREADS=1
$PY cp_lp3_P2.py --alpha 1.175 --alpha_str 47/40 --sings 1.175:1.65 --etaA 0.002 --etaA2 0.0002 --mu0 0.02 --bsub 2 \
  --h 0.03125 --h_c 0 --box 2.5 --levels 3 --batch 2000 --tolA 3e-5 --r_marg 1.65 --r_marg2 2.6 --r0 0.4 --etaK 1e-4 \
  --r_supp 2.25 --certloop 10 --cert_depth 7 --procs 24 --init_from runs/w11.npz --out runs/p_P2.npz > runs/p_P2.log 2>&1
