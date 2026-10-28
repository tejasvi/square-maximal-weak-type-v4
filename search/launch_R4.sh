#!/bin/bash
# Run R4 (as P2, with outer margin 0.0005 and the dense scan for narrow dips of A K), started from runs/p_P2.npz.
# Command reconstructed from the original launch file: the R4 line with its common options; host paths removed.
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 MKL_NUM_THREADS=2 MALLOC_ARENA_MAX=2 HL_HIGHS_THREADS=1
$PY cp_lp3.py --alpha 1.175 --alpha_str 47/40 --sings 1.175:1.65 --h 0.03125 --h_c 0 --box 2.5 --levels 3 --batch 2000 \
  --tolA 3e-5 --r_marg 1.65 --r_marg2 2.6 --r0 0.4 --etaK 1e-4 --r_supp 2.25 --bsub 2 --certloop 12 --cert_depth 7 \
  --procs 32 --pitscan 64 --pit_frac 0.5 --etaA 0.002 --etaA2 0.0005 --mu0 0.02 --init_from runs/p_P2.npz \
  --out runs/r_R4.npz > runs/r_R4.log 2>&1
