# Lean proof of c₂ ≤ 3.59123

This directory proves, in Lean 4 with Mathlib, that the weak type (1,1) constant c₂ of the centred
Hardy–Littlewood maximal operator over axis-parallel squares in the plane satisfies c₂ ≤ 3.59123, which is Theorem 1.2
of the accompanying paper.

The main theorems are in `Hl47a/Main.lean`, and their definitions are in `Hl47a/Statement.lean`, which imports only
Mathlib. `Hl47a.NonstrictClaim` is the bound in the form with the level sets {Mf ≥ λ} and real λ > 0.

```lean
theorem Hl47a.weakTypeConstant_two_le : Hl47a.weakTypeConstant 2 ≤ ENNReal.ofReal (359123 / 100000)
theorem Hl47a.weakTypeConstant_two_lt : Hl47a.weakTypeConstant 2 < ENNReal.ofReal (359123 / 100000)
theorem Hl47a.isWeakTypeBound_two : Hl47a.IsWeakTypeBound 2 (ENNReal.ofReal (359123 / 100000))
theorem Hl47a.nonstrict_two : Hl47a.NonstrictClaim
```

For each of them, `#print axioms` reports only the three standard axioms:

```
'Hl47a.weakTypeConstant_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hl47a.weakTypeConstant_two_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hl47a.isWeakTypeBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hl47a.nonstrict_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The numerical data are checked by `decide +kernel`, so the Lean kernel itself evaluates them. On each small rectangle,
the lower bound for AK is the smallest of the lower bounds for the 16 Bernstein coefficients of a bicubic polynomial that
approximates AK there, minus a proved bound for the approximation error. The tensor sums behind these bounds are
computed in exact integer arithmetic, and `GeneratorLeafData.intLowerBound_eq` and `BandLeafData.intLowerBound_eq` prove
that the integer forms equal the rational ones.

## Build

```
lake exe cache get
lake build
```

The toolchain is `leanprover/lean4:v4.35.0-rc3`, and Mathlib is pinned at commit c55e6e786f. The tree has
2299 modules. Most of the build time goes to the Lean kernel's checks of the data modules, which give lower bounds for
K on cells and for AK on small rectangles: about 64 CPU-hours in total, or about an hour on 88 hardware threads.

## Credits

This directory is a modified version of Yongxi Lin's Lean development partial-balayage-lean
(https://github.com/CoolRmal/partial-balayage-lean), commit 0055cdf5b947f4e23b0b736a297ab38b48b1a270
(2026-10-06T10:04:00Z), released under the Apache License 2.0. `LICENSE-Lin` is the licence file of that commit,
unchanged; `LICENSE`, which covers the whole directory, is the same Apache License 2.0 text.

We keep the structure of Lin's argument for squares and replace his constants by those of the kernel K and the
certificate of the paper. Unlike Lin's kernel, K does not vanish outside the diamond r < R (here r = |u| + |v|, and
R = 33/20 for K and 7/4 for Lin's kernel). We therefore added a check of claim (C4) of the paper, AK ≥ 0, outside that
diamond. In Lin's proof of claims (C1) and (C2) (K ≥ 0, and K ≥ 1 on the unit diamond), the check of K ≥ 0
stops at the diamond r < R, outside which his kernel vanishes. We also replaced that proof by cell checks for K on the
square max(|u|, |v|) < 9/4 that are built on his leaf and triangle modules. Some theorem names keep the exponents of Lin's
kernel although their statements use those of K; for example, `rpow_two_nine_fifths_le` states 2^(73/40) ≤ 73/20.

`FILES.txt` assigns every file except `README.md`, `FILES.txt` and `SHA256SUMS` to one of three groups:

- unchanged (232 files): byte-identical to the file at the same path in Lin's commit (for `LICENSE-Lin`, to his
  `LICENSE`).
- modified (1264 files): Lin's file, or a data file generated in the format of one of his files. Each Lean file keeps
  Lin's copyright header and adds a line "Modified by Tejasvi Singh Tomar, 2026:" that says what changed.
- ours (808 files): new files, with our copyright header.

Only the modules needed for the theorems above are included. The rest of Lin's repository is left out, among it his
other results, the data and checks of his kernel, his comparator harness, his scripts and his documentation. The
programs that generated the data files are not included either; the Lean kernel checks the data. Some comments in the
modified files still describe Lin's kernel.
