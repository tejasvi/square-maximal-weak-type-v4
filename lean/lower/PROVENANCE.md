# Provenance

## Upstream

- Repository: https://github.com/CoolRmal/centered-maximal-constant (Yongxi Lin), Apache License 2.0.
- Commit: `72c022ba09032b522c878cca2f9b6c68217d77ea`, dated 2026-10-01 01:14:24 UTC, taken from the source
  archive of the `main` branch. Archive (`.tar.gz`) sha256:
  `6db8c4981af04ac00e207e2e75b14f04c0ae92742c541ea727b74a699cc2c85e`. Its tar header records the commit id.
- `LICENSE` has git blob `8dada3edaf50dbc082c9a125058f25def75e625a`.

Unchanged files: `cmp` shows them byte-identical to the files of commit 72c022b with the same paths.

| file | sha256 |
|---|---|
| `LICENSE` | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |
| `lean-toolchain` | `bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47` |
| `lake-manifest.json` | `240d6c63ac245b8edf1964a193f8a9f33292b191ddd87434b115ebc7f785b556` |
| `CenteredMaximal/Statement.lean` | `a3dff3cb12d57d58e9999a73abc11afc58f84f4748cdb14d067cb5eff1f42bb5` |
| `CenteredMaximal/Basic.lean` | `662d63a24f1faa1faf593a621062d8d33c44bd460ffe732887d4d7bacd3824a0` |

Modified files and the upstream files they derive from:

| file | derived from (sha256 of the upstream file) |
|---|---|
| `lakefile.toml` | `lakefile.toml` (`a8d03bdc363e0c7e9fe042080888d0e669b36ba50d84688836205c42bdfb5498`) |
| `CenteredMaximal/Periodic/Witness.lean` | `CenteredMaximal/Lattice/Witness.lean` (`54c65e6119dfe111e7e03b06bc7340231b1e7893a68cbe0158a38b53ab12c46f`) |
| `CenteredMaximal/Periodic/Smear.lean` | `CenteredMaximal/Lattice/Smear.lean` (`eb47cb29738130cd40f1c3a4e16f31e2607a492625d4587e145dd6df9f09a2f8`) |
| `CenteredMaximal/Periodic/LowerBound.lean` | `CenteredMaximal/Lattice/LowerBound.lean` (`721a7e4d7c97d28ba6758bf1e7fb0916bc72edafdfca48ec4d372b73f3ea24db`) |

## Configuration

- `data/c2lower_1p70272_e2ca1616.json`, sha256 `e2ca1616be95afa6680e3ccf157cc16fdd39026ad0f5fa79ebd32e5214779888`:
  the frozen configuration. Its fields: `lam` = 1; `Px`, `Py` (the periods); `pts` (the 50 atoms of the period
  cell, as rational strings `x`, `y`, mass); `reach` (the largest box side the rectangle search uses). Its exact
  checker uses radii on the grid 2⁻⁴⁰ · ℤ, so `tools/gen_cert.py` uses `--Dr 2^40` (the default).
  `source` and `float_ratio` are informational and not read.
- Covered area per unit mass: 482167717377842991882283179477574801392641890014291050323 /
  283174368139841919615520431313000857449005056000000000000 = 1.702723733596…, floor at 10 digits 1.7027237335.
  The certificate generated from this file has exactly this ratio, which the theorem
  `ofReal_le_weakTypeConstant_two_exact` states.

## Generated data

- `CenteredMaximal/Periodic/Data.lean` and `CenteredMaximal/Periodic/Data/{Atoms,Rects0,Rects1,Pieces0,Pieces1,Pieces2}.lean`
  are the output of `python3 -I tools/gen_cert.py data/c2lower_1p70272_e2ca1616.json OUTDIR` (byte-identical;
  sha256 of every file in `SHA256SUMS`), with `tools/gen_cert.py` sha256
  `9ac21838f2f7dfa99200c6775e3bff5fae2fb53cd90791f7e620f8223a3e101d`.
- Certificate size: 50 atoms, 405 witness rectangles, 11,396 atom references, 1,556 pieces in 226 slabs;
  Q = lcm(coordinate denominators, 2⁴⁰) (98 bits), Dm = mass denominator (118 bits); least witness side
  2ρ/Q = 0.0705 ≥ ℓ = 1/16; witness atoms come from the cell and its eight neighbours.

## Toolchain and build

- Lean `leanprover/lean4:v4.35.0-rc3`; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` (with the dependency
  revisions pinned in `lake-manifest.json`).
- `lake build` (15 modules, Mathlib build present): 25 s wall clock on 22 cores. In `Main.lean` each
  `decide +kernel` check takes about 5.5 s of kernel type checking.
- `lake env lean Axioms.lean` prints, for both `CenteredMaximal.ofReal_le_weakTypeConstant_two` and
  `CenteredMaximal.ofReal_le_weakTypeConstant_two_exact`: `[propext, Classical.choice, Quot.sound]`.
- Negative controls (not shipped): the same certificate with the numerator increased by one,
  `checkCert cert 17027237336 10000000000` and the exact rational with numerator + 1, are rejected by
  `decide +kernel` ("proved that the proposition … is false").
