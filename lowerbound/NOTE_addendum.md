# Addendum to frozen/NOTE_lower_bound_ad4ef0ed.md (FORMAT and one proof line)

Written 2026-10-21 05:44 PDT at audit-uncert's request (FORMAT section, rho_S <= d line).

Applies to the frozen certificate frozen/c2lower_1p70272_e2ca1616.json (frozen/SHA256SUMS d9d21127...). frozen/ itself
is unchanged; this file is separate on purpose. Checkers: frozen/check_exact2_abb311c7.py (integers) and
frozen/check_exact_e8df1f7c.py (Fractions).

## 1. Certificate format
JSON object; every number is a rational written as a string "p" or "p/q" (Python Fraction syntax):
- "lam": "1". check_exact2.py raises unless lam = 1; check_exact.py handles any lam > 0.
- "Px", "Py": here "328734960629/100000000000" and "1371827000331/500000000000". The cell is C = [0, Px) x [0, Py) and
  the measure is periodic under Px Z x Py Z.
- "pts": list of [x, y, m] with 0 <= x < Px, 0 <= y < Py, m > 0 (check_exact2.py checks this): the 50 atoms of one cell.
- "reach": here "1396/125" (= 11.168), the bound on box sides.
- "source", "float_ratio": informational (search file, float value); neither checker reads them.
- D = 2^40 is NOT in the JSON. Both checkers fix it by default (check_exact2.py --Dr, check_exact.py --D) and
  check_exact2.py records it as "Dr" in the check2 report. The exact value depends on D, so D = 2^40 is part of the
  certificate.

## 2. Box family
- Boxes B = [x_a, x_b] x [y_a, y_b]: x_a <= x_b are x-coordinates of atoms of the periodic measure, y_a <= y_b are
  y-coordinates of atoms (not necessarily the same atoms), and x_b - x_a <= reach AND y_b - y_a <= reach (each side
  separately). Degenerate boxes (x_a = x_b and/or y_a = y_b, e.g. a single atom) are included.
- S = the atoms in the closed box B, mu(S) = the sum of their masses; boxes with mu(S) = 0 are skipped.
- Finite window, check_exact2.py: Dx = lcm of the denominators of Px, Py, reach and all atom coordinates;
  nb = (floor(reach/Px) + 2)(floor(reach/Py) + 2), so a box meets at most nb cells and mu(S) <= nb mu(C);
  rho_max = (isqrt(floor(D^2 nb mu(C)/4)) + 1)/D > sqrt(nb mu(C)/4), so rho_S <= rho_max for every box;
  r = (ceil(rho_max Dx) + 1)/Dx. It keeps the translates with -(reach + r) <= x <= Px + reach + r (same in y) and the
  boxes with x_a >= -r, x_b <= Px + r, y_a >= -r, y_b <= Py + r. For every kept box all atoms in it are in the window, so
  S is complete. A skipped box has x_a + rho_S < 0, x_b - rho_S > Px, or the same in y, so its rectangle misses C.
- Finite window, check_exact.py: the translates (i, j) with |i| <= ceil((reach + r1)/Px) + 1 and
  |j| <= ceil((reach + r1)/Py) + 1, r1 = sqrt((reach/Px + 2)(reach/Py + 2) mu(C)/4) in floating point (the float only
  sizes the window), and all boxes over window atoms (no pruning). Boxes at the window edge may miss atoms beyond the
  edge; that only lowers mu(S), and their rectangles lie far from C. It gives the same 5135 rectangles and the
  same exact value as check_exact2.py.
- Soundness does not depend on the window: Lemma 1 holds for any set of atoms inside the box, so a smaller window can
  only lower the value.

## 3. Radii and rectangles
- k = isqrt(floor(D^2 mu(S)/(4 lam))), rho_S = (k - 1)/D; boxes with k - 1 <= 0 are skipped. k/D is the largest
  multiple of 1/D with (k/D)^2 <= mu(S)/(4 lam), so rho_S < sqrt(mu(S)/(4 lam)) strictly (check_exact.py computes the
  same number as isqrt_frac_lower(mu(S)/(4 lam), D) - 1/D).
- The rectangle of B is [x_b - rho_S, x_a + rho_S] x [y_b - rho_S, y_a + rho_S], built from the BOX bounds. Since
  x_a <= min_S x and x_b >= max_S x (same in y), it lies inside R_S(rho_S) = intersection over p in S of Q(p, rho_S),
  and equals it when the box is tight (bounds attained by atoms of S). The tight box of S has the same S and is also
  enumerated, so the union over all boxes equals the union of the R_S(rho_S) over the sets S that occur.
- Clipping: each rectangle is intersected with [0, Px] x [0, Py] and kept only if both sides are positive. There is no
  separate translation step: the window contains every translate of every box whose rectangle meets C.
- A = area of the union of the clipped rectangles, exact (check_exact2.py: integers over (lcm(Dx, D))^2, sweep line with
  a segment tree of coverage counts; check_exact.py: Fractions). The certified value is lam A / mu(C) as an exact
  rational; the stated value is floor(10^10 lam A / mu(C))/10^10 = 1.7027237335 (check2 report field
  ratio_floor_1e10 = "17027237335").

## 4. Lemma 2, step 1: the margin covers rho_S
Let d bound diam S and diam R_S(rho_S) (sup norm) for the finitely many (S, rho_S) used. The x-width of
R_S(rho_S) = [max_S x - rho_S, min_S x + rho_S] is 2 rho_S - (max_S x - min_S x), so
2 rho_S <= diam R_S(rho_S) + diam S <= 2d, i.e. rho_S <= d. If a translate of R_S(rho_S) meets a cell at a point z,
every atom of S is within rho_S <= d of z (sup norm), as in the proof of Lemma 1. So for a cell at distance >= d from the
complement of B_N, the rectangle and the atoms of S lie in B_N, which step 1 needs.
