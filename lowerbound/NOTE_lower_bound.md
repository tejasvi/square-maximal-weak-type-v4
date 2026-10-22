# Lower bounds for c_2 from periodic point-mass configurations

c_2 is the least C with lam |{M f >= lam}| <= C ||f||_1 for all f in L^1(R^2) and lam > 0, where
M f(x) = sup_{s>0} (4 s^2)^-1 int_{Q(x,s)} |f| and Q(x,s) = {y : |y - x|_inf <= s} (closed squares).
(Strict or non-strict level sets give the same constant.)

## Lemma 1 (rectangles in the superlevel set)
Let mu = sum_i m_i delta_{p_i} (m_i > 0, finitely many atoms in every bounded set), lam > 0, S a finite set of atoms
and 0 < rho <= sqrt(mu(S)/(4 lam)). Then R_S(rho) := intersection over p in S of Q(p, rho) satisfies
M mu(x) >= lam for every x in R_S(rho), where M mu(x) = sup_s mu(Q(x,s))/(4 s^2).
Proof. x in Q(p, rho) for all p in S means |p - x|_inf <= rho, i.e. S is contained in Q(x, rho). Hence
mu(Q(x, rho)) >= mu(S) >= 4 lam rho^2.  []
(Conversely every point of {M mu >= lam} lies in some R_S(sqrt(mu(S)/(4 lam))) with S the atoms of a square; this is
used only by the search, not by the certificate.)

## Lemma 2 (periodic configurations)
Let mu be periodic with respect to the lattice P_x Z x P_y Z, with finitely many atoms in the cell C = [0,P_x) x [0,P_y).
Let U be the union of all lattice translates of finitely many rectangles R_S(rho_S) as in Lemma 1, with S finite and
rho_S < sqrt(mu(S)/(4 lam)) strictly, and let A = |U cap C|. Then c_2 >= lam A / mu(C).
Proof.
1. Truncation. Let d bound the diameters of the finitely many sets S used and of their rectangles. For N >= 1 let mu_N be
   mu restricted to the N x N block of cells B_N = [0, N P_x) x [0, N P_y). If a cell of B_N has distance >= d from the
   complement of B_N, every translate of a rectangle meeting that cell, together with its set S, lies in B_N, so by
   Lemma 1 (applied to mu_N) the part of U in that cell lies in {M mu_N >= lam}. There are at least (N - 2c)^2 such cells,
   c = ceil(d / min(P_x, P_y)), so |{M mu_N >= lam}| >= (N - 2c)^2 A, while ||mu_N|| = N^2 mu(C).
2. Smoothing. Let f_eps = sum over atoms p of mu_N of m_p (2 eps)^-2 1_{Q(p, eps)} (so ||f_eps||_1 = ||mu_N||). If x lies in
   a translate of R_S(rho_S), then Q(x, rho_S + eps) contains every Q(p, eps), p in S, so
   M f_eps(x) >= mu(S) / (4 (rho_S + eps)^2) >= lam as soon as eps <= sqrt(mu(S)/(4 lam)) - rho_S (positive, finitely many S).
   Hence lam |{M f_eps >= lam}| / ||f_eps||_1 >= lam (N - 2c)^2 A / (N^2 mu(C)).
3. Letting N -> infinity gives c_2 >= lam A / mu(C).  []

## Certificate format and check
A certificate lists lam, P_x, P_y and the atoms of one cell (all rational). The checker (check_exact.py)
- enumerates the boxes [x_a, x_b] x [y_a, y_b] with bounds at atom coordinates of a finite window and sides <= reach;
- takes S = the atoms in the box and rho_S = (largest k/D with (k/D)^2 <= mu(S)/(4 lam)) - 1/D, which is strictly below
  sqrt(mu(S)/(4 lam));
- clips the rectangles R_S to the cell and computes the area of their union exactly (rationals);
- prints the exact rational lam A / mu(C), a lower bound for c_2 by Lemma 2.

## The certified configuration (FINAL)
Period cell [0, P_x) x [0, P_y) with P_x = 328734960629/10^11 (about 3.28735) and P_y = 1371827000331/(5 * 10^11)
(about 2.74365); lam = 1; 50 atoms per cell (exact rationals in the certificate file):
- mass 1 at (0, 0) and mass 501053640219/(1.25 * 10^11) (about 4.00843) at (P_x/2, 0): Lin's alternating-column frame;
- line A: 6 equally spaced atoms of mass about 0.0061156 on a horizontal segment beside the heavy column
  (x/h in [0.6997, 0.9243], h = P_x/2, at height y = 0.3955 P_y), copied by the frame's symmetries
  x -> -x, x -> 2h - x, y -> -y (24 atoms);
- line B: 6 equally spaced atoms of mass about 0.0049720 on x/h in [0, 0.3107] at height y = 0.2002 P_y, with the same
  symmetry copies (24 atoms; the segment and its mirror image form one line through the light column).
The checker gives lam A / mu(C) = 482167717377842991882283179477574801392641890014291050323 /
283174368139841919615520431313000857449005056000000000000 >= 1.7027237335; hence c_2 >= 1.7027237335.
For comparison: Lin's lattice (frame alone, his parameters) gives 1.6855099933 with the same checker.
