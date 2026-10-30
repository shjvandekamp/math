#!/usr/bin/env python3
"""agent_col task 2/3: double-pole data along the doubled lines L_{0c} at the collision u_N = u_0, delta = 0.

For a vector f at delta = 0 (block N = block 0), its double-pole coefficient along L_{0c} is
dp_c(f) = (L_{0c}^2 f)|_{L_{0c}}, a zero-sum vector function on L_{0c}; write dp_c = alpha_c v_{0c} + tau_c w
(longitudinal alpha, transverse tau; v_{0c} = (A_0(c,i) X_i)_i).  These are Lambda-free: computed directly
from each word.  Evaluated at many random points of each L_{0c} (Laurent expansion, agent_col_lib.polar_vec).

Prints, for S_0 (the distinct delta = 0 family members), Y = W_m + W_m K_0 + H_0, A (appended old columns)
and the new columns: ranks of dp (all three lines), of tau, and dim S_0 - rank dp(S_0) versus dim W_m.
If S_0 cap {no double poles} = W_m and W_m is in S_0, then dim S_0 = dim W_m + rank dp(S_0).
Exact mod p = 2^61-1, one random product-form point per n.
What this does not show: proofs; that the number of sample points per line is always sufficient
(it is increased until the ranks stabilise, printed).
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, eval_terms_matrix, rand_points, rank, T_E, T_F,  # noqa: E402
                           point_on_line, polar_kernels, polar_vec)
from agent_col_stepY import canon_W, times_K0  # noqa: E402


def polar_matrix(A, vecs, lines_pts, N, mode='dp'):
    """rows = vectors; columns = (line c, point, comp) for dp (2 comps) or tau (1 comp) or alpha."""
    rows = [[] for _ in vecs]
    for c, pts in lines_pts:
        for X0, Yd in pts:
            pk, Xs = polar_kernels(A, X0, Yd, c, {0, N}, 3)
            v0c = [A[0][c][i][0] * X0[i] % P for i in range(Q)]
            for r, terms in enumerate(vecs):
                out = polar_vec(pk, Xs, terms, 3)
                d = [out[i][0] for i in range(Q)]
                if mode == 'dp':
                    rows[r].extend([d[0], d[1]])
                elif mode == 'tau':
                    rows[r].append((d[0] * v0c[1] - d[1] * v0c[0]) % P)
                elif mode == 'alpha':    # longitudinal coefficient (valid when tau = 0): d0 / v0c0
                    rows[r].append(d[0] * pow(v0c[0], P - 2, P) % P)
    return rows


def main(ns, ppl_list):
    for n in ns:
        m = n - 1
        N = n - 1
        rng = random.Random(900 + n)
        A0, _ = collision_config(n, 0, rng, 1)
        Es = [T_E(s, a) for s in range(m) for a in range(Q)]
        Aold = Es + [T_F(t, s, a, b, n) for t in range(m) for s in range(m) if s != t
                     for a in range(Q) for b in range(Q)]
        new = [T_F(t, N, a, b, n) for t in range(1, m) for a in range(Q) for b in range(Q)]
        new += [T_F(N, s, a, b, n) for s in range(1, m) for a in range(Q) for b in range(Q)]
        new += [T_F(0, N, a, b, n) for a in range(Q) for b in range(Q)]
        S0 = Aold + new
        Wm = canon_W(m)
        WmK = [times_K0(v) for v in Wm]
        H0 = [[(1, a, [(0, b)], 'IW', [0])] for a in range(Q) for b in range(Q)]
        Y = Wm + WmK + H0
        pts = rand_points(A0, (len(S0) + len(Wm)) // 2 + 12, rng, 1)
        dS0 = rank(eval_terms_matrix(A0, S0, pts, 1, ncomp=2))
        dWS = rank(eval_terms_matrix(A0, S0 + Wm, pts, 1, ncomp=2))
        dW = rank(eval_terms_matrix(A0, Wm, pts, 1, ncomp=2))
        for ppl in (ppl_list or [4 * m + 8, 8 * m + 16]):
            lines_pts = []
            for c in range(Q):
                pl = []
                for _ in range(ppl):
                    X0 = point_on_line(A0, 0, c, rng)
                    Yd = [rng.randrange(1, P) for _ in range(Q)]
                    pl.append((X0, Yd))
                lines_pts.append((c, pl))
            rdp = {name: rank(polar_matrix(A0, vs, lines_pts, N, 'dp'))
                   for name, vs in (('S0', S0), ('Y', Y), ('A', Aold), ('new', new), ('Wm', Wm))}
            rtau = {name: rank(polar_matrix(A0, vs, lines_pts, N, 'tau'))
                    for name, vs in (('S0', S0), ('Y', Y), ('A', Aold), ('new', new))}
            print(f'n={n} m={m} ({ppl} pts/line): rank dp: {rdp}; rank tau: {rtau}', flush=True)
        print(f'   dim S_0={dS0}, dim W_m={dW}, W_m in S_0: {dWS == dS0}; '
              f'dim S_0 - rank dp(S_0) = {dS0 - rdp["S0"]}; 18m-9 = {18 * m - 9}, 9m = {9 * m}, 9(m-1) = {9 * (m - 1)}',
              flush=True)


if __name__ == '__main__':
    ns = [int(x) for x in sys.argv[1:]] or [4, 5, 6]
    main(ns, None)
