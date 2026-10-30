#!/usr/bin/env python3
"""agent_col task 2: the 12 first-order jets at the collision u_N = u_0 and what separates them from S_0.

Jets (agent_col_lib.jet_terms, D = dK_N/d delta at delta = 0, D(a,i) = K_0(a,i)(nu_i - L'_a/L_0a)):
    JE_a  = d/d delta (E_{N,a} - E_{0,a})        = -X_a e_a D
    JF_ab = d/d delta (F_{N,0,a,b} - F_{0,N,a,b}) = X_a D(a,b) e_b (I - K_0 Pi) + X_a K_0(a,b) e_b D Pi.
Checks (exact mod p = 2^61-1, one random point per n):
 (1) the explicit jets equal the delta-coefficient of the pair differences (series evaluation);
 (2) rank of the jets modulo S_0 (= 12 is Coll(n) given dim S_0 = |fam| - 12);
 (3) pole orders: the eps^-3 coefficient along L_{0c} vanishes (jets have at most double poles);
 (4) ranks of the double-pole data dp, its transverse part tau, on S_0, S_0 + jets: does the double-pole
     data along the doubled lines alone separate the jets from S_0?  (local reason)
 (5) the same with the jets' dependence on nu: the jets for nu and nu' = nu + (1,1,1) agree mod S_0.
What this does not show: proofs; anything beyond the printed n.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, family_series, kernels_series, rand_points, rank,  # noqa
                           family_labels, term_vec, T_E, T_F, jet_terms, kernels_with_D, WordCache,
                           point_on_line, polar_kernels_with_D, polar_vec)


def eval_with_D(A, vecs, pts, k, nu):
    rows = [[] for _ in vecs]
    for X in pts:
        kers = kernels_with_D(A, X, k, nu)
        wc = WordCache(kers, 1)
        for r, terms in enumerate(vecs):
            v = term_vec(kers, X, terms, 1, wc, 2)
            rows[r].extend([v[0][0], v[1][0]])
    return rows


def polar_rows(A, vecs, lines_pts, N, k, nu, mode, order=3):
    rows = [[] for _ in vecs]
    for c, pts in lines_pts:
        for X0, Yd in pts:
            pk, Xs = polar_kernels_with_D(A, X0, Yd, c, {k, N}, order + 1, k, nu)
            v0c = [A[k][c][i][0] * X0[i] % P for i in range(Q)]
            for r, terms in enumerate(vecs):
                out = polar_vec(pk, Xs, terms, order + 1, order=order)
                if mode == 'triple':
                    rows[r].extend([out[0][0], out[1][0]])
                    continue
                d = [out[i][order - 2] for i in range(Q)]     # coefficient of eps^-2
                if mode == 'dp':
                    rows[r].extend([d[0], d[1]])
                elif mode == 'tau':
                    rows[r].append((d[0] * v0c[1] - d[1] * v0c[0]) % P)
    return rows


def main(ns):
    for n in ns:
        m = n - 1
        N = n - 1
        rng = random.Random(4100 + n)
        A2, info = collision_config(n, 0, rng, 2)
        nu = info['nu']
        A0 = [[[[x[0]] for x in row] for row in blk] for blk in A2]     # delta = 0 configuration
        # (1) verification against the series
        X = rand_points(A0, 1, rng, 1)[0]
        ser = family_series(kernels_series(A2, X, 2), X, n, 2)
        labs = family_labels(n)
        pos = {l: i for i, l in enumerate(labs)}
        jl, jt = jet_terms(n, 0)
        kers = kernels_with_D(A0, X, 0, nu)
        ok = True
        for lab, terms in zip(jl, jt):
            v = term_vec(kers, X, terms, 1, None, 2)
            if lab[0] == 'JE':
                i1, i0 = pos[('E', N, lab[1])], pos[('E', 0, lab[1])]
            else:
                i1, i0 = pos[('F', N, 0, lab[1], lab[2])], pos[('F', 0, N, lab[1], lab[2])]
            for comp in range(2):
                want = (ser[i1][comp][1] - ser[i0][comp][1]) % P
                ok &= (v[comp][0] == want)
        print(f'n={n}: (1) explicit jets equal the delta-coefficients of the pair differences: {ok}', flush=True)
        # S_0 generators
        Es = [T_E(s, a) for s in range(m) for a in range(Q)]
        S0 = Es + [T_F(t, s, a, b, n) for t in range(m) for s in range(m) if s != t for a in range(Q) for b in range(Q)]
        S0 += [T_F(t, N, a, b, n) for t in range(1, m) for a in range(Q) for b in range(Q)]
        S0 += [T_F(N, s, a, b, n) for s in range(1, m) for a in range(Q) for b in range(Q)]
        S0 += [T_F(0, N, a, b, n) for a in range(Q) for b in range(Q)]
        pts = rand_points(A0, (len(S0) + 12) // 2 + 10, rng, 1)
        dS0 = rank(eval_with_D(A0, S0, pts, 0, nu))
        dSJ = rank(eval_with_D(A0, S0 + jt, pts, 0, nu))
        print(f'   (2) dim S_0 = {dS0} (|fam|-12 = {3 * n * (3 * n - 2) - 12}); rank jets mod S_0 = {dSJ - dS0}', flush=True)
        # (5) nu-shift invariance
        nu2 = [(x + 1) % P for x in nu]
        rowsJ1 = eval_with_D(A0, jt, pts, 0, nu)
        rowsJ2 = eval_with_D(A0, jt, pts, 0, nu2)
        diff = [[(a - b) % P for a, b in zip(r1, r2)] for r1, r2 in zip(rowsJ1, rowsJ2)]
        S0rows = eval_with_D(A0, S0, pts, 0, nu)
        print(f'   (5) jets(nu) - jets(nu+(1,1,1)) mod S_0 has rank {rank(S0rows + diff) - dS0} (expect 0)', flush=True)
        # (3),(4) polar data
        ppl = 4 * m + 8
        lines_pts = []
        for c in range(Q):
            pl = []
            for _ in range(ppl):
                X0 = point_on_line(A0, 0, c, rng)
                Yd = [rng.randrange(1, P) for _ in range(Q)]
                pl.append((X0, Yd))
            lines_pts.append((c, pl))
        trip = polar_rows(A0, jt, lines_pts, N, 0, nu, 'triple')
        print(f'   (3) jets: eps^-3 coefficients all zero: {all(x == 0 for r in trip for x in r)}', flush=True)
        r_dpS = rank(polar_rows(A0, S0, lines_pts, N, 0, nu, 'dp'))
        r_dpSJ = rank(polar_rows(A0, S0 + jt, lines_pts, N, 0, nu, 'dp'))
        r_tS = rank(polar_rows(A0, S0, lines_pts, N, 0, nu, 'tau'))
        r_tSJ = rank(polar_rows(A0, S0 + jt, lines_pts, N, 0, nu, 'tau'))
        r_dpJE = rank(polar_rows(A0, S0 + jt[:3], lines_pts, N, 0, nu, 'dp'))
        r_dpJF = rank(polar_rows(A0, S0 + jt[3:], lines_pts, N, 0, nu, 'dp'))
        print(f'   (4) rank dp: S_0 {r_dpS}, S_0+jets {r_dpSJ} (+{r_dpSJ - r_dpS}), S_0+JE {r_dpJE - r_dpS:+d}, '
              f'S_0+JF {r_dpJF - r_dpS:+d}; rank tau: S_0 {r_tS}, S_0+jets {r_tSJ} (+{r_tSJ - r_tS})', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [5, 6])
