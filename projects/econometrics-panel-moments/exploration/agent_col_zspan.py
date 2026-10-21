#!/usr/bin/env python3
"""agent_col task 3(a), last check: are the 9m explicit vectors of Z = span{B_{t,0,a,b} (t >= 1), h_0ab (I - K_0)}
(which together with A span Y and complete A inside S_0) SPARSE combinations of the distinct delta = 0 family
members?  A sparse explicit expression would give a Lambda-free proof of Z in S_0 (hence of Q_cyc(m)).
Prints, for each Z-vector, the number of nonzero coefficients in the basis of the 9m^2+12m-9 distinct delta = 0
members (exact mod p = 2^61-1, one random point), and how many of them are on new columns vs old (A) columns.
Also the same for the canonical vectors B_{t,s} with t, s >= 1 (which lie in C, the common part, trivially?).
What this does not show: that no other (non-family) explicit identity exists.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, eval_terms_matrix, rand_points, T_E, T_F)  # noqa: E402


def main(ns):
    for n in ns:
        m = n - 1
        N = n - 1
        rng = random.Random(3300 + n)
        A0, _ = collision_config(n, 0, rng, 1)
        labs = [('E', s, a) for s in range(m) for a in range(Q)]
        vecs = [T_E(s, a) for s in range(m) for a in range(Q)]
        for t in range(m):
            for s in range(m):
                if s != t:
                    for a in range(Q):
                        for b in range(Q):
                            labs.append(('F', t, s, a, b))
                            vecs.append(T_F(t, s, a, b, n))
        nold = len(vecs)
        for t in range(1, m):
            for a in range(Q):
                for b in range(Q):
                    labs.append(('F', t, 'N', a, b))
                    vecs.append(T_F(t, N, a, b, n))
        for s in range(1, m):
            for a in range(Q):
                for b in range(Q):
                    labs.append(('F', 'N', s, a, b))
                    vecs.append(T_F(N, s, a, b, n))
        for a in range(Q):
            for b in range(Q):
                labs.append(('F', 0, 'N', a, b))
                vecs.append(T_F(0, N, a, b, n))
        Zv = [[(1, a, [(t, b)], 'IW', [0])] for t in range(m) for a in range(Q) for b in range(Q)]
        Bts = [[(1, a, [(t, b)], 'IW', [s])] for t in range(1, m) for s in range(1, m) if s != t
               for a in range(Q) for b in range(Q)]
        pts = rand_points(A0, len(vecs) // 2 + 10, rng, 1)
        Ev = eval_terms_matrix(A0, vecs, pts, 1, ncomp=2)
        M = flint.nmod_mat(Ev, P)
        Rr, rk = M.rref()
        assert rk == len(vecs), f'family rank {rk} < {len(vecs)}'
        piv, r = [], 0
        for c in range(M.ncols()):
            if r < rk and int(Rr[r, c]) != 0:
                piv.append(c)
                r += 1
        Sq = flint.nmod_mat([[Ev[i][c] for i in range(len(vecs))] for c in piv], P)
        Sqinv = Sq.inv()

        def support(targets, name):
            Et = eval_terms_matrix(A0, targets, pts, 1, ncomp=2)
            stats = []
            for y in Et:
                coef = Sqinv * flint.nmod_mat([[y[c]] for c in piv], P)
                cf = [int(coef[i, 0]) for i in range(len(vecs))]
                for k in range(0, len(y), 5):
                    assert sum(cf[i] * Ev[i][k] for i in range(len(vecs))) % P == y[k], 'not in span'
                nz_old = sum(1 for i in range(nold) if cf[i])
                nz_new = sum(1 for i in range(nold, len(vecs)) if cf[i])
                stats.append((nz_old, nz_new))
            print(f'n={n} {name}: (#nonzero on old A-columns of {nold}, on new columns of {len(vecs) - nold}) '
                  f'min {min(stats)}, max {max(stats)}', flush=True)

        support(Zv[9:], 'Z part B_{t,0} (t>=1)')
        support(Zv[:9], 'Z part h_0ab(I-K_0)')
        support(Bts[:9], 'canonical B_{t,s} (t,s>=1), first 9')


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [5, 6])
