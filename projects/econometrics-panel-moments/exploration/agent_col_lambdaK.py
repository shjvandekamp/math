#!/usr/bin/env python3
"""agent_col task 3: a candidate head-map invariant suggested by the collision u_N = u_0.

W^K := {w in W_m : w K_0 in W_m} (dim W_m - 9m by agent_col_stepY).  Question: is Lambda_m(w K_0) determined by
Lambda_m(w) on W^K (a 'transfer identity' for the head map under the oldest kernel)?  Test: rank of
[Lambda_m(w) ; Lambda_m(w K_0)] over a basis of W^K versus rank of Lambda_m(w) alone.  Also the same with
K_0 replaced by the newest kernel K_{m-1} and by a middle kernel.  Lambda_m = head sums of the DHW coordinates
minus E-spread (agent_ag_lib conventions), exact mod p = 2^61-1 at one random product-form point.
What this does not show: anything beyond the printed m.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, make_A, s_const, eval_terms_matrix, rand_points, rank, family_terms,  # noqa
                           right_kernel_mat)
from agent_col_stepY import canon_W  # noqa: E402


def times_k(vec, k):
    out = []
    for coef, a0, heads, kind, word in vec:
        assert kind == 'IW'
        out.append((coef, a0, heads, 'W', [k]))
        out.append((-coef, a0, heads, 'W', list(word) + [k]))
    return out


def main(ms):
    for m in ms:
        rng = random.Random(4400 + m)
        g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
        A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
        labs, fam = family_terms(m)                         # DHW basis of W_m (order 0..m-1)
        Wc = canon_W(m)
        npts = (3 * len(Wc)) // 2 + 20
        pts = rand_points(A, npts, rng, 1)
        Efam = eval_terms_matrix(A, fam, pts, 1, ncomp=2)
        # square invertible subsystem for coordinates in the DHW basis
        Mf = flint.nmod_mat(Efam, P)
        Rr, rk = Mf.rref()
        assert rk == len(fam)
        piv, r = [], 0
        for c in range(Mf.ncols()):
            if r < rk and int(Rr[r, c]) != 0:
                piv.append(c)
                r += 1
        Sq = flint.nmod_mat([[Efam[i][c] for i in range(len(fam))] for c in piv], P)
        Sqinv = Sq.inv()
        heads = [(t, a, b) for t in range(m) for a in range(Q) for b in range(Q)]
        hpos = {h: i for i, h in enumerate(heads)}

        def Lam(rows):
            """rows: evaluations of vectors in W_m -> Lambda matrix (#vectors x 9m)."""
            out = []
            for y in rows:
                coef = Sqinv * flint.nmod_mat([[y[c]] for c in piv], P)
                lam = [0] * len(heads)
                for i, lab in enumerate(labs):
                    x = int(coef[i, 0])
                    if not x:
                        continue
                    if lab[0] == 'F':
                        _, t, s, a, b = lab
                        lam[hpos[(t, a, b)]] = (lam[hpos[(t, a, b)]] + x) % P
                    else:
                        _, s, a = lab
                        for b in range(Q):
                            lam[hpos[(s, a, b)]] = (lam[hpos[(s, a, b)]] - x) % P
                out.append(lam)
            return out

        Ew = eval_terms_matrix(A, Wc, pts, 1, ncomp=2)
        for k, name in ((0, 'oldest K_0'), (m // 2, 'middle'), (m - 1, 'newest')):
            EwK = eval_terms_matrix(A, [times_k(v, k) for v in Wc], pts, 1, ncomp=2)
            # W^K: combinations c of canonical basis with c . (W K_k) in W_m  <=>  rank condition; compute
            # kernel of the map c -> (c.WK) modulo W_m: stack [EwK ; Ew] and find c with c.EwK = d.Ew
            stack = flint.nmod_mat(EwK + Ew, P).transpose()
            ker = right_kernel_mat(stack)                       # (c, d) with c.EwK + d.Ew = 0
            nW = len(Wc)
            Cs = [v[:nW] for v in ker]
            if not Cs:
                print(f'm={m} {name}: W^K = 0')
                continue
            wrows = [[sum(c[i] * Ew[i][j] for i in range(nW) if c[i]) % P for j in range(len(Ew[0]))] for c in Cs]
            wKrows = [[(-sum(v[nW + i] * Ew[i][j] for i in range(nW) if v[nW + i])) % P for j in range(len(Ew[0]))]
                      for v in ker]
            L1 = Lam(wrows)
            L2 = Lam(wKrows)
            r1, r2 = rank(L1), rank(L2)
            r12 = rank([a + b for a, b in zip(L1, L2)])
            print(f'm={m} {name}: dim W^K = {len(Cs)} (dim W_m - 9m = {nW - 9 * m}); rank Lambda(w) = {r1}, '
                  f'rank Lambda(wK) = {r2}, joint rank = {r12}  '
                  f'(Lambda(wK) determined by Lambda(w): {r12 == r1})', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [3, 4])
