#!/usr/bin/env python3
"""agent_col task 3(a): the delta = 0 step map at the collision u_N = u_0 and its head-map content.

Setting (delta = 0, m = n-1 distinct blocks, block N = block 0).  A = span{E_s, Phi_0(F^{(m)})} (old columns),
Phi_0(w) = w K_0 + L(Lambda_m(w)),  L(lambda) = sum_{t>=1} lambda_tab B_{t,0,a,b} + sum lambda_0ab h_0ab (I - K_0).
Z := image of L (9m explicit vectors).  Checks:
 (1) Y = W_m + W_m K_0 equals A (+) Z (direct)?
 (2) B_tau := combinations of the 18m-9 new columns with zero transverse double-pole data (= those lying in Y);
     the step map T0 : B_tau -> Z = Y/A (coordinates of the combinations in Z modulo A); rank and block pattern
     by head t of Z (t = 0 is H_0).
 (3) Lambda content: write each Y-combination y as Phi_0(w) + e + z; compare the Z-coordinates z with
     -Lambda_m(w) (i.e. is z = y-explicit part minus L(Lambda(w))?) and report the density of Lambda_m(w).
Exact mod p = 2^61-1, one random point per n.
What this does not show: proofs; a canonical choice of B_tau basis (the pattern is basis dependent).
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, eval_terms_matrix, rand_points, rank, T_E, T_F,  # noqa: E402
                           right_kernel_mat, point_on_line, polar_kernels, polar_vec)
from agent_col_stepY import canon_W, times_K0  # noqa: E402


def tau_rows(A0, vecs, n, rng, ppl):
    N = n - 1
    rows = [[] for _ in vecs]
    for c in range(Q):
        for _ in range(ppl):
            X0 = point_on_line(A0, 0, c, rng)
            Yd = [rng.randrange(1, P) for _ in range(Q)]
            pk, Xs = polar_kernels(A0, X0, Yd, c, {0, N}, 3)
            v0c = [A0[0][c][i][0] * X0[i] % P for i in range(Q)]
            for r, terms in enumerate(vecs):
                out = polar_vec(pk, Xs, terms, 3)
                d = [out[i][0] for i in range(Q)]
                rows[r].append((d[0] * v0c[1] - d[1] * v0c[0]) % P)
    return rows


def main(ns):
    for n in ns:
        m = n - 1
        N = n - 1
        rng = random.Random(2300 + n)
        A0, _ = collision_config(n, 0, rng, 1)
        Es = [T_E(s, a) for s in range(m) for a in range(Q)]
        Fold = [T_F(t, s, a, b, n) for t in range(m) for s in range(m) if s != t for a in range(Q) for b in range(Q)]
        Fold_lab = [(t, s, a, b) for t in range(m) for s in range(m) if s != t for a in range(Q) for b in range(Q)]
        Aold = Es + Fold
        new = [T_F(t, N, a, b, n) for t in range(1, m) for a in range(Q) for b in range(Q)]
        new += [T_F(N, s, a, b, n) for s in range(1, m) for a in range(Q) for b in range(Q)]
        new += [T_F(0, N, a, b, n) for a in range(Q) for b in range(Q)]
        Zt = [(t, a, b) for t in range(m) for a in range(Q) for b in range(Q)]
        Z = [[(1, a, [(t, b)], 'IW', [0])] for (t, a, b) in Zt]     # B_{t,0} (t>=1) and h_0ab(I - K_0)
        Wm = canon_W(m)
        Y = Wm + [times_K0(v) for v in Wm]
        pts = rand_points(A0, (len(Y) + len(new)) // 2 + 12, rng, 1)

        def ev(vs):
            return eval_terms_matrix(A0, vs, pts, 1, ncomp=2)

        EA, EZ, EY, EN = ev(Aold), ev(Z), ev(Y), ev(new)
        dA, dZ, dY = rank(EA), rank(EZ), rank(EY)
        dAZ = rank(EA + EZ)
        dAZY = rank(EA + EZ + EY)
        print(f'n={n} m={m}: (1) dim A={dA}, dim Z={dZ} (9m={9 * m}), dim(A+Z)={dAZ}, dim Y={dY}, '
              f'A+Z = Y: {dAZ == dY == dAZY}', flush=True)
        # (2) B_tau
        ppl = 4 * m + 8
        TR = tau_rows(A0, new, n, rng, ppl)
        Btau = right_kernel_mat(flint.nmod_mat(TR, P).transpose())   # combos c with sum c_j tau(new_j) = 0
        print(f'   (2) dim B_tau = {len(Btau)} (9m = {9 * m})', flush=True)
        # coordinates of each B_tau combination in the basis A u Z (solve)
        basis = EA + EZ                       # rows = vectors (each a list over evaluation columns)
        BT = flint.nmod_mat(basis, P)         # (#basis) x (#cols); we need columns as equations
        # choose independent evaluation columns: pivot columns of rref(BT)
        Rr, rk = BT.rref()
        piv, r = [], 0
        for cidx in range(BT.ncols()):
            if r < rk and int(Rr[r, cidx]) != 0:
                piv.append(cidx)
                r += 1
        assert rk == len(basis), 'A u Z not independent'
        Sq = flint.nmod_mat([[basis[i][cidx] for i in range(len(basis))] for cidx in piv], P)  # square
        Sqinv = Sq.inv()
        T0, Wcoef = [], []
        for cvec in Btau:
            y = [sum(cvec[j] * EN[j][k] for j in range(len(new))) % P for k in range(len(EN[0]))]
            ysq = flint.nmod_mat([[y[cidx]] for cidx in piv], P)
            sol = Sqinv * ysq
            coeffs = [int(sol[i, 0]) for i in range(sol.nrows())]
            # verify on all columns
            for k in range(0, len(y), 7):
                assert sum(coeffs[i] * basis[i][k] for i in range(len(basis))) % P == y[k], 'not in A + Z'
            T0.append(coeffs[len(EA):])
            Wcoef.append(coeffs[:len(EA)])
        T0m = flint.nmod_mat(T0, P)
        print(f'   (2) rank T0 (B_tau -> Z mod A) = {T0m.rank()} of {len(Btau)}', flush=True)
        # block pattern by head t of Z (rows of Z grouped by t) -- density of T0
        nz = sum(1 for r in T0 for x in r if x)
        print(f'   T0 density: {nz}/{len(T0) * len(T0[0])}', flush=True)
        # (3) Lambda content: the A-part of y is Phi_0(w) + e with w = sum f_k F^{(m)}_k + ...; Lambda_m(w)_tab
        #     = sum_s f_{tsab} - e-spread.  Here the A-coefficients are exactly (e, f) in the m-family basis.
        dens = []
        for coeffs in Wcoef:
            e, f = coeffs[:len(Es)], coeffs[len(Es):]
            lam = {}
            for (t, s, a, b), x in zip(Fold_lab, f):
                lam[(t, a, b)] = (lam.get((t, a, b), 0) + x) % P
            dens.append(sum(1 for v in lam.values() if v))
        print(f'   (3) nonzero Lambda_m(w) entries of the A-parts of the B_tau combinations: '
              f'{sorted(dens)[:5]}...{sorted(dens)[-3:]} (of {9 * m}); rank of the Lambda matrix: ', end='')
        LM = []
        for coeffs in Wcoef:
            e, f = coeffs[:len(Es)], coeffs[len(Es):]
            lam = {k: 0 for k in Zt}
            for (t, s, a, b), x in zip(Fold_lab, f):
                lam[(t, a, b)] = (lam[(t, a, b)] + x) % P
            LM.append([lam[k] for k in Zt])
        print(rank(LM), flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [5])
