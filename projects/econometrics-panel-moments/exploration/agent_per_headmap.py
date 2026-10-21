#!/usr/bin/env python3
"""Task 4 probe: is the (normalised) head map regular on the canonical lattice L_B'?

Head map (project definition, agent_ag_lib.head_map_matrix):
    Lambda(w)_{tab} = sum_s [F_{t,s,a,b}-coefficient of w] - [E_{t,a}-coefficient of w].
Normalised (persistence): Lambda'(w)_{tab} := n_ab Lambda(w)_{tab}, n_aa = -eps,
n_ab = -eps^2 c_tab; in F'/eta coordinates  w = sum alpha F' + sum gamma eta:
    Lambda'(w)_{tab} = sum_s alpha_{tsab} - [a = b] gamma_ta - [a != b] eps c_tab gamma_ta.
Appending the latest block, Phi_n(w) = w K_N + sum_tab Lambda'(w)_tab B'_{t,N,a,b}
(normalised form of the project's append map).  If E1(n) holds and
    (*)  Lambda'(L_B') ⊆ C[[eps]]^{9n},
then eps * (old canonical part G' K_N) ⊆ L_F'^(n+1) + eps*span{B'_{t,N}}, which is one of
the three pieces of an inductive proof of E1(n+1).  This script computes, for every
normalised canonical vector beta, the F'/eta-coordinates of eps*beta modulo eps (exact
mod P, block-Toeplitz with one extra order so that the constant terms are determined)
and reports the rank of the map beta -> Lambda'(eps*beta) mod eps (0 <=> (*) holds).
What this does not show: anything when (*) fails beyond the failure itself.
"""
import argparse
import sys
import time
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Q, Model, PointSeries, saturate  # noqa: E402
from agent_per_reduced import normalised_rows  # noqa: E402
from agent_per_e1 import nm, order_coords  # noqa: E402


def coords_mod_eps(Frows, Xrows, e):
    """Constant terms alpha_i(0) of the unique C[[eps]]-solution of sum alpha_i F_i = x
    for each x in Xrows; uses orders 0..e (needs eps^e L_sat ⊆ span F, so that
    solutions mod eps^(e+1) agree mod eps)."""
    d, _, M = Frows.shape
    E1 = e + 1
    cs = [order_coords(M, mm) for mm in range(E1)]
    offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
    A = np.zeros((int(offs[-1]), d * E1), dtype=np.int64)
    RHS = np.zeros((int(offs[-1]), Xrows.shape[0]), dtype=np.int64)
    for mm in range(E1):
        r0, r1 = int(offs[mm]), int(offs[mm + 1])
        for l in range(mm + 1):
            A[r0:r1, l * d:(l + 1) * d] = Frows[:, mm - l, cs[mm]].T
        RHS[r0:r1, :] = Xrows[:, mm, cs[mm]].T
    Aug = nm(np.hstack([A, RHS]))
    R, rk = Aug.rref()
    ncA = d * E1
    # pivot columns
    piv = []
    r = 0
    for c in range(Aug.ncols()):
        if r < rk and int(R[r, c]) != 0:
            piv.append(c)
            r += 1
    assert all(c < ncA for c in piv), 'inconsistent system (x not in the lattice)'
    # particular solution with free variables 0: alpha[piv[i]] = R[i, rhs]
    sol = np.zeros((ncA, Xrows.shape[0]), dtype=np.int64)
    Rl = R.tolist()
    for i, c in enumerate(piv):
        sol[c, :] = [int(x) for x in Rl[i][ncA:]]
    # check uniqueness of the constant terms: the kernel of A must have zero l=0 part
    X, nul = nm(A).nullspace()
    Xl = X.tolist()
    ker0 = max((sum(1 for i in range(d) if int(Xl[i][q]) != 0) for q in range(nul)), default=0)
    return sol[:d, :], ker0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--seed', type=int, default=21)
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        emax_guess = 2 * n + 2
        K = emax_guess + 4
        npts = max(d // 2 + 12, 3 * (emax_guess + 1) ** 2 + 10)
        m = Model(n, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(m, npts, K, seed=args.seed + 1)
        labF, F = normalised_rows(ps, 'F')
        labB, B = normalised_rows(ps, 'B')
        F = F[:, :K - 1, :].copy()
        B = B[:, :K - 1, :].copy()
        e = int(saturate(F, K - 2)['shifts'].max())
        epsB = np.zeros_like(B)
        epsB[:, 1:, :] = B[:, :-1, :]
        alpha0, ker0 = coords_mod_eps(F, epsB, e)        # d x d (rows: F'/eta labels, cols: beta)
        # head map mod eps
        heads = [(t, a, b) for t in range(n) for a in range(Q) for b in range(Q)]
        hpos = {h: i for i, h in enumerate(heads)}
        Lam = np.zeros((len(heads), d), dtype=np.int64)
        for i, lab in enumerate(labF):
            if lab[0] == 'F':
                _, t, s, a, b = lab
                Lam[hpos[(t, a, b)], :] += alpha0[i, :]
            else:
                _, s, a = lab
                Lam[hpos[(s, a, a)], :] -= alpha0[i, :]     # off-diagonal gamma term is O(eps)
        Lam %= P
        rk = nm(Lam).rank() if Lam.any() else 0
        # split by type of beta (eta / beta diag / beta off)
        types = {}
        for j, lab in enumerate(labB):
            key = 'eta' if lab[0] == 'E' else ('beta_diag' if lab[3] == lab[4] else 'beta_off')
            types.setdefault(key, []).append(j)
        per = {k: (nm(Lam[:, v]).rank() if Lam[:, v].any() else 0) for k, v in types.items()}
        print(f'n={n}: e={e}; constant terms unique: {ker0 == 0}; rank of beta -> Lambda\'(eps beta) mod eps '
              f'= {rk} (0 <=> (*) holds); by type {per}  [{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
