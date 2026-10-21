#!/usr/bin/env python3
"""Task 2c/4: the containment  eps * L_B'  ⊆  L_F'  (conjecture E1) and the defect.

L_B' = C[[eps]]-span of the normalised canonical family {eta_sb = f_sb nu_sb,
beta_tasb = f_ta f_sb nu_sb}; L_F' = span of the normalised DHW family
{E/(-eps), F_{t,s,a,a}/(-eps), F_{t,s,a,b}/(-eps^2 c_tab)} (agent_per_reduced).
E1 says: every eps*beta (and eps*eta) is a C[[eps]]-combination of the DHW family.
E1 implies L_F' has full rank, i.e. det R_n != 0 (for that n).

Method (exact mod P at one random product-form point, eps-series):
 1. saturate(L_F') gives e = max shift with eps^e L_sat ⊆ L_F' and the index
    [L_sat : L_F'];  same for L_B'.  delta_n = [L_B' : L_F'] = difference of the indices.
 2. x in L_sat lies in L_F' iff  sum_i alpha_i(eps) F'_i = x  mod eps^e  is solvable with
    polynomials alpha_i of degree < e.  All x = eps*B'_j are tested at once by one rank
    comparison rank[A] = rank[A | RHS] (block-Toeplitz A, orders 0..e-1).
 Evaluation points: npts >= 3 e^2 + 10 so that evaluation is injective on every
 eps^m-coefficient space (m < e) of zero-sum Laurent vectors of pole order <= m
 (dimension 2 * 3 (m+1)^2), hence the vanishing constraints are exact.
Also tests eps^2 * L_B' ⊆ L_F' (true at n = 3 where E1 fails).
What this does not show: E1 for n not run; the rank is mod P at one point (a
full-rank/containment certificate is valid for that n generically only if it holds
at the point -- a failure at one point would be evidence only).
"""
import argparse
import sys
import time
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Model, PointSeries, saturate  # noqa: E402
from agent_per_reduced import normalised_rows  # noqa: E402


def nm(arr):
    return flint.nmod_mat((np.asarray(arr) % P).tolist(), P)


def order_coords(M, mm):
    """Evaluation coordinates used for the order-mm block: both components (layout
    [comp1 at pts | comp2 at pts]) at the first h = 3(mm+1)^2 + 5 points, enough for
    injectivity on zero-sum Laurent vectors of pole order <= mm (3(mm+1)^2 monomials)."""
    npts = M // 2
    h = min(npts, 3 * (mm + 1) ** 2 + 5)
    return list(range(h)) + list(range(npts, npts + h))


def containment(Frows, Xrows, e):
    """Are all rows of Xrows (series, valuation >= 0) in the C[[eps]]-span of Frows?
    Uses orders 0..e-1 only (valid if eps^e L_sat ⊆ span Frows)."""
    d, _, M = Frows.shape
    cs = [order_coords(M, mm) for mm in range(e)]
    offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
    A = np.zeros((int(offs[-1]), d * e), dtype=np.int64)
    RHS = np.zeros((int(offs[-1]), Xrows.shape[0]), dtype=np.int64)
    for mm in range(e):
        r0, r1 = int(offs[mm]), int(offs[mm + 1])
        for l in range(mm + 1):
            A[r0:r1, l * d:(l + 1) * d] = Frows[:, mm - l, cs[mm]].T
        RHS[r0:r1, :] = Xrows[:, mm, cs[mm]].T
    rA = nm(A).rank()
    rAX = nm(np.hstack([A, RHS])).rank()
    return rA, rAX


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4, 5])
    ap.add_argument('--seed', type=int, default=21)
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        emax_guess = 2 * n + 2
        K = emax_guess + 3
        npts = max(d // 2 + 12, 3 * emax_guess ** 2 + 10)
        m = Model(n, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(m, npts, K, seed=args.seed + 1)
        _, F = normalised_rows(ps, 'F')
        _, B = normalised_rows(ps, 'B')
        F = F[:, :K - 1, :].copy()
        B = B[:, :K - 1, :].copy()
        sF = saturate(F, K - 2)['shifts']
        sB = saturate(B, K - 2)['shifts']
        e = int(sF.max())
        assert e <= emax_guess
        epsB = np.zeros_like(B)
        epsB[:, 1:, :] = B[:, :-1, :]
        eps2B = np.zeros_like(B)
        eps2B[:, 2:, :] = B[:, :-2, :]
        r1 = containment(F, epsB, e)
        r2 = containment(F, eps2B, e)
        print(f'n={n}: [L_sat:L_B\'] = {int(sB.sum())}, [L_sat:L_F\'] = {int(sF.sum())}, '
              f'delta_n = {int(sF.sum() - sB.sum())}, e = {e}; '
              f'eps*L_B\' ⊆ L_F\': {r1[0] == r1[1]} (ranks {r1}); '
              f'eps^2*L_B\' ⊆ L_F\': {r2[0] == r2[1]}  [{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
