#!/usr/bin/env python3
"""Task 2b: the Smith-reduced DHW problem inside the flat limit W^0 = W^naive.

Normalised families (every member has eps-valuation 0, leading term in W^0):
  B'  : eta_sb = E_sb/(-eps) = f_sb nu_sb,  beta_tasb = f_ta f_sb nu_sb
        (= B/(-eps) for a = b, B/(-eps^2 c_tab) for a != b)          [canonical basis]
  F'  : E/(-eps), F_{t,s,a,a}/(-eps), F_{t,s,a,b}/(-eps^2 c_tab)      [DHW]
  G'  : the same normalisation applied to the standard-tail family G.
For a C[[eps]]-lattice L of full rank in W(eps) put
  A_k(L) := { [eps^k] w : w in L, w = O(eps^k) }  ⊆ W^0,   A_0 ⊆ A_1 ⊆ ... ⊆ W^0,
dim A_k = #{Smith exponents of L in L_sat that are <= k} (intrinsic, no coordinates).
A_k is computed exactly mod P by block-Toeplitz linear algebra on eps-series evaluated
at random points (combinations with polynomial coefficients of degree <= k).

Also: the pole-order filtration of W^0 = W^naive (agent_per_flatlimit):
  Pi_k := { v in W^naive : every Laurent monomial X^m of v has sum_j max(0,-m_j) <= k }.
Prints dim A_k(B'), dim A_k(G'), dim A_k(F'), dim Pi_k, and the dimensions of
A_k(B') + Pi_k, A_k(F') + Pi_k, A_k(F') + A_k(B') (inclusion tests).
With --bigrade also the table dim(A_k(F') ∩ Pi_j) (LAG-1 test: Pi_{k-1} ⊆ A_k(F') for all k).
Exactness: the vanishing constraints at order m use both components at 3(m+1)^2 + 5 points,
enough for injectivity on zero-sum Laurent vectors of pole order <= m (every eps^m-coefficient
of a normalised family member has pole order <= m); off-diagonal rows lose two orders of
precision, so kmax <= K - 2 is enforced.
What this does not show: anything for n beyond those run; ranks are mod P at one point.
"""
import argparse
import sys
import time
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Q, Model, PointSeries, family_rows, rank, inv  # noqa: E402
from agent_per_flatlimit import naive_basis, eval_naive  # noqa: E402


def normalised_rows(ps, kind):
    """Rows of the normalised family (valuation 0)."""
    labels, rows = family_rows(ps, kinds=(kind,))
    K = ps.K
    out = np.zeros_like(rows)
    for j, lab in enumerate(labels):
        if lab[0] == 'E':
            v, cst = 1, P - 1
        else:
            _, t, s, a, b = lab
            if a == b:
                v, cst = 1, P - 1
            else:
                v, cst = 2, (-ps.m.c[t][a][b]) % P
        assert not rows[j, :v].any(), (lab, 'valuation lower than expected')
        ci = inv(cst)
        out[j, :K + 1 - v] = (rows[j, v:] * ci) % P
    return labels, out


def order_coords(M, mm):
    """Coordinates for the order-mm constraint block: both components at the first
    3(mm+1)^2 + 5 points (injective on zero-sum Laurent vectors of pole order <= mm)."""
    npts = M // 2
    h = min(npts, 3 * (mm + 1) ** 2 + 5)
    return list(range(h)) + list(range(npts, npts + h))


def nm(arr):
    return flint.nmod_mat((np.asarray(arr) % P).tolist(), P)


def A_spaces(rows, kmax, prec=None):
    """A_k for k = 0..kmax as arrays of evaluation rows (full M coordinates).
    prec: valid orders are 0..prec (rows are exact there); requires kmax <= prec."""
    d, K1, M = rows.shape
    if prec is not None:
        assert kmax <= prec, 'kmax exceeds the series precision'
    res = []
    for k in range(kmax + 1):
        if k == 0:
            res.append(rows[:, 0, :] % P)
            continue
        nun = d * (k + 1)
        cs = [order_coords(M, mm) for mm in range(k)]
        offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
        C = np.zeros((int(offs[-1]), nun), dtype=np.int64)
        Im = np.zeros((M, nun), dtype=np.int64)
        for l in range(k + 1):
            for mm in range(l, k):
                C[int(offs[mm]):int(offs[mm + 1]), l * d:(l + 1) * d] = rows[:, mm - l, cs[mm]].T
            Im[:, l * d:(l + 1) * d] = rows[:, k - l, :].T
        X, nul = nm(C).nullspace()
        if nul == 0:
            res.append(np.zeros((0, M), dtype=np.int64))
            continue
        Xs = flint.nmod_mat([[int(X[i, j]) for j in range(nul)] for i in range(nun)], P)
        img = nm(Im) * Xs                       # M x nul
        Mi = np.array(img.transpose().tolist(), dtype=np.int64)
        res.append(Mi)
    return res


def laurent_pole_filtration(model, info, basis, kmax):
    """Pi_k as sub-bases (lists of coefficient vectors in the naive unknowns)."""
    n = model.n
    idx, mons = info['idx'], info['mons']
    # pole order of unknown (i, m): Laurent monomial of component i is X_i X^m / (X0X1X2)^n
    pole = {}
    for (i, m), j in idx.items():
        e = [m[r] - n + (1 if r == i else 0) for r in range(Q)]
        pole[j] = sum(-x for x in e if x < 0)
    B = flint.nmod_mat(basis, P)            # dim x N
    out = []
    for k in range(kmax + 1):
        bad = [j for j in range(info['N']) if pole[j] > k]
        if not bad:
            out.append(basis)
            continue
        # combos c with (c B)[bad] = 0
        sub = flint.nmod_mat([[int(B[r, j]) for j in bad] for r in range(B.nrows())], P)   # dim x |bad|
        X, nul = sub.transpose().nullspace()
        combos = [[int(X[r, q]) for r in range(B.nrows())] for q in range(nul)]
        vecs = []
        if combos:
            Cm = flint.nmod_mat(combos, P) * B
            vecs = [[int(Cm[q, j]) for j in range(info['N'])] for q in range(Cm.nrows())]
        out.append(vecs)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4])
    ap.add_argument('--K', type=int, default=8)
    ap.add_argument('--kmax', type=int, default=6)
    ap.add_argument('--bigrade', action='store_true')
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        m = Model(n, seed=11, hi=10 ** 6)
        ps = PointSeries(m, max(d // 2 + 12, 3 * (args.kmax + 1) ** 2 + 5), args.K, seed=5)
        info, basis = naive_basis(m)
        assert len(basis) == d
        Pi = laurent_pole_filtration(m, info, basis, args.kmax)
        Pi_eval = [eval_naive(m, info, b, ps.X) if b else np.zeros((0, 2 * ps.npts), dtype=np.int64)
                   for b in Pi]
        fams = {}
        for kind in ('B', 'G', 'F'):
            _, rows = normalised_rows(ps, kind)
            fams[kind] = A_spaces(rows, args.kmax, prec=args.K - 2)
        print(f'n={n} (d={d}) [{time.time() - t0:.0f}s]')
        print('   k : dimA(B) dimA(G) dimA(F) dimPi | A(B)+Pi A(F)+Pi A(F)+A(B)')
        for k in range(args.kmax + 1):
            AB, AG, AF, PI = fams['B'][k], fams['G'][k], fams['F'][k], Pi_eval[k]
            rB, rG, rF, rP = rank(AB), rank(AG), rank(AF), rank(PI)
            print(f'   {k} : {rB:6d} {rG:6d} {rF:6d} {rP:6d} | {rank(np.vstack([AB, PI])):7d} '
                  f'{rank(np.vstack([AF, PI])):7d} {rank(np.vstack([AF, AB])):10d}', flush=True)
        if args.bigrade:
            print('   dim(A_k(F) ∩ Pi_j), rows k, columns j = 0..kmax;  LAG-1 <=> entry (k, k-1) = dim Pi_{k-1}')
            lag1 = True
            for k in range(args.kmax + 1):
                AF = fams['F'][k]
                rA = rank(AF)
                row = []
                for j in range(args.kmax + 1):
                    rP = rank(Pi_eval[j])
                    row.append(rA + rP - (rank(np.vstack([AF, Pi_eval[j]])) if len(AF) else rP))
                if k >= 1 and row[k - 1] != rank(Pi_eval[k - 1]):
                    lag1 = False
                print(f'   k={k}: dimA={rA:4d} |', ' '.join(f'{x:4d}' for x in row), flush=True)
            print(f'   LAG-1 (Pi_(k-1) ⊆ A_k(F) for k = 1..{args.kmax}): {lag1}')


if __name__ == '__main__':
    main()
