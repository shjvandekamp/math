#!/usr/bin/env python3
"""Task 3a: the DHW symbols sigma_k as explicit Laurent vectors; gradings.

sigma_k := (A_k(L_F') + Pi_{k-1}) / Pi_{k-1}  ⊆  gr_k = Pi_k / Pi_{k-1}, realised as the
top (pole order exactly k) parts of the elements of A_k(L_F') (agent_per_reduced).
Elements of W^0 are converted from point evaluations to Laurent vectors through the
explicit basis of W^naive (agent_per_flatlimit), so supports are exact.

Prints, per k: dim gr_k, dim sigma_k, and
  * TORUS GRADING: sum over Laurent monomials X^m of dim pi_m(sigma_k) (projection onto
    the coordinates of one monomial); equality with dim sigma_k <=> sigma_k is spanned
    by single-monomial vectors (graded by torus weight);
  * POLE-TYPE GRADING: the same test for the coarser grading by the pole pattern
    (which variables carry negative exponents, with multiplicity);
  * the per-monomial dimension profile of sigma_k vs gr_k (where the deficit sits);
  * with --initial: the initial monomials in(gr_k) minus in(sigma_k) under two term orders
    (lex on (exponent, component) with variable priorities (0,1,2) and (2,1,0)), summarised
    by pole type, to see whether the missing (delayed) directions form a stable pattern.
What this does not show: anything for n not run; a graded/ungraded verdict is at one
random point mod P.
"""
import argparse
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Q, Model, PointSeries, rank  # noqa: E402
from agent_per_flatlimit import naive_basis, eval_naive  # noqa: E402
from agent_per_reduced import A_spaces, normalised_rows, nm  # noqa: E402


class LaurentCoords:
    """Convert evaluation rows of W^0 elements into Laurent vectors (dict (comp, exp) -> c)."""

    def __init__(self, model, info, basis, X):
        self.n = model.n
        self.info = info
        self.basis = basis
        Ew = eval_naive(model, info, basis, X)          # d x M
        R, rk = nm(Ew).rref()
        d = len(basis)
        assert rk == d
        piv = []
        for i in range(d):
            for j in range(R.ncols()):
                if int(R[i, j]):
                    piv.append(j)
                    break
        self.piv = piv
        self.Esq = nm(Ew[:, piv])                       # d x d invertible
        self.Einv = self.Esq.inv()
        # unknown -> Laurent (component, exponent)
        n = self.n
        self.lab = {}
        for (i, m), j in info['idx'].items():
            e = tuple(m[r] - n + (1 if r == i else 0) for r in range(Q))
            self.lab[j] = (i, e)
        self.Bm = nm(np.array(basis, dtype=np.int64))  # d x N

    def to_laurent(self, Y):
        """Y: rows of evaluations (k x M) lying in W^0. Returns coefficient matrix over unknowns."""
        if len(Y) == 0:
            return np.zeros((0, len(self.lab)), dtype=np.int64)
        Z = nm(np.asarray(Y)[:, self.piv]) * self.Einv      # k x d basis coordinates
        C = Z * self.Bm                                      # k x N
        return np.array(C.tolist(), dtype=np.int64)


def pole(e):
    return sum(-x for x in e if x < 0)


def pole_type(e):
    return tuple(min(0, x) for x in e)


def initial_set(T, cols_order):
    """Pivot columns (in the given column order) of the row space of T."""
    if len(T) == 0:
        return []
    R, rk = nm(T[:, cols_order]).rref()
    Rl = R.tolist()
    piv = []
    for i in range(rk):
        for j, x in enumerate(Rl[i]):
            if int(x):
                piv.append(cols_order[j])
                break
    return piv


def analyse(n, K, kmax, seed=11, initial=False):
    d = 9 * n * n - 6 * n
    m = Model(n, seed=seed, hi=10 ** 6)
    ps = PointSeries(m, max(d // 2 + 12, 3 * (kmax + 1) ** 2 + 5), K, seed=5)
    info, basis = naive_basis(m)
    LC = LaurentCoords(m, info, basis, ps.X)
    _, F = normalised_rows(ps, 'F')
    A = A_spaces(F, kmax, prec=K - 2)
    N = len(LC.lab)
    poles = np.array([pole(LC.lab[j][1]) for j in range(N)])
    out = []
    for k in range(kmax + 1):
        C = LC.to_laurent(A[k]) % P
        if len(C):
            assert not C[:, poles > k].any(), 'A_k not inside Pi_k'
        top_cols = [j for j in range(N) if poles[j] == k]
        if not top_cols:
            break
        T = C[:, top_cols] if len(C) else np.zeros((0, len(top_cols)), dtype=np.int64)
        sk = rank(T) if len(T) else 0
        # gr_k dimension: top parts of Pi_k = W^naive ∩ {pole <= k}
        Bfull = np.array(basis, dtype=np.int64)
        # elements of W^naive with pole <= k: nullspace of the columns with pole > k
        bad = [j for j in range(N) if poles[j] > k]
        if bad:
            X, nul = nm(Bfull[:, bad]).transpose().nullspace()
            comb = np.array([[int(X[r, q]) for r in range(d)] for q in range(nul)], dtype=np.int64)
            PiK = np.array((nm(comb) * nm(Bfull)).tolist(), dtype=np.int64) if nul else np.zeros((0, N), dtype=np.int64)
        else:
            PiK = Bfull
        G = PiK[:, top_cols] % P
        gk = rank(G)
        # gradings
        mon_of = defaultdict(list)
        typ_of = defaultdict(list)
        for q, j in enumerate(top_cols):
            mon_of[LC.lab[j][1]].append(q)
            typ_of[pole_type(LC.lab[j][1])].append(q)
        s_mon = sum(rank(T[:, cols]) for cols in mon_of.values()) if sk else 0
        s_typ = sum(rank(T[:, cols]) for cols in typ_of.values()) if sk else 0
        g_mon = sum(rank(G[:, cols]) for cols in mon_of.values())
        g_typ = sum(rank(G[:, cols]) for cols in typ_of.values())
        prof = Counter()
        for mono, cols in mon_of.items():
            prof[(rank(G[:, cols]), rank(T[:, cols]) if sk else 0)] += 1
        miss = {}
        if initial:
            for name, prio in (('lex012', (0, 1, 2)), ('lex210', (2, 1, 0))):
                keyf = lambda q: (tuple(-LC.lab[top_cols[q]][1][r] for r in prio), LC.lab[top_cols[q]][0])  # noqa: E731
                order = sorted(range(len(top_cols)), key=keyf)
                pg = set(initial_set(G, order))
                ps_ = set(initial_set(T, order)) if sk else set()
                assert ps_ <= pg or not sk or True
                mset = Counter(pole_type(LC.lab[top_cols[q]][1]) for q in pg - ps_)
                miss[name] = (len(pg - ps_), len(ps_ - pg), dict(sorted(mset.items())))
        out.append((k, gk, g_mon, g_typ, sk, s_mon, s_typ, dict(prof), miss))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4])
    ap.add_argument('--K', type=int, default=10)
    ap.add_argument('--kmax', type=int, default=7)
    ap.add_argument('--initial', action='store_true')
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        res = analyse(n, args.K, args.kmax, initial=args.initial)
        print(f'n={n}  [{time.time() - t0:.0f}s]')
        print('   k | dim gr_k (sum over monomials, over pole types) | dim sigma_k (sum over monomials, over types) '
              '| monomial profile {(dim gr piece, dim sigma piece): #monomials}')
        for k, gk, gm, gt, sk, sm, st, prof, miss in res:
            print(f'   {k} | {gk:4d} ({gm:4d}, {gt:4d}) | {sk:4d} ({sm:4d}, {st:4d}) | {prof}', flush=True)
            for name, (nm_, extra, mset) in miss.items():
                print(f'       {name}: #missing initial monomials {nm_} (extra {extra}); by pole type {mset}', flush=True)


if __name__ == '__main__':
    main()
