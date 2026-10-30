#!/usr/bin/env python3
"""Intrinsic degeneracy of the E/F family under economic coalescence.

u_t(i) = (1 + eps b_i)^{x_t} exactly (economic: exp(beta_i) = 1 + eps b_i, integer
covariates x_t), eps = l (l-adic).  As eps -> 0 all blocks coalesce to one block.
Intrinsic measure: Smith exponents (over Z_(l)) of the evaluation matrix
[ v_k(X_j)_i ] of the family vectors at FIXED generic rational points X_j
(components i = 0,1; zero-sum), which does not depend on any coordinates on W_n.
Prints the exponent multiset for the DHW family F (with E) and, for comparison,
for the standard-tail family G (Theorem A) and the canonical family B.
What this does not show: the leading coefficient's nonvanishing for all n.
"""
import argparse
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, kernel_at, word_product  # noqa: E402
from hq_fresh_smith import smith_exponents, summarize  # noqa: E402

Q = 3


def family_eval(A, n, X, R, kind):
    mats = {w: kernel_at(A[w], X, R) for w in range(n)}
    out = []
    for s in range(n):
        for a in range(Q):
            K = mats[s]
            out.append([X[a] * ((1 if i == a else 0) - K[a][i]) for i in range(Q)])
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            if kind == 'F':
                W = word_product([s] + [u for u in range(n) if u not in (s, t)], mats, R)
                Wm = None
            elif kind == 'G':
                tail = [u for u in range(n) if u > s and u != t]
                W = word_product([s] + tail, mats, R)
                Wm = word_product(tail, mats, R) if tail else None
            else:
                W = mats[s]
                Wm = None
            for a in range(Q):
                for b in range(Q):
                    pref = X[a] * mats[t][a][b]
                    if Wm is None:
                        out.append([pref * ((1 if i == b else 0) - W[b][i]) for i in range(Q)])
                    else:
                        out.append([pref * (Wm[b][i] - W[b][i]) for i in range(Q)])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[2, 3, 4])
    ap.add_argument('--l', type=int, default=10007)
    args = ap.parse_args()
    R = Ring(None)
    l = args.l
    rng = random.Random(8)
    g = [[R(rng.randint(2, 60)) for _ in range(Q)] for _ in range(Q)]
    bb = [R(0), R(rng.randint(1, l - 1)), R(rng.randint(1, l - 1))]
    for n in args.n:
        xs = rng.sample(range(1, 40), n)
        us = [[(1 + R(l) * bb[i]) ** xs[t] for i in range(Q)] for t in range(n)]
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        N = 3 * n + 9 * n * (n - 1)
        pts = [[R(rng.randint(1, 50)) for _ in range(Q)] for _ in range(N // 2 + 6)]
        for kind in ('B', 'G', 'F'):
            rows = [[] for _ in range(N)]
            for X in pts:
                vals = family_eval(A, n, X, R, kind)
                for k in range(N):
                    rows[k].extend([vals[k][0], vals[k][1]])
            M = flint.fmpq_mat(rows)
            e = smith_exponents(M, l, K=200)
            print(f'n={n} kind={kind}: intrinsic Smith exponents {summarize(e)}  (sum {sum(e)})', flush=True)


if __name__ == '__main__':
    main()
