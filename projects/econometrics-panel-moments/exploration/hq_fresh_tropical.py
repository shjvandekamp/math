#!/usr/bin/env python3
"""Single-dominant-term probe: valuation matrix of R_n at tropical points.

Product-form blocks with g(i,a) = c * l^{gamma_ia}, u_t(i) = c' * l^{w_t(i)}
(epsilon = l prime, c, c' random l-adic units).  Exact R_n (fmpq); entry
valuations V_ij = v_l(R_ij).  If the min-cost perfect matching of V is
unique, det R_n has a single dominant term, so det R_n != 0 near the
tropical point and the leading coefficient is a product of entry leading
coefficients.  Reported: trop det, v(det R_n), uniqueness.

What this does not show: anything for n beyond those run; uniqueness at a
sampled point is a finite certificate only.
"""
import argparse
import random
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linear_sum_assignment

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, build_R, geometry_ok  # noqa: E402

Q = 3
BIG = 10 ** 6


def vl_int(x, l):
    v = 0
    while x % l == 0:
        x //= l
        v += 1
    return v


def vl(x, l):
    if x == 0:
        return None
    return vl_int(abs(int(x.p)), l) - vl_int(int(x.q), l)


def tropical_blocks(n, l, gam, ws, rng):
    Rq = Ring(None)

    def lp(k):
        return Rq(l) ** k if k >= 0 else Rq(1) / Rq(l) ** (-k)
    for _ in range(50):
        g = [[Rq(rng.randint(1, l - 1)) * lp(gam[i][a]) for a in range(Q)] for i in range(Q)]
        us = [[Rq(rng.randint(1, l - 1)) * lp(ws[t][i]) for i in range(Q)] for t in range(n)]
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        if geometry_ok(A, n):
            return A
    return None


def matching_info(V):
    N = V.shape[0]
    C = np.where(V == None, BIG, V).astype(np.int64)  # noqa: E711
    r, c = linear_sum_assignment(C)
    opt = int(C[r, c].sum())
    if opt >= BIG:
        return None, False, None
    unique = True
    for i in range(N):
        C2 = C.copy()
        C2[r[i], c[i]] = BIG
        r2, c2 = linear_sum_assignment(C2)
        if int(C2[r2, c2].sum()) == opt:
            unique = False
            break
    return opt, unique, (r, c)


def probe(n, l, gam, ws, rng, want_det=True):
    A = tropical_blocks(n, l, gam, ws, rng)
    if A is None:
        return None
    Rq = Ring(None)
    cols, rows = build_R(A, n, Rq)
    M = [rows[key] for key in cols]
    N = len(cols)
    V = np.empty((N, N), dtype=object)
    for i in range(N):
        for j in range(N):
            V[i, j] = vl(M[i][j], l)
    opt, unique, _ = matching_info(V)
    vdet = None
    if want_det:
        import flint
        d = flint.fmpq_mat(M).det()
        vdet = vl(d, l)
    return opt, vdet, unique


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=3)
    ap.add_argument('--trials', type=int, default=40)
    ap.add_argument('--range', type=int, default=3)
    ap.add_argument('--l', type=int, default=10007)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--economic', action='store_true',
                    help='w_t = x_t * b (one-parameter subgroup), x_t increasing integers')
    args = ap.parse_args()
    rng = random.Random(args.seed)
    stats = {'unique': 0, 'equal': 0, 'cancel': 0, 'none': 0}
    for trial in range(args.trials):
        gam = [[rng.randint(0, args.range) for _ in range(Q)] for _ in range(Q)]
        if args.economic:
            b = [rng.randint(-args.range, args.range) for _ in range(Q)]
            xs = sorted(rng.sample(range(0, 4 * args.range + 4), args.n))
            ws = [[x * bi for bi in b] for x in xs]
        else:
            ws = [[rng.randint(0, args.range) for _ in range(Q)] for _ in range(args.n)]
        res = probe(args.n, args.l, gam, ws, rng)
        if res is None:
            stats['none'] += 1
            continue
        opt, vdet, unique = res
        tag = 'UNIQUE' if unique else ('equal' if vdet == opt else 'CANCEL')
        stats['unique' if unique else ('equal' if vdet == opt else 'cancel')] += 1
        print(f'trial {trial}: gamma={gam} w={ws}: trop det={opt} v(det)={vdet} {tag}', flush=True)
    print('summary', stats)


if __name__ == '__main__':
    main()
