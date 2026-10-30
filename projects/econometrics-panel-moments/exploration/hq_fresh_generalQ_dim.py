#!/usr/bin/env python3
"""General Q: dim M_T = ell(Q,T) for 3 <= T <= Q+1 (notes sec. 6.5).  Checks mod p = 2^61-1.

(1) Multi-block lemma for k <= Q-1 blocks at the uniform witness point (g(j,r) = w_r^j,
    u_t(j) = z_t^j): the fat ideal J^(k) (f vanishes to order #{t : x in B_t} at every x,
    imposed by all partial derivatives at random points of every stratum = intersection of
    base-locus components of distinct blocks) satisfies
        dim J^(k)_{kQ} = (Q+1)^k   and   dim J^(k)_{kQ+1} = dim S_1 H_1...H_k = Q^{k+1} - ell(Q,k+1).
(2) Independent check: dim M_T from the raw path likelihoods at a random economic point
    equals ell(Q,T) (and DHW's closed form Q^T - Q(2+Q-T)(1+Q)^(T-2) in this range).
What this does not show: anything for T > Q+1 (there the products are dependent).
"""
import itertools as it
import random
import sys
from math import comb
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_generalQ_T4 import monos, polymul, lin, evalm, point_on, P  # noqa: E402


def ell(Q, T):
    return sum(comb(T - 1 - max(j - (Q - 2), 0), min(Q - 2, j)) * (T - 2 - j) * Q ** (j + 1) for j in range(T - 2))


def deriv_rows(ms, x, Q, order):
    rows = []
    for o in range(order):
        for alpha in it.combinations_with_replacement(range(Q), o):
            r = []
            for m in ms:
                mm = list(m)
                c = 1
                ok = True
                for i in alpha:
                    if mm[i] == 0:
                        ok = False
                        break
                    c = c * mm[i] % P
                    mm[i] -= 1
                r.append(c * evalm(tuple(mm), x) % P if ok else 0)
            rows.append(r)
    return rows


def witness_blocks(Q, k):
    w = [2 ** r for r in range(Q)]
    z = [2 ** (Q * (t + 1)) for t in range(k)]
    return [[[pow(w[r], j, P) * pow(z[t], j, P) % P for j in range(Q)] for r in range(Q)] for t in range(k)]


def fat_dim(Q, A, d, rng):
    k = len(A)
    eta = [[1 if j == i else 0 for j in range(Q)] for i in range(Q)]
    comps = [[[A[t][s], A[t][s2]] for s, s2 in it.combinations(range(Q), 2)] + [[eta[r], A[t][r]] for r in range(Q)]
             for t in range(k)]
    ms = monos(Q, d)
    rows = []
    for S in range(1, k + 1):
        for blocks in it.combinations(range(k), S):
            for choice in it.product(*[comps[t] for t in blocks]):
                basis = []
                for f in (f for c in choice for f in c):
                    if flint.nmod_mat(basis + [f], P).rank() > len(basis):
                        basis.append(f)
                if len(basis) >= Q:
                    continue
                dimZ = Q - 1 - len(basis)
                npts = (comb(d + dimZ, dimZ) + 3) if dimZ > 0 else 1
                for _ in range(npts):
                    rows += deriv_rows(ms, point_on(basis, Q, rng), Q, S)
    return len(ms) - flint.nmod_mat(rows, P).rank()


def product_span_dim(Q, A):
    k = len(A)
    eta = [[1 if j == i else 0 for j in range(Q)] for i in range(Q)]
    Hs = []
    for t in range(k):
        H = []
        for r in range(Q):
            f = lin(eta[r])
            for s in range(Q):
                if s != r:
                    f = polymul(f, lin(A[t][s]))
            H.append(f)
        Hs.append(H)
    polys = [lin(e) for e in eta]
    for H in Hs:
        polys = [polymul(p, h) for p in polys for h in H]
    ms = monos(Q, k * Q + 1)
    return flint.nmod_mat([[pl.get(m, 0) for m in ms] for pl in polys], P).rank()


def raw_dim(Q, T, rng):
    g = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
    w = [rng.randint(2, 10 ** 6) for _ in range(Q)]
    xs = rng.sample(range(1, 31), T)   # distinct covariate values (repeats are special points)
    pi = [[[g[q][r] * pow(w[q], xs[t], P) % P for r in range(Q)] for q in range(Q)] for t in range(T)]
    cols = []
    for _ in range(Q ** T + 5):
        eta = [rng.randint(1, P - 1) for _ in range(Q)]
        layer = [(1, 0)]
        for t in range(T):
            Kt = []
            for a in range(Q):
                inv = pow(sum(pi[t][j][a] * eta[j] for j in range(Q)) % P, -1, P)
                Kt.append([pi[t][i][a] * eta[i] % P * inv % P for i in range(Q)])
            layer = [(v * Kt[prev][y] % P, y) for (v, prev) in layer for y in range(Q)]
        cols.append([v for v, _ in layer])
    return Q ** T - flint.nmod_mat(cols, P).rank()


def main():
    rng = random.Random(5)
    for Q, k in [(3, 1), (3, 2), (4, 2), (4, 3), (5, 2), (5, 3)]:
        A = witness_blocks(Q, k)
        d0, d1 = fat_dim(Q, A, k * Q, rng), fat_dim(Q, A, k * Q + 1, rng)
        ps = product_span_dim(Q, A)
        print(f'Q={Q} k={k}: dim J_kQ = {d0} (want {(Q + 1) ** k}); dim J_(kQ+1) = {d1}, dim S_1 H..H = {ps} '
              f'(want {Q ** (k + 1) - ell(Q, k + 1)})', flush=True)
    for Q, T in [(3, 3), (3, 4), (4, 4), (4, 5), (5, 4), (5, 5)]:
        print(f'raw dim M_{T} (Q={Q}) = {raw_dim(Q, T, rng)}; ell = {ell(Q, T)}; '
              f'closed form = {Q ** T - Q * (2 + Q - T) * (1 + Q) ** (T - 2)}', flush=True)


if __name__ == '__main__':
    main()
