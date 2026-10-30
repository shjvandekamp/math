#!/usr/bin/env python3
"""General Q, T <= Q+1: the quotient images are unitriangular over canonical multi-head columns.

(1) Exact (Fraction) brute-force check of the conditional-sum image of EVERY new (24) column (all j,
    shared periods >= 2) for (Q,T) = (3,4), (4,4), (4,5), (5,5):
        C(m) = K_1(y0,q_1) prod_l K_{t_l+1}(q_l, q_{l+1}) K_{t_j+1}(q_j, q_0) e_{q_0} (I - K_{s2+1} P)
    (q_{j+1} := q_0; P = increasing product of the remaining transitions); for j = 0 the prefix is
    K_1(y0,q_0) and the head chain is empty.
(2) mod 2^61-1: the canonical multi-head family C(H, q_H; s, q0) = prod_{u in H} (X_{q_u}/L_{u q_u}) *
    X_{q0} e_{q0} (I - K_s) (H a set of blocks, s not in H) has full rank as vector functions
    (evaluation at random points) for (Q, n) = (4,2), (4,3), (5,3), (5,4) and is rank-deficient for
    n = Q (e.g. (3,3)), so deep strata are needed.
"""
import itertools as it
import random
import sys
from fractions import Fraction
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hq_fresh_generalQ as GQ  # noqa: E402

P = (1 << 61) - 1


def kernels(pi, X, Q, T):
    Ks = []
    for t in range(T):
        K = []
        for a in range(Q):
            L = sum(pi[t][j][a] * X[j] for j in range(Q))
            K.append([pi[t][i][a] * X[i] / L for i in range(Q)])
        Ks.append(K)
    return Ks


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def check_images(Q, T, rng):
    pi = [[[Fraction(rng.randint(1, 9)) for _ in range(Q)] for _ in range(Q)] for _ in range(T)]
    X = [Fraction(rng.randint(1, 9)) for _ in range(Q)]
    y0 = 0
    Ks = kernels(pi, X, Q, T)
    paths = list(it.product(range(Q), repeat=T))
    py = {}
    for y in paths:
        w = Fraction(1)
        prev = y0
        for t in range(T):
            w *= Ks[t][prev][y[t]]
            prev = y[t]
        py[y] = w
    n_new = 0
    for shared, s1, s2, values, tau1, tau2 in GQ.source_indices(Q, T):
        if 0 in shared:
            continue                       # lift (period 1 shared)
        q0 = values[0]
        C = [Fraction(0)] * Q
        for y in paths:
            if any(y[t] != v for t, v in zip(shared, values[1:])):
                continue
            a_ = GQ.weight(y, tau1, y0, pi) if y[s1] == q0 else 0
            b_ = GQ.weight(y, tau2, y0, pi) if y[s2] == q0 else 0
            m = (a_ - b_) / GQ.weight(y, list(range(T)), y0, pi)
            C[y[0]] += m * py[y]
        # prediction (zero-based: Ks[k] = transition into period k+1; the block after period p is Ks[p])
        chain = [y0] + list(values[1:]) + [q0]        # y0 -> q_1 -> ... -> q_j -> q0
        heads = [0] + [t + 1 for t in shared]         # Ks[0] (into period 1), then Ks[p+1] after shared period p
        pref = Fraction(1)
        for k, (st, en) in enumerate(zip(chain[:-1], chain[1:])):
            pref *= Ks[heads[k]][st][en]
        rest = [p for p in range(1, T - 1) if p not in shared and p != s2]
        word = [s2] + rest
        M = Ks[word[0] + 1]
        for p in word[1:]:
            M = matmul(M, Ks[p + 1])
        pred = [pref * ((1 if i == q0 else 0) - M[q0][i]) for i in range(Q)]
        assert C == pred, ('mismatch', Q, T, shared, s2, values)
        n_new += 1
    return n_new


def multihead_rank(Q, n, rng):
    A = [[[rng.randint(1, 10 ** 6) for _ in range(Q)] for _ in range(Q)] for _ in range(n)]   # A[t][a][i]
    cols = []
    for j in range(n):
        for H in it.combinations(range(n), j):
            for s in range(n):
                if s in H:
                    continue
                for qH in it.product(range(Q), repeat=j):
                    for q0 in range(Q):
                        cols.append((H, qH, s, q0))
    npts = len(cols) // (Q - 1) + 6
    rows = [[] for _ in cols]
    for _ in range(npts):
        X = [rng.randint(1, P - 1) for _ in range(Q)]
        L = [[sum(A[t][a][i] * X[i] for i in range(Q)) % P for a in range(Q)] for t in range(n)]
        for k, (H, qH, s, q0) in enumerate(cols):
            sc = 1
            for u, qu in zip(H, qH):
                sc = sc * X[qu] % P * pow(L[u][qu], P - 2, P) % P
            sc = sc * X[q0] % P
            invL = pow(L[s][q0], P - 2, P)
            vec = [((1 if i == q0 else 0) - A[s][q0][i] * X[i] % P * invL) % P for i in range(Q)]
            rows[k].extend([sc * vec[i] % P for i in range(Q - 1)])     # zero-sum: drop last component
    return len(cols), flint.nmod_mat(rows, P).rank()


def main():
    rng = random.Random(3)
    for Q, T in [(3, 4), (4, 4), (4, 5), (5, 5)]:
        print(f'Q={Q} T={T}: {check_images(Q, T, rng)} new-column images match the multi-head formula exactly',
              flush=True)
    for Q, n in [(3, 2), (3, 3), (4, 2), (4, 3), (5, 3), (5, 4)]:
        N, rk = multihead_rank(Q, n, rng)
        print(f'canonical multi-head family Q={Q} n={n}: rank {rk}/{N}{"  FULL" if rk == N else "  deficient"}',
              flush=True)


if __name__ == '__main__':
    main()
