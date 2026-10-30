#!/usr/bin/env python3
"""Exact check, any Q: conditional-sum images of the new equation-(24) columns.

For a source moment m (raw DHW form, zero-based periods, initial outcome y0) and
X = eta (fixed effects, homogeneous), C_i(m)(X) := sum_{y : y_1 = i} m(y) p_y(X)
(p_y = prod_t K_t(X)(y_{t-1}, y_t), K_t(a,i) = pi_t(i,a) X_i / sum_j pi_t(j,a) X_j).
Claim (used for every Q, derived by telescoping the transformed chain):
  j = 1, shared period t >= 2 (one-based), first-differing period s:
      C(m) = K_1(y0,a) K_t(a,b) e_b (I - K_s P)      (P = remaining kernels, increasing)
  j = 0, s2 = s:
      C(m) = K_1(y0,a) e_a (I - K_s P)
where K_u is the transition following period u (one-based), a = q_1 (shared
value) or q_0, b = q_0.  Checked exactly (Fraction) at random rational points for
Q = 3, 4 and T = 4, 5 by brute-force path sums.  What this does not show: rank.
"""
import itertools as it
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hq_fresh_generalQ as GQ  # noqa: E402


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


def check(Q, T, rng):
    pi = [[[Fraction(rng.randint(1, 9)) for _ in range(Q)] for _ in range(Q)] for _ in range(T)]
    X = [Fraction(rng.randint(1, 9)) for _ in range(Q)]
    y0 = 0
    Ks = kernels(pi, X, Q, T)          # Ks[t] = transition into period t+1 (zero-based t)
    paths = list(it.product(range(Q), repeat=T))
    py = {}
    for y in paths:
        w = Fraction(1)
        prev = y0
        for t in range(T):
            w *= Ks[t][prev][y[t]]
            prev = y[t]
        py[y] = w
    nchk = 0
    for shared, s1, s2, values, tau1, tau2 in GQ.source_indices(Q, T):
        if 0 in shared:          # lifted column (shared set contains period 1)
            continue
        if len(shared) > 1:
            continue             # (only j <= 1 are new for these (Q, T) checked)
        q = values[0]
        C = [Fraction(0)] * Q
        for y in paths:
            if any(y[t] != v for t, v in zip(shared, values[1:])):
                continue
            a_ = GQ.weight(y, tau1, y0, pi) if y[s1] == q else 0
            b_ = GQ.weight(y, tau2, y0, pi) if y[s2] == q else 0
            m = (a_ - b_) / (Fraction(1) * GQ.weight(y, list(range(T)), y0, pi))
            C[y[0]] += m * py[y]
        # predicted (zero-based: Ks[k] is the transition into period k; the block
        # following period u is Ks[u+1]; quotient blocks are Ks[2..T-1])
        blocks = list(range(2, T))
        s = s2 + 1
        if len(shared) == 1:
            head = shared[0] + 1
            a, b = values[1], q
            word = [s] + [u for u in blocks if u not in (s, head)]
            M = Ks[word[0]]
            for u in word[1:]:
                M = matmul(M, Ks[u])
            pref = Ks[0][y0][a] * Ks[head][a][b]
            pred = [pref * ((1 if i == b else 0) - M[b][i]) for i in range(Q)]
        else:
            a = q
            word = [s] + [u for u in blocks if u != s]
            M = Ks[word[0]]
            for u in word[1:]:
                M = matmul(M, Ks[u])
            pref = Ks[0][y0][a]
            pred = [pref * ((1 if i == a else 0) - M[a][i]) for i in range(Q)]
        assert C == pred, ('mismatch', Q, T, shared, s1, s2, values, C, pred)
        nchk += 1
    return nchk


def main():
    rng = random.Random(1)
    for Q, T in [(3, 4), (4, 4), (3, 5), (4, 5)]:
        n = check(Q, T, rng)
        print(f'Q={Q} T={T}: {n} new-column conditional-sum images match the E/F formulas exactly')


if __name__ == '__main__':
    main()
