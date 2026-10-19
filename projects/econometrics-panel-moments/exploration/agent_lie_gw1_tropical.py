#!/usr/bin/env python3
"""One-head DHW block D_{t,a} (rows (t,v,a,d), columns (b, w_s), w_s = s.(rest increasing)):
tropical leading terms and signs at positive points.

eps = l = 10007; product-form points g(i,a) = c l^gamma, u_x(i) = c' l^alpha
(c, c' random l-adic units), exact fmpq.
 (Tr1) fraction of random tropical points with v_l(det D) = tropical det (no
       cancellation of the optimal assignment), n = 3, 4, all a;
 (Tr2) points where the FIRST-LETTER assignment (column (b, w_s) -> row (s, b),
       the natural diagonal: empty prefix) is optimal and non-cancelling: none;
 (Sg)  entries of D_{t,a} with a fixed sign across 12 positive points (no
       naive total positivity).
What this does not show: anything uniform in n.
"""
import random
import sys
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.optimize import linear_sum_assignment

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_lie_common import Q, Ring, dhw_word, gw1_matrix, random_point, words_on  # noqa: E402
from hq_fresh_fast import geometry_ok  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402

Rq = Ring(None)
L = 10007
E = Rq(L)


def val(x):
    if x == 0:
        return None
    num, den, v = abs(int(x.p)), int(x.q), 0
    while num % L == 0:
        num //= L
        v += 1
    while den % L == 0:
        den //= L
        v -= 1
    return v


def lp(k):
    return E ** k if k >= 0 else Rq(1) / E ** (-k)


def point(n, alpha, gamma, rng):
    for _ in range(50):
        g = [[Rq(rng.randint(1, L - 1)) * lp(gamma[i][a]) for a in range(Q)] for i in range(Q)]
        us = [[Rq(rng.randint(1, L - 1)) * lp(alpha[x][i]) for i in range(Q)] for x in range(n)]
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        if geometry_ok(A, n):
            return A
    return None


def cost(D):
    N = D.nrows()
    C = np.full((N, N), 10 ** 6)
    for i in range(N):
        for j in range(N):
            v = val(D[i, j])
            if v is not None:
                C[i, j] = v
    r, c = linear_sum_assignment(C)
    return C, C[r, c].sum()


def main():
    rng = random.Random(2)
    for n, ntr in ((3, 150), (4, 120)):
        t = 0
        S = [u for u in range(n) if u != t]
        dhw = [dhw_word(t, s, n) for s in S]
        rowpos = {(v, d): i for i, (v, d) in enumerate((v, d) for v in S for d in range(Q))}
        diag = [rowpos[(w[0], b)] for b in range(Q) for w in dhw]
        st = Counter()
        for _ in range(ntr):
            alpha = [[rng.choice([0, 1, -1, 2, -2]) for _ in range(Q)] for _ in range(n)]
            gamma = [[rng.choice([0, 0, 1, -1]) for _ in range(Q)] for _ in range(Q)]
            A = point(n, alpha, gamma, rng)
            if A is None:
                continue
            nocancel = firstletter = True
            for a in range(Q):
                D = gw1_matrix(A, n, Rq, t, a, dhw)
                C, td = cost(D)
                vd = val(D.det())
                nocancel &= vd == td
                firstletter &= vd == td == sum(C[diag[j], j] for j in range(len(diag)))
            st[('no-cancel', nocancel, 'first-letter-optimal', firstletter)] += 1
        print(f'(Tr) n={n}: {dict(st)}')
    n, t = 4, 0
    S = [1, 2, 3]
    words = words_on(S)
    sig = {}
    for seed in range(12):
        A = random_point(n, Rq, 3000 + seed, lo=1, hi=30)
        for a in range(Q):
            cols = [(t, a, b, [(1, list(w))]) for w in words for b in range(Q)]
            rows = build_cols(A, n, Rq, cols)
            for v in S:
                for d in range(Q):
                    for j in range(len(cols)):
                        x = rows[(t, v, a, d)][j]
                        sig.setdefault((a, v, d, j), set()).add(0 if x == 0 else (1 if x > 0 else -1))
    print(f'(Sg) n=4: entries of D_(0,a) (all words) with a fixed sign over 12 positive points: '
          f'{sum(1 for s in sig.values() if len(s) == 1)}/{len(sig)} (structural zeros included)')


if __name__ == '__main__':
    main()
