#!/usr/bin/env python3
"""Near-identity (persistence) limit G = D + eps H for word families: Lie structure.

eps = l = 10007, exact fmpq matrices, l-adic Smith exponents (hq_fresh_smith).
In this limit K_u = I + eps N_u + ... pointwise, so a word's leading behaviour
is its letter set (abelianisation) and order enters through commutators.

Checks:
 (P1) n = 3, all 216 families with two distinct words per head: Smith sum
      versus two combinatorial counts:
        swaps = #unordered head pairs {t,s} with words (s), s.r for head t and
                (t), t.r for head s, same tail r: then the b-sums of
                F(t,.,s.r) - F(t,.,s) and F(s,.,t.r) - F(s,.,t) differ by
                X_a e_a [K_t, K_s](I - r)  (a commutator);
        same  = #heads whose two words have the same letter set.
 (P2) exact identity  sum_b F(t,a,b,s.R) - sum_b F(s,a,b,t.R)
      = -X_a e_a [K_t, K_s] R  (mod E)  at random rational points.
 (P3) DHW Smith sums in the limit, n = 3, 4 (the defect grows; cf. brief).
"""
import itertools as it
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_lie_common import Q, Ring, dhw_word, family_matrix, words_on  # noqa: E402
from hq_fresh_fast import row_index, kernel_at, matmul, cross, dot  # noqa: E402
from hq_fresh_global_degen import make  # noqa: E402
from hq_fresh_smith import smith_exponents  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402

Rq = Ring(None)
L = 10007


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


def counts(n, wph):
    swaps = 0
    for t, s in it.combinations(range(n), 2):
        if (s,) not in wph[t] or (t,) not in wph[s]:
            continue
        tails_t = {tuple(w[1:]) for w in wph[t] if w[0] == s and len(w) > 1}
        tails_s = {tuple(w[1:]) for w in wph[s] if w[0] == t and len(w) > 1}
        swaps += len(tails_t & tails_s)
    same = sum(1 for t in range(n) if len({frozenset(w) for w in wph[t]}) < len(wph[t]))
    return swaps, same


def p1():
    n = 3
    table = defaultdict(Counter)
    for seed in (5, 6):
        A = make('persist', n, L, random.Random(seed))
        words = {t: words_on([u for u in range(n) if u != t]) for t in range(n)}
        for combo in it.product(*[list(it.combinations(words[t], 2)) for t in range(n)]):
            wph = {t: list(combo[t]) for t in range(n)}
            M, _, _ = family_matrix(A, n, Rq, wph)
            table[counts(n, wph)][sum(smith_exponents(M, L, K=40))] += 1
    print('(P1) n=3, 2 points x 216 families: (swaps, same-set heads) -> {Smith sum: count}')
    for k in sorted(table):
        print(f'      {k}: {dict(table[k])}')


def p2():
    # exact identity: sum_b F(t,a,b,s.R) - sum_b F(s,a,b,t.R) = -X_a e_a [K_t,K_s] R - E_{t,a} + E_{s,a}
    n = 4
    rng = random.Random(3)
    ok = True
    for _ in range(5):
        A = [[[Rq(rng.randint(1, 30)) for _ in range(Q)] for _ in range(Q)] for _ in range(n)]
        X = [Rq(rng.randint(1, 30)) for _ in range(Q)]
        K = [kernel_at(A[u], X, Rq) for u in range(n)]
        t, s = 0, 1
        Rw = matmul(K[2], K[3])
        for a in range(Q):
            lhs = [Rq(0)] * Q
            for b in range(Q):
                for (h, o) in ((t, s), (s, t)):
                    sign = 1 if h == t else -1
                    W = matmul(K[o], Rw)
                    for j in range(Q):
                        lhs[j] += sign * X[a] * K[h][a][b] * ((1 if b == j else 0) - W[b][j])
            KtKs, KsKt = matmul(K[t], K[s]), matmul(K[s], K[t])
            CR = matmul([[KtKs[i][j] - KsKt[i][j] for j in range(Q)] for i in range(Q)], Rw)
            rhs = [-X[a] * CR[a][j] - X[a] * ((1 if a == j else 0) - K[t][a][j])
                   + X[a] * ((1 if a == j else 0) - K[s][a][j]) for j in range(Q)]
            ok &= all(lhs[j] == rhs[j] for j in range(Q))
    print(f'(P2) swap identity sum_b F(t,a,b,s.R) - sum_b F(s,a,b,t.R) = -X_a e_a[K_t,K_s]R - E_ta + E_sa: '
          f'exact at 5 random rational points (n=4, R = K_2 K_3): {ok}')


def p3():
    out = []
    for n in (3, 4):
        t0 = time.time()
        A = make('persist', n, L, random.Random(1000 * n))
        dhw = {t: [dhw_word(t, s, n) for s in range(n) if s != t] for t in range(n)}
        canon = {t: [(s,) for s in range(n) if s != t] for t in range(n)}
        e1 = smith_exponents(family_matrix(A, n, Rq, dhw)[0], L, K=60)
        e0 = smith_exponents(family_matrix(A, n, Rq, canon)[0], L, K=60)
        out.append(f'n={n}: DHW sum {sum(e1)} (max {max(e1)}), canonical sum {sum(e0)} [{time.time() - t0:.0f}s]')
    print('(P3) persistence Smith sums: ' + '; '.join(out))


if __name__ == '__main__':
    p1()
    p2()
    p3()
