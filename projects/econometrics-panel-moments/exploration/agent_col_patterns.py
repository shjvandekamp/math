#!/usr/bin/env python3
"""agent_col task 3(b): how general is the 'clean collision' property?

For a collision pattern {j: k} (u_j = u_k (1 + delta nu_j), all at rate delta, independent random nu_j),
compare the Smith exponents (over F_p[[delta]], exact mod p = 2^61-1, Toeplitz ranks) of the E/F family
evaluation matrix with the number of family pairs that coincide at delta = 0.
'Clean' = exponents only 0, 1 and #(exponent 1) = #(coinciding pairs)  [equivalently: at delta = 0 the
distinct family members are independent, and the jets of the coincidences are independent modulo them].
Patterns: period-p foldings u_t -> u_{t mod p} (t >= p), single collisions u_N -> u_k, nested/palindromes.
What this does not show: anything beyond the printed n and patterns; proofs.
"""
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, multi_collision_config, eval_jets, family_series, rand_points,  # noqa: E402
                           smith_counts)
from agent_col_iterated import coincidences  # noqa: E402


def run(n, coll, seed, K=3):
    rng = random.Random(seed)
    pairs = {j: (k, [rng.randrange(1, P) for _ in range(Q)]) for j, k in coll.items()}
    A, _ = multi_collision_config(n, pairs, rng, K)
    nfam = 3 * n * (3 * n - 2)
    pts = rand_points(A, nfam // 2 + 6, rng, K)
    Ms = eval_jets(lambda kers, X: family_series(kers, X, n, K), A, pts, K)
    counts, _ = smith_counts(Ms)
    return counts, coincidences(Ms[0])


def patterns(n):
    N = n - 1
    out = []
    for p in (3, 4, 5):
        if n > p:
            out.append((f'period{p}', {t: t % p for t in range(p, n)}))
    for k in range(N):
        out.append((f'single N->{k}', {N: k}))
    out.append(('palindrome', {N - j: j for j in range(n) if j < N - j}))
    return out


if __name__ == '__main__':
    ns = [int(x) for x in sys.argv[1:]] or [5, 6, 7]
    for n in ns:
        for name, coll in patterns(n):
            t0 = time.time()
            counts, dup = run(n, coll, 1000 * n + len(coll))
            clean = (counts.get(2, 0) == 0 and counts['>2'] == 0 and counts[1] == dup)
            print(f'n={n} {name:13s}: Smith {counts}; coinciding pairs {dup}; clean: {clean}  '
                  f'[{time.time() - t0:.1f}s]', flush=True)
