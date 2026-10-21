#!/usr/bin/env python3
"""agent_col task 3(b): iterated (simultaneous) non-adjacent collisions.

Configurations (n blocks 0..N, N = n-1), all collisions at the same rate delta with independent random nu's:
  nested2  : u_N -> u_0, u_{N-1} -> u_1                 (0,1,...,N-2,1',0')
  crossing2: u_N -> u_1, u_{N-1} -> u_0                 (0,1,...,N-2,0',1')
  nested3  : u_N -> u_0, u_{N-1} -> u_1, u_{N-2} -> u_2
  gapped2  : u_N -> u_0, u_{N-2} -> u_1
  palin    : full palindrome u_{N-j} -> u_j for all j < N-j
Prints the Smith exponents (over F_p[[delta]], Toeplitz ranks, exact mod p = 2^61-1) of the E/F family
evaluation matrix and the number of family pairs that coincide at delta = 0 (computed by comparing the
delta = 0 vectors at random points).
What this does not show: anything beyond the printed n; proofs.
"""
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, multi_collision_config, eval_jets, family_series, rand_points,  # noqa: E402
                           smith_counts)


def configs(n):
    N = n - 1
    out = {}
    out['single'] = {N: 0}
    if n >= 6:
        out['nested2'] = {N: 0, N - 1: 1}
        out['crossing2'] = {N: 1, N - 1: 0}
        out['gapped2'] = {N: 0, N - 2: 1}
    if n >= 8:
        out['nested3'] = {N: 0, N - 1: 1, N - 2: 2}
    pal = {N - j: j for j in range(n) if j < N - j}
    if len(pal) >= 2 and n >= 6:
        out['palin'] = pal
    return out


def coincidences(Ms0):
    """number of family members equal to an earlier one at delta = 0 (columns compared exactly)."""
    seen = {}
    dup = 0
    for r in Ms0:
        key = tuple(r)
        if key in seen:
            dup += 1
        else:
            seen[key] = 1
    return dup


def main(ns, K=3):
    for n in ns:
        for name, coll in configs(n).items():
            rng = random.Random(31 * n + len(name))
            pairs = {j: (k, [rng.randrange(1, P) for _ in range(Q)]) for j, k in coll.items()}
            t0 = time.time()
            A, _ = multi_collision_config(n, pairs, rng, K)
            nfam = 3 * n * (3 * n - 2)
            pts = rand_points(A, nfam // 2 + 6, rng, K)
            Ms = eval_jets(lambda kers, X: family_series(kers, X, n, K), A, pts, K)
            counts, _ = smith_counts(Ms)
            dup = coincidences(Ms[0])
            print(f'n={n} {name:9s} {coll}: Smith {counts}; equal pairs at delta=0: {dup}; '
                  f'12 x #collisions = {12 * len(coll)}  [{time.time() - t0:.1f}s]', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [6, 7, 8])
