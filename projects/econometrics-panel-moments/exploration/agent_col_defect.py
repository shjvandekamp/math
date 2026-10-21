#!/usr/bin/env python3
"""agent_col task 1: intrinsic Smith exponents of the E/F family at the collision u_N = u_k (1 + delta nu).

For n blocks (N = n-1 newest) and a target block k, blocks 0..N-1 and nu, g are random mod
p = 2^61-1, u_N = u_k (1 + delta nu).  The family {E} u {F} (3n(3n-2) vectors) is evaluated at
#fam/2 + 6 random points with exact jets in delta (agent_col_lib), and the Smith exponents over
F_p[[delta]] are read off from the ranks of block-Toeplitz matrices (exponents 0, 1, 2, >2).
Also prints the predicted number of coinciding family pairs at delta = 0:
   k <= N-3: 12 (F_{N,k} = F_{k,N}: 9, E_{N,a} = E_{k,a}: 3); k = N-2: 30; k = N-1: 18n-24.

Usage: agent_col_defect.py [--n 4 5 6 7 8] [--seeds 1 2] [--ks all|0,1,..] [--K 3] [--extra 6]
What this checks: the exponent multiset at single random points (exact mod p; a full Toeplitz rank
certifies the exponents at that point, generic-point statements are evidence only).
What it does not show: anything for n beyond those run; that the counts are the same at every point.
"""
import argparse
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (collision_config, eval_jets, family_series, rand_points,  # noqa: E402
                           smith_counts)


def predicted(n, k):
    N = n - 1
    if k == N - 1:
        return 18 * n - 24
    if k == N - 2:
        return 30
    return 12


def run(n, k, seed, K=3, extra=6):
    rng = random.Random(1000 * seed + 37 * n + k)
    A, info = collision_config(n, k, rng, K)
    nfam = 3 * n * (3 * n - 2)
    pts = rand_points(A, nfam // 2 + extra, rng, K)
    Ms = eval_jets(lambda kers, X: family_series(kers, X, n, K), A, pts, K)
    counts, ranks = smith_counts(Ms)
    return counts, ranks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[4, 5, 6, 7, 8])
    ap.add_argument('--seeds', type=int, nargs='+', default=[1, 2])
    ap.add_argument('--ks', default='oldest_and_far', help="'all', 'oldest_and_far' or comma list")
    ap.add_argument('--K', type=int, default=3)
    ap.add_argument('--extra', type=int, default=6)
    args = ap.parse_args()
    for n in args.n:
        N = n - 1
        if args.ks == 'all':
            ks = list(range(N))
        elif args.ks == 'oldest_and_far':
            ks = sorted(set([0] + [kk for kk in (1, N - 3) if 0 <= kk <= N - 3]))
        else:
            ks = [int(x) for x in args.ks.split(',')]
        for k in ks:
            for seed in args.seeds:
                t0 = time.time()
                counts, ranks = run(n, k, seed, args.K, args.extra)
                print(f'n={n} k={k} seed={seed}: Smith exponents {counts}  (#fam={3 * n * (3 * n - 2)}, '
                      f'coinciding pairs predicted {predicted(n, k)})  [{time.time() - t0:.1f}s]', flush=True)


if __name__ == '__main__':
    main()
