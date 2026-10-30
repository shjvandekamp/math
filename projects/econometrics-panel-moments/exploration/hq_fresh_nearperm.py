#!/usr/bin/env python3
"""Near-permutation degenerations g = P_sigma + eps g' (eps = l, l-adic, exact fmpq).

K_t(X) -> P_sigma for every block (deterministic dynamics a -> sigma(a)); sigma = id is the
persistence limit.  Prints the canonical Smith exponents of R_n(eps) and v(det R_n) for
sigma in {3-cycle, reversed 3-cycle, transposition, id}, two random seeds each.
Observed (n = 3, 4, 5): id 30, 63, 117; transposition 18, 29, 65; 3-cycles 12, 0, -21
(negative: canonical coordinates blow up, exponents -1 appear).
What this does not show: a clean limit (the flat limit is deep; see notes sec. 4.12).
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402
from hq_fresh_smith import smith_exponents, summarize  # noqa: E402

Q = 3
L = 10007


def run(n, sigma, seed):
    R = Ring(None)
    rng = random.Random(seed)
    while True:
        g = [[R(1) if i == sigma[a] else R(L) * R(rng.randint(1, 50)) for a in range(Q)] for i in range(Q)]
        us = [[R(rng.randint(1, 50)) for _ in range(Q)] for _ in range(n)]
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        if geometry_ok(A, n):
            break
    e = smith_exponents(R_matrix(A, n, R), L, K=60)
    return summarize(e), sum(e)


def main():
    sig = {'3cyc': (1, 2, 0), '3cyc-rev': (2, 0, 1), 'transp': (1, 0, 2), 'id': (0, 1, 2)}
    for n in [int(x) for x in sys.argv[1:]] or [3, 4, 5]:
        for name, s in sig.items():
            for seed in (1, 2):
                summ, tot = run(n, s, seed)
                print(f'n={n} sigma={name:8s} seed={seed}: Smith {summ}  v(det R_n)={tot}', flush=True)


if __name__ == '__main__':
    main()
