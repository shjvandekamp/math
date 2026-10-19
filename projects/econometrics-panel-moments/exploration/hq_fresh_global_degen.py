#!/usr/bin/env python3
"""Smith exponents of R_n(eps) along global one-parameter degenerations.

epsilon = l (prime); exact R_n over Q (fmpq); l-adic Smith exponents via
hq_fresh_smith.  All points lie in the product-form family
A_t(a,i) = g(i,a) u_t(i) (Zariski closure of the economic family).

Degenerations (name -> g(eps), u_t(eps)):
  weakdep : G = J + eps H        (state dependence -> 0)
  persist : G = I + eps H        (strong persistence)
  stair1  : u_t = c_t * eps^{t * (0,1,2)}  (economic subgroup, x_t = t)
  stair2  : u_t = c_t * eps^{2^t * (0,1,2)} (rapidly separated x_t)
  vert    : block t concurrent at vertex t mod 3 (u_t(t mod 3) = eps c)
What this does not show: anything beyond the n computed.
"""
import argparse
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402
from hq_fresh_smith import smith_exponents, summarize  # noqa: E402

Q = 3


def make(name, n, l, rng):
    Rq = Ring(None)
    E = Rq(l)

    def unit():
        return Rq(rng.randint(1, l - 1))
    for _ in range(100):
        if name == 'weakdep':
            ci = [unit() for _ in range(Q)]
            g = [[ci[i] + E * unit() for _ in range(Q)] for i in range(Q)]
            us = [[unit() for _ in range(Q)] for _ in range(n)]
        elif name == 'persist':
            g = [[(unit() if i == a else Rq(0)) + E * unit() for a in range(Q)] for i in range(Q)]
            us = [[unit() for _ in range(Q)] for _ in range(n)]
        elif name in ('stair1', 'stair2'):
            g = [[unit() for _ in range(Q)] for _ in range(Q)]
            xs = [t + 1 for t in range(n)] if name == 'stair1' else [2 ** t for t in range(n)]
            us = [[unit() * E ** (xs[t] * i) for i in range(Q)] for t in range(n)]
        elif name == 'vert':
            g = [[unit() for _ in range(Q)] for _ in range(Q)]
            us = [[unit() * (E if i == t % Q else Rq(1)) for i in range(Q)] for t in range(n)]
        else:
            raise ValueError(name)
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        if geometry_ok(A, n):
            return A
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4])
    ap.add_argument('--kinds', nargs='+', default=['weakdep', 'persist', 'stair1', 'stair2', 'vert'])
    ap.add_argument('--l', type=int, default=10007)
    ap.add_argument('--K', type=int, default=80)
    args = ap.parse_args()
    for kind in args.kinds:
        for n in args.n:
            t0 = time.time()
            rng = random.Random(1000 * n + hash(kind) % 997)
            A = make(kind, n, args.l, rng)
            if A is None:
                print(f'{kind} n={n}: no admissible point')
                continue
            M = R_matrix(A, n, Ring(None))
            e = smith_exponents(M, args.l, K=args.K)
            print(f'{kind:8s} n={n}: Smith {summarize(e)}  sum={sum(e)}  [{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
