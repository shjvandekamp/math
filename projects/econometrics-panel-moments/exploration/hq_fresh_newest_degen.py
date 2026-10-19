#!/usr/bin/env python3
"""Route 1 probe: degenerate only the newest block along a torus weight.

Old blocks 0..n-1: product form A_t(a,i) = g(i,a) u_t(i) with random
integer data (l-adic units).  Newest block n: u_n(i) = c_i * l^{w_i}, so
epsilon = l (a prime) and the weight w is the tropical direction.  All
arithmetic is exact (fmpq); the l-adic valuation of an exact determinant
equals the epsilon-valuation of the generic Laurent expansion unless its
leading coefficient happens to vanish mod l (probability ~ degree / l;
two primes are used).

Printed for each weight w:
  v(det R_{n+1}), v(det Gamma), v(f) with f = det R_{n+1}/(det Gamma det R_n),
  and the leading coefficient of f mod l.
What this does not show: anything for n beyond those run.
"""
import argparse
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok, kernel_at, cross  # noqa: E402

Q = 3


def vl(x, l):
    """l-adic valuation of a nonzero fmpq."""
    num, den = int(x.p), int(x.q)
    v = 0
    while num % l == 0:
        num //= l
        v += 1
    while den % l == 0:
        den //= l
        v -= 1
    return v, num, den


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def det_gamma(A, n_old):
    """prod over old unordered cross pairs of det K_new(P) (= det of x -> xK on the zero-sum plane)."""
    d = flint.fmpq(1)
    for (u, c), (v, e) in it.combinations([(t, a) for t in range(n_old) for a in range(Q)], 2):
        if u == v:
            continue
        P = cross(A[u][c], A[v][e])
        d *= det3(kernel_at(A[n_old], P, None))
    return d


def setup(n, l, w, rng):
    Rq = Ring(None)
    while True:
        g = [[rng.randint(1, l - 1) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randint(1, l - 1) for _ in range(Q)] for _ in range(n)]
        cnew = [rng.randint(1, l - 1) for _ in range(Q)]
        unew = [Rq(cnew[i]) * Rq(l) ** w[i] if w[i] >= 0 else Rq(cnew[i]) / Rq(l) ** (-w[i]) for i in range(Q)]
        A = [[[Rq(g[i][a]) * Rq(us[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
        A.append([[Rq(g[i][a]) * unew[i] for i in range(Q)] for a in range(Q)])
        if geometry_ok(A, n + 1):
            return A


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[2, 3])
    ap.add_argument('--primes', type=int, nargs='+', default=[1009, 10007])
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    weights = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0),
               (0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0), (0, 1, 3), (0, 3, 1)]
    for n in args.n:
        print(f'old blocks n={n}  (R_{n + 1} is {9 * (n + 1) * n}x{9 * (n + 1) * n}, Schur factor size {18 * n})')
        for w in weights:
            out = []
            for l in args.primes:
                rng = random.Random(args.seed * 7919 + n * 31 + l)
                A = setup(n, l, w, rng)
                Rq = Ring(None)
                dn1 = R_matrix(A, n + 1, Rq).det()
                dn = R_matrix(A[:n], n, Rq).det()
                dg = det_gamma(A, n)
                if dn1 == 0:
                    out.append(f'l={l}: det R_{n + 1} = 0 exactly')
                    continue
                v1, _, _ = vl(dn1, l)
                vg, _, _ = vl(dg, l)
                vn, _, _ = vl(dn, l)
                f = dn1 / (dg * dn)
                vf, num, den = vl(f, l)
                lead = num * pow(den, -1, l) % l
                out.append(f'l={l}: v(detR)={v1} v(Gamma)={vg} v(detRold)={vn} v(f)={vf} lead(f)={lead}')
            print(f'  w={w}: ' + ' | '.join(out))
            sys.stdout.flush()


if __name__ == '__main__':
    main()
