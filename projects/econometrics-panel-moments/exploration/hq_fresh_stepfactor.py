#!/usr/bin/env python3
"""Second-level induction probe: does the step factor recurse when the OLDEST block degenerates?

Blocks 0..n (block n newest).  Step factor
    f_n(0..n) := det R_{n+1}(0..n) / ( det Gamma(n | 0..n-1) * det R_n(0..n-1) ),
Gamma(n | old) = prod over old cross points of det K_n(P).  Degenerate block 0 along a
torus weight w (u_0 = c * l^w, eps = l, l-adic exact arithmetic) and compare the
leading l-adic term of f_n with the step factor f_{n-1}(1..n) of the system without
block 0 (block 0 kept out).  Prints v(f_n), v(f_{n-1}) and lead(f_n)/f_{n-1} mod l for
several random positions of the newest block: if the ratio is independent of the
newest block (or simple), the step factors recurse.
What this does not show: a proof; only the ratio's behaviour at sampled points.
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok, kernel_at, cross  # noqa: E402

Q = 3


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def gamma(A, old, new):
    d = flint.fmpq(1)
    lines = [(t, a) for t in old for a in range(Q)]
    for (u, c), (v, e) in it.combinations(lines, 2):
        if u != v:
            d *= det3(kernel_at(A[new], cross(A[u][c], A[v][e]), None))
    return d


def detR(A, idx, R):
    if len(idx) <= 1:
        return flint.fmpq(1)
    B = [A[i] for i in idx]
    return R_matrix(B, len(idx), R).det()


def stepf(A, idx, R):
    old, new = idx[:-1], idx[-1]
    return detR(A, idx, R) / (gamma(A, old, new) * detR(A, old, R))


def vl(x, l):
    num, den = int(x.p), int(x.q)
    v = 0
    while num % l == 0:
        num //= l
        v += 1
    while den % l == 0:
        den //= l
        v -= 1
    return v, num * pow(den, -1, l) % l


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    l = 10007
    R = Ring(None)
    rng = random.Random(21)
    g = [[R(rng.randint(2, l - 1)) for _ in range(Q)] for _ in range(Q)]
    base = [[R(rng.randint(2, l - 1)) for _ in range(Q)] for _ in range(n)]   # blocks 0..n-1
    for w in [(1, 0, 0), (0, 1, 1), (0, 1, 2), (0, 0, 0)]:
        out = []
        for trial in range(3):
            unew = [R(rng.randint(2, l - 1)) for _ in range(Q)]
            us = [row[:] for row in base] + [unew]
            us[0] = [base[0][i] * R(l) ** w[i] for i in range(Q)]
            A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n + 1)]
            if not geometry_ok(A, n + 1):
                out.append('geom')
                continue
            fn = stepf(A, list(range(n + 1)), R)
            fm = stepf(A, list(range(1, n + 1)), R)
            v1, c1 = vl(fn, l)
            v2, c2 = vl(fm, l)
            out.append(f'v(f_n)={v1} v(f_n-1)={v2} lead ratio={c1 * pow(c2, -1, l) % l}')
        print(f'n={n}, oldest block along w={w}: ' + ' | '.join(out), flush=True)


if __name__ == '__main__':
    main()
