#!/usr/bin/env python3
"""Rank of the raw equation-(24) family at finite degenerate tables.

Goal: find the most degenerate parameter points (inside or near the economic
family pi_t(q,r) = g(q,r) u_t(q)) at which the family keeps full rank.  Full
modular rank at a rational point proves full real rank there, hence generic
independence on every family containing that point.  A rank drop proves
nothing about generic independence; it only marks the point as unusable.

Standard library only; reuses hq_fresh_special_points.family_rank.
"""
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_special_points import family_rank, dimension  # noqa: E402

Q = 3


def table(g, us):
    """pi[t][q][r] = g[q][r] * us[t][q]."""
    T = len(us)
    return [[[Fraction(g[q][r]) * Fraction(us[t][q]) for r in range(Q)] for q in range(Q)] for t in range(T)]


def main():
    Ts = [int(a) for a in sys.argv[1:]] or [4, 5]
    rng = random.Random(2024)
    for T in Ts:
        us = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(T)]
        us_econ = [[Fraction(w) ** (t + 1) for w in (1, 2, 5)] for t in range(T)]
        cases = []
        g_gen = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(Q)]
        cases.append(('generic G, generic u', g_gen, us))
        # two equal columns of G: lines L_{t1} = L_{t2} in every block (economic)
        g = [[row[0], row[1], row[1]] for row in g_gen]
        cases.append(('G cols 1=2 (coincident lines per block)', g, us))
        # two equal rows of G: concurrent lines per block (economic)
        g = [g_gen[0], g_gen[1], g_gen[1]]
        cases.append(('G rows 1=2 (concurrent lines per block)', g, us))
        # G with a zero: no transition into state 2 from state 0 etc.
        g = [row[:] for row in g_gen]
        g[2][0] = 0
        cases.append(('G[2][0]=0 (one zero)', g, us))
        g = [[g_gen[q][r] if q >= r else 0 for r in range(Q)] for q in range(Q)]
        cases.append(('G lower triangular', g, us))
        g = [[g_gen[q][r] if q <= r else 0 for r in range(Q)] for q in range(Q)]
        cases.append(('G upper triangular', g, us))
        g = [[1 if q == r else 0 for r in range(Q)] for q in range(Q)]
        g = [[g[q][r] + 0 for r in range(Q)] for q in range(Q)]
        cases.append(('G = identity (deterministic stay)', g, us))
        g = [[2 if q == r else 1 for r in range(Q)] for q in range(Q)]
        cases.append(('G = J + I', g, us))
        g = [[1, 1, 1], [1, 2, 4], [1, 4, 17]]
        cases.append(('project witness G, u = (1,2,5)^(t+1)', g, us_econ))
        cases.append(('project witness G, generic u', g, us))
        g = [[1, 1, 1], [1, 2, 4], [1, 4, 16]]
        cases.append(('conic G (Vandermonde), generic u', g, us))
        # u degenerate: two periods with equal u (economic x_t = x_s)
        us2 = [row[:] for row in us]
        us2[T - 1] = us2[T - 2][:]
        cases.append(('generic G, u_{T-1} = u_{T-2}', g_gen, us2))
        us3 = [row[:] for row in us]
        us3[1] = us3[0][:]
        cases.append(('generic G, u_1 = u_0', g_gen, us3))
        # u with a zero coordinate: state q impossible at period t
        us4 = [row[:] for row in us]
        us4[T - 1][2] = 0
        cases.append(('generic G, u_{T-1}(2) = 0', g_gen, us4))
        # last block only: rank-2 table (pi_T(.,1) = pi_T(.,2)), outside economic family
        print(f'T={T}, family size {dimension(T)}')
        for name, g, u in cases:
            pi = table(g, u)
            cnt, rk = family_rank(T, pi)
            print(f'  {name:48s}: rank {rk}/{cnt}{"  FULL" if rk == cnt else ""}')
            sys.stdout.flush()
        pi = table(g_gen, us)
        for r in range(Q):
            for q in range(Q):
                pi[T - 1][q][2] = pi[T - 1][q][1]
        cnt, rk = family_rank(T, pi)
        print(f'  {"last period only: pi_T(.,1)=pi_T(.,2)":48s}: rank {rk}/{cnt}{"  FULL" if rk == cnt else ""}')
        pi = table(g_gen, us)
        for q in range(Q):
            pi[1][q][2] = pi[1][q][1]
        cnt, rk = family_rank(T, pi)
        print(f'  {"period 2 only: pi_2(.,1)=pi_2(.,2)":48s}: rank {rk}/{cnt}{"  FULL" if rk == cnt else ""}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
