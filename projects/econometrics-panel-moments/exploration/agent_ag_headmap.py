#!/usr/bin/env python3
"""agent_ag: is the head map Lambda_n intrinsic / local?  (exact mod p = 2^61-1, random product points)

T1  Lambda_n(h_tab (I - W)) for every word W on [n]-t: unit vector e_tab iff W is a DHW word.
T2  rank of Lambda_n on W_{[n]-t} (vectors without poles on block t's lines).
T3  residues along a line L_uc: rank on ker Lambda_n vs on W_n (6n-5); generic and special points
    (economic geometric u_t = (1,2,5)^(t+1), conic (1,s,s^2), Moebius u_{t+1} = tau u_t/(1+z u_t)).
T4  newest-vertex limit (u_N(0) -> 0, K0_N never enters state 0): V0 = {w : rho_P(w) K0_N(P) = 0 at all
    old cross points}; prints dim V0, rank Lambda|V0, dim(V0 cap ker Lambda) (= 3n + 9n(n-3)/2?),
    and whether Lambda|V0 lies in the span of the residues of w along L_ta at P0_tab = L_ta cap L0_Nb.
What this does not show: anything for n beyond those printed; other specialisations.
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_ag_lib import (P, Q, Basis, inv, product_config, family, head_map_matrix, nullspace,  # noqa: E402
                          combine, point_on_line, residue_vec, double_residue_vec, cross_points, cross3,
                          dhw_word)


def identity(d):
    return flint.nmod_mat([[1 if i == j else 0 for j in range(d)] for i in range(d)], P)


def setup(n, rng, us=None):
    A, g, uu = product_config(n, rng, us=us)
    labs, specs = family(n)
    B = Basis(A, specs, rng)
    return A, g, labs, specs, B


def t1(rng):
    for n in (3, 4):
        A, g, labs, specs, B = setup(n, rng)
        t, a, b = 0, 1, 2
        others = [u for u in range(n) if u != t]
        words = [list(p) for k in range(1, n) for p in it.permutations(others, k)]
        C = B.coords([[(1, a, [(t, b)], b, w)] for w in words])
        heads, L = head_map_matrix(labs, C, n)
        hi = heads.index((t, a, b))
        dhw = {tuple(dhw_word(t, s, list(range(n)))) for s in others}
        unit = [tuple(w) for j, w in enumerate(words)
                if all(int(L[i, j]) == (1 if i == hi else 0) for i in range(L.nrows()))]
        print(f'T1 n={n}: words with Lambda = unit: {len(unit)}/{len(words)}; equal to the DHW words: {set(unit) == dhw}')


def t2(rng):
    for n in (3, 4, 5):
        A, g, labs, specs, B = setup(n, rng)
        rks = []
        for t in range(n):
            sub = [u for u in range(n) if u != t]
            _, sspecs = family(n - 1, blocks=sub)
            _, L = head_map_matrix(labs, B.coords(sspecs), n)
            rks.append(L.rank())
        print(f'T2 n={n}: rank Lambda_n on W_[n]-t for t=0..n-1: {rks} (9n={9 * n})')


def special_us(kind, n, rng):
    if kind == 'econ-geom':
        return [[pow(w, t + 1, P) for w in (1, 2, 5)] for t in range(n)]
    if kind == 'conic':
        return [[1, s, s * s % P] for s in (rng.randrange(2, 10 ** 6) for _ in range(n))]
    if kind == 'mobius':
        tau = [rng.randrange(2, 100) for _ in range(Q)]
        z = [rng.randrange(2, 100) for _ in range(Q)]
        u = [rng.randrange(2, 100) for _ in range(Q)]
        out = []
        for _ in range(n):
            out.append(u[:])
            u = [tau[i] * u[i] % P * inv(1 + z[i] * u[i]) % P for i in range(Q)]
        return out
    return None


def t3(rng):
    for n, kind in [(3, 'generic'), (4, 'generic'), (5, 'generic'), (3, 'econ-geom'), (4, 'econ-geom'),
                    (4, 'conic'), (4, 'mobius')]:
        A, g, labs, specs, B = setup(n, rng, us=special_us(kind, n, rng))
        d = len(specs)
        _, L = head_map_matrix(labs, identity(d), n)
        kvecs = [combine(specs, v) for v in nullspace(L)]
        mins = []
        for (u, c) in [(t, a) for t in range(n) for a in range(Q)]:
            pts = [point_on_line(A, u, c, rng) for _ in range(6 * n + 4)]
            rows = []
            for X in pts:
                vals = [residue_vec(A, v, u, c, X) for v in kvecs]
                rows += [[vv[j] for vv in vals] for j in range(Q)]
            mins.append(flint.nmod_mat(rows, P).rank())
        print(f'T3 n={n} {kind:9s}: residue rank of ker Lambda along the 3n lines: min {min(mins)}, max {max(mins)} '
              f'(rank on W_n = 6n-5 = {6 * n - 5})')


def t4(rng):
    for n in (3, 4):
        A, g, labs, specs, B = setup(n, rng)
        cN = [rng.randrange(1, 10 ** 6) for _ in range(Q)]
        d = len(specs)
        rows = []
        for (u, c), (v, dd) in cross_points(n):
            vals = []
            for sp in specs:
                X, rho = double_residue_vec(A, sp, u, c, v, dd)
                s = 0
                for a in range(Q):
                    la = (g[1][a] * cN[1] * X[1] + g[2][a] * cN[2] * X[2]) % P
                    s = (s + rho[a] * g[1][a] * cN[1] % P * X[1] % P * inv(la)) % P
                vals.append(s)
            rows.append(vals)
        V0 = nullspace(flint.nmod_mat(rows, P))
        V0m = flint.nmod_mat([[V0[k][i] for k in range(len(V0))] for i in range(d)], P)
        heads, L = head_map_matrix(labs, identity(d), n)
        LV = L * V0m
        Y = []
        for (t, a, b) in heads:
            X = cross3(A[t][a], [0, g[1][b] * cN[1] % P, g[2][b] * cN[2] % P])
            vals = [residue_vec(A, sp, t, a, X) for sp in specs]
            Y += [[vv[0] for vv in vals], [vv[1] for vv in vals]]
        YV = flint.nmod_mat(Y, P) * V0m
        both = flint.nmod_mat([[int(M[i, j]) for j in range(M.ncols())] for M in (YV, LV) for i in range(M.nrows())], P)
        print(f'T4 n={n}: dim V0={len(V0)}, rank Lambda|V0={LV.rank()}, dim(V0 cap ker Lambda)={len(V0) - LV.rank()} '
              f'(3n+9n(n-3)/2={3 * n + 9 * n * (n - 3) // 2}); residues at P0: rank {YV.rank()}, '
              f'with Lambda {both.rank()} (Lambda|V0 in their span: {both.rank() == YV.rank()})')


if __name__ == '__main__':
    rng = random.Random(2026)
    t1(rng)
    t2(rng)
    t3(rng)
    t4(rng)
