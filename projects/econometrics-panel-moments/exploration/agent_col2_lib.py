#!/usr/bin/env python3
"""agent_col2_lib: polynomial numerators and local jet conditions for the delta = 0 space S_0.

Setting (research/AGENT_COL_NOTES.md): m distinct blocks, block 0 doubled (time slots 0, 1, ..., m-1, 0' or any
other middle order), n = m+1 slots.  A vector f in S_0 has double poles at most on the lines L_0c and simple
poles on the lines of blocks t >= 1; with D_lim = D_0^2 prod_{t>=1} D_t (degree 3n), D_lim f = (X_i g_i)_i
with g_i homogeneous of degree d = 3n and sum_i X_i g_i = 0.

This module provides (all exact mod p = 2^61-1):
 * monomial bases, evaluation and interpolation of homogeneous polynomials in X0, X1, X2;
 * numerators(A, vecs, mults): the g-coefficient vectors of term-list vectors (agent_col_lib conventions) by
   interpolation of D_lim * f at #monomials random points (with an independent check point);
 * Taylor functionals: coefficient of eps^k in g_i(z + eps*Y) as a linear functional on g-coefficients;
 * base points of a block and the syzygy equations sum_i X_i g_i = 0.
Self-test: E and B vectors of a generic 2-block system satisfy the usual W_n base conditions; the numerator
reconstruction reproduces the values at an extra point.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, kernels_series, term_vec, WordCache, make_A, s_const)  # noqa: E402


# ------------------------------------------------------------------ monomials
_MON = {}


def monomials(d):
    if d not in _MON:
        mons = [(a, b, d - a - b) for a in range(d, -1, -1) for b in range(d - a, -1, -1)]
        _MON[d] = (mons, {mo: i for i, mo in enumerate(mons)})
    return _MON[d]


def powers(x, d):
    out = [1] * (d + 1)
    for k in range(1, d + 1):
        out[k] = out[k - 1] * x % P
    return out


def eval_monomials(d, X):
    mons, _ = monomials(d)
    p0, p1, p2 = powers(X[0], d), powers(X[1], d), powers(X[2], d)
    return [p0[a] * p1[b] % P * p2[c] % P for (a, b, c) in mons]


def series_powers(z, y, d, K):
    """(z + eps y)^k as truncated series of length K, k = 0..d."""
    out = [[1] + [0] * (K - 1)]
    base = [z % P, y % P] + [0] * (K - 2)
    for k in range(1, d + 1):
        prev = out[-1]
        new = [0] * K
        for i in range(K):
            if prev[i]:
                new[i] = (new[i] + prev[i] * base[0]) % P
                if i + 1 < K:
                    new[i + 1] = (new[i + 1] + prev[i] * base[1]) % P
        out.append(new)
    return out


def taylor_rows(d, z, Y, K):
    """For each monomial of degree d: coefficients of eps^0..eps^{K-1} of mono(z + eps Y). Returns K lists."""
    mons, _ = monomials(d)
    sp = [series_powers(z[j], Y[j], d, K) for j in range(Q)]
    rows = [[0] * len(mons) for _ in range(K)]
    for idx, (a, b, c) in enumerate(mons):
        s0, s1, s2 = sp[0][a], sp[1][b], sp[2][c]
        # product of three length-K series
        t = [0] * K
        for i in range(K):
            if s0[i]:
                for j in range(K - i):
                    if s1[j]:
                        t[i + j] = (t[i + j] + s0[i] * s1[j]) % P
        u = [0] * K
        for i in range(K):
            if t[i]:
                for j in range(K - i):
                    if s2[j]:
                        u[i + j] = (u[i + j] + t[i] * s2[j]) % P
        for k in range(K):
            rows[k][idx] = u[k]
    return rows


def g_functional(d, comp, row):
    """Embed a functional on one component (list over monomials) into the 3-component g space."""
    nm = len(monomials(d)[0])
    out = [0] * (3 * nm)
    out[comp * nm:(comp + 1) * nm] = row
    return out


def syzygy_rows(d):
    """Equations (coefficient of each degree-(d+1) monomial in sum_i X_i g_i) = 0."""
    mons, idx = monomials(d)
    mons1, idx1 = monomials(d + 1)
    nm = len(mons)
    rows = [[0] * (3 * nm) for _ in mons1]
    for i in range(Q):
        for k, mo in enumerate(mons):
            mo1 = list(mo)
            mo1[i] += 1
            rows[idx1[tuple(mo1)]][i * nm + k] = 1
    return rows


# ------------------------------------------------------------------ geometry
def cross(a, b):
    return [(a[1] * b[2] - a[2] * b[1]) % P, (a[2] * b[0] - a[0] * b[2]) % P, (a[0] * b[1] - a[1] * b[0]) % P]


def line_coeffs(A, t, c):
    return [A[t][c][i][0] % P for i in range(Q)]


def base_points(A, t):
    """The 6 base points of block t: interior z_{cd} = L_tc cap L_td (c<d) and boundary z_c = L_tc cap {X_c=0}."""
    inter, bound = {}, {}
    for c in range(Q):
        for d in range(c + 1, Q):
            inter[(c, d)] = cross(line_coeffs(A, t, c), line_coeffs(A, t, d))
    for c in range(Q):
        e = [1 if i == c else 0 for i in range(Q)]
        bound[c] = cross(line_coeffs(A, t, c), e)
    return inter, bound


def lin(l, X):
    return sum(l[i] * X[i] for i in range(Q)) % P


def other_point_on_line(l, rng, avoid=()):
    """A random point on the line l (different from the given points)."""
    while True:
        x, y = rng.randrange(1, P), rng.randrange(1, P)
        if l[0] % P:
            X = [(-(l[1] * x + l[2] * y)) * pow(l[0], P - 2, P) % P, x, y]
        elif l[1] % P:
            X = [x, (-(l[0] * x + l[2] * y)) * pow(l[1], P - 2, P) % P, y]
        else:
            X = [x, y, 0]
        if all(x_ for x_ in X):
            return X


# ------------------------------------------------------------------ numerators
def dlim_value(A, X, mults):
    v = 1
    for t, mu in mults.items():
        for c in range(Q):
            v = v * pow(lin(line_coeffs(A, t, c), X), mu, P) % P
    return v


class Numerators:
    """Interpolate D_lim * f (degree d+1 components) for term-list vectors; return g-coefficient vectors."""

    def __init__(self, A, mults, d, rng):
        self.A, self.mults, self.d = A, mults, d
        mons1, _ = monomials(d + 1)
        self.M1 = len(mons1)
        while True:
            pts = []
            while len(pts) < self.M1 + 2:
                X = [rng.randrange(1, P) for _ in range(Q)]
                try:
                    kernels_series(A, X, 1)
                except ZeroDivisionError:
                    continue
                pts.append(X)
            V = flint.nmod_mat([eval_monomials(d + 1, X) for X in pts[:self.M1]], P)
            if V.rank() == self.M1:
                break
        self.pts = pts
        self.Vinv = V.inv()
        self.dl = [dlim_value(A, X, mults) for X in pts]

    def g_vectors(self, vecs, extra_blocks=None):
        """vecs: term lists over the blocks of A (plus optional extra kernels via extra_blocks(X))."""
        d = self.d
        mons, idx = monomials(d)
        mons1, idx1 = monomials(d + 1)
        nm = len(mons)
        vals = [[[0] * len(self.pts) for _ in range(2)] for _ in vecs]
        for k, X in enumerate(self.pts):
            kers = kernels_series(self.A, X, 1)
            if extra_blocks is not None:
                kers = kers + extra_blocks(X)
            wc = WordCache(kers, 1)
            for r, terms in enumerate(vecs):
                v = term_vec(kers, X, terms, 1, wc, 2)
                vals[r][0][k] = v[0][0] * self.dl[k] % P
                vals[r][1][k] = v[1][0] * self.dl[k] % P
        out = []
        for r in range(len(vecs)):
            g = [0] * (3 * nm)
            Pc = []
            for comp in range(2):
                y = flint.nmod_mat([[vals[r][comp][k]] for k in range(self.M1)], P)
                c = self.Vinv * y
                coef = [int(c[i, 0]) for i in range(self.M1)]
                # check at the extra points
                for k in range(self.M1, len(self.pts)):
                    ev = eval_monomials(d + 1, self.pts[k])
                    assert sum(a * b for a, b in zip(coef, ev)) % P == vals[r][comp][k], 'interpolation check failed'
                Pc.append(coef)
            Pc.append([(-a - b) % P for a, b in zip(Pc[0], Pc[1])])
            for comp in range(3):
                for i1, mo1 in enumerate(mons1):
                    cf = Pc[comp][i1]
                    if not cf:
                        continue
                    if mo1[comp] == 0:
                        raise ValueError('numerator component not divisible by X_i')
                    mo = list(mo1)
                    mo[comp] -= 1
                    g[comp * nm + idx[tuple(mo)]] = cf
            out.append(g)
        return out


def apply_rows(rows, vec):
    return [sum(r[i] * vec[i] for i in range(len(vec)) if vec[i] and r[i]) % P for r in rows]


def rank(rows):
    return flint.nmod_mat(rows, P).rank() if rows else 0


def selftest():
    rng = random.Random(2)
    n = 2
    g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
    us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(n)]
    A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
    d = 3 * n
    num = Numerators(A, {0: 1, 1: 1}, d, rng)
    vecs = [[(1, a, [], 'IW', [s])] for s in range(n) for a in range(Q)]
    vecs += [[(1, a, [(t, b)], 'IW', [1 - t])] for t in range(n) for a in range(Q) for b in range(Q)]
    G = num.g_vectors(vecs)
    syz = syzygy_rows(d)
    assert all(x == 0 for gv in G for x in apply_rows(syz, gv))
    nm = len(monomials(d)[0])
    for t in range(n):
        inter, bound = base_points(A, t)
        for z in list(inter.values()) + list(bound.values()):
            ev = eval_monomials(d, z)
            for gv in G:
                for comp in range(3):
                    assert sum(ev[i] * gv[comp * nm + i] for i in range(nm)) % P == 0, 'base condition'
    print(f'selftest: {len(vecs)} canonical vectors of W_2: numerators satisfy the syzygy and all 12 base conditions; '
          f'rank {rank(G)} (dim W_2 = 24).')


if __name__ == '__main__':
    selftest()
