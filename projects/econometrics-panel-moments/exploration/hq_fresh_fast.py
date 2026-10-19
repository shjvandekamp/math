#!/usr/bin/env python3
"""Fast construction of R_n over python-flint scalars (fmpq or nmod).

Same mathematics as hq_fresh_lib.b_coefficient_matrix (rows = canonical
local-pair coordinates B_{u,v,c,d}, columns = source columns
F_{t,s,a,b}), but the word for each (cross point, t, s) is formed once
and reused for all nine (a, b).  Scalars are any python-flint type
supporting + - * / (fmpq for exact rationals, nmod for F_p).

Run directly for a self-test against the Fraction implementation and a
modular full-rank sweep at economic points:
    .venv/bin/python hq_fresh_fast.py
"""
import itertools as it
import random
import sys
from fractions import Fraction
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))

Q = 3


class Ring:
    """Scalar factory: exact rationals (p=None) or integers mod p."""

    def __init__(self, p=None):
        self.p = p

    def __call__(self, x):
        if self.p is None:
            if isinstance(x, Fraction):
                return flint.fmpq(x.numerator, x.denominator)
            return flint.fmpq(x)
        if isinstance(x, Fraction):
            return flint.nmod(x.numerator, self.p) / flint.nmod(x.denominator, self.p)
        if isinstance(x, flint.fmpq):
            return flint.nmod(int(x.p), self.p) / flint.nmod(int(x.q), self.p)
        return flint.nmod(x, self.p)

    def matrix(self, rows):
        if self.p is None:
            return flint.fmpq_mat(rows)
        return flint.nmod_mat([[int(x) for x in r] for r in rows], self.p)


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def matmul(a, b):
    return [[a[i][0] * b[0][j] + a[i][1] * b[1][j] + a[i][2] * b[2][j] for j in range(Q)] for i in range(Q)]


def kernel_at(At, X, R):
    K = []
    for a in range(Q):
        L = dot(At[a], X)
        if L == 0:
            raise ZeroDivisionError('kernel on its own line')
        K.append([At[a][i] * X[i] / L for i in range(Q)])
    return K


def residue_kernel(At, c, X, R):
    z = R(0)
    M = [[z, z, z] for _ in range(Q)]
    M[c] = [At[c][i] * X[i] for i in range(Q)]
    return M


def word_product(order, mats, R):
    P = None
    for u in order:
        P = mats[u] if P is None else matmul(P, mats[u])
    if P is None:
        one, zero = R(1), R(0)
        P = [[one if i == j else zero for j in range(Q)] for i in range(Q)]
    return P


def increasing_word(s, t, n):
    return [s] + [u for u in range(n) if u != s and u != t]


def col_index(n):
    return [(t, s, a, b) for t in range(n) for s in range(n) if s != t
            for a in range(Q) for b in range(Q)]


def row_index(n):
    rows = []
    for u, v in it.combinations(range(n), 2):
        for c, d in it.product(range(Q), repeat=2):
            rows.append((u, v, c, d))
            rows.append((v, u, d, c))
    return rows


def geometry_ok(A, n):
    """Cross points have nonzero coordinates and lie on no third line; det A_t != 0."""
    for t in range(n):
        At = A[t]
        det = (At[0][0] * (At[1][1] * At[2][2] - At[1][2] * At[2][1])
               - At[0][1] * (At[1][0] * At[2][2] - At[1][2] * At[2][0])
               + At[0][2] * (At[1][0] * At[2][1] - At[1][1] * At[2][0]))
        if det == 0:
            return False
    lines = [(t, a) for t in range(n) for a in range(Q)]
    for (u, c), (v, d) in it.combinations(lines, 2):
        if u == v:
            continue
        P = cross(A[u][c], A[v][d])
        if any(x == 0 for x in P):
            return False
        for (w, e) in lines:
            if (w, e) not in ((u, c), (v, d)) and dot(A[w][e], P) == 0:
                return False
    return True


def build_R(A, n, R):
    """R_n as a dict: rows[(u,v,c,d)] -> list over col_index(n)."""
    cols = col_index(n)
    cpos = {key: i for i, key in enumerate(cols)}
    zero = R(0)
    rows = {key: [zero] * len(cols) for key in row_index(n)}
    for u, v in it.combinations(range(n), 2):
        for c, d in it.product(range(Q), repeat=2):
            P = cross(A[u][c], A[v][d])
            U = [A[u][c][i] * P[i] for i in range(Q)]
            V = [A[v][d][i] * P[i] for i in range(Q)]
            # coordinates in (U, V): use the (0,1) minor if nonzero, else another
            for i0, j0 in ((0, 1), (0, 2), (1, 2)):
                det = U[i0] * V[j0] - U[j0] * V[i0]
                if det != 0:
                    break
            norm_uv = -A[u][c][d] * P[c] * P[d]
            norm_vu = -A[v][d][c] * P[c] * P[d]
            mats = {}
            for w in range(n):
                if w == u:
                    mats[w] = residue_kernel(A[u], c, P, R)
                elif w == v:
                    mats[w] = residue_kernel(A[v], d, P, R)
                else:
                    mats[w] = kernel_at(A[w], P, R)
            Lval = {(w, e): dot(A[w][e], P) for w in range(n) for e in range(Q)}
            ruv, rvu = rows[(u, v, c, d)], rows[(v, u, d, c)]
            for t in range(n):
                for s in range(n):
                    if s == t:
                        continue
                    W = word_product(increasing_word(s, t, n), mats, R)
                    # coordinates of each row of W in (U, V)
                    coords = []
                    for b in range(Q):
                        x = W[b]
                        al = (x[i0] * V[j0] - x[j0] * V[i0]) / det
                        be = (U[i0] * x[j0] - U[j0] * x[i0]) / det
                        coords.append((al, be))
                    for a in range(Q):
                        if t == u and a != c:
                            continue
                        if t == v and a != d:
                            continue
                        for b in range(Q):
                            al, be = coords[b]
                            if al == 0 and be == 0:
                                continue
                            pref = A[t][a][b] * P[b]
                            if t not in (u, v):
                                pref = pref / Lval[(t, a)]
                            sc = -P[a] * pref
                            j = cpos[(t, s, a, b)]
                            ruv[j] = sc * be / norm_uv
                            rvu[j] = sc * al / norm_vu
    return cols, rows


def R_matrix(A, n, R):
    cols, rows = build_R(A, n, R)
    return R.matrix([rows[key] for key in cols])


def product_blocks(n, R, rng, g=None, us=None, lo=1, hi=60):
    """A_t(a,i) = g(i,a) u_t(i) (product form = Zariski closure of economic family)."""
    while True:
        gg = g if g is not None else [[rng.randint(lo, hi) for _ in range(Q)] for _ in range(Q)]
        uu = us if us is not None else [[rng.randint(lo, hi) for _ in range(Q)] for _ in range(n)]
        A = [[[R(gg[i][a]) * R(uu[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
        if geometry_ok(A, n):
            return A
        if g is not None and us is not None:
            raise ValueError('given point violates the geometry conditions')


def economic_blocks(n, R, gamma_g, w, x):
    """Economic point: g(q,r) given, u_t(q) = w_q ** x_t with integer x_t."""
    us = [[R(w[q]) ** x[t] for q in range(Q)] for t in range(n)]
    A = [[[R(gamma_g[i][a]) * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
    return A


def selftest():
    import hq_fresh_lib as lib
    rng = random.Random(5)
    for n in (2, 3):
        while True:
            g = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(Q)]
            us = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(n)]
            Af = [[[Fraction(g[i][a] * us[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
            if lib.check_geometry(Af, n)[0] and all(lib.det_fraction(Af[t]) for t in range(n)):
                break
        cols0, rows0 = lib.b_coefficient_matrix(Af, n)
        Rq = Ring(None)
        A = [[[Rq(x) for x in row] for row in blk] for blk in Af]
        cols1, rows1 = build_R(A, n, Rq)
        assert cols0 == cols1
        for key in rows0:
            assert [Rq(x) for x in rows0[key]] == rows1[key], ('mismatch', n, key)
        print(f'selftest n={n}: fast R_n equals the Fraction implementation entrywise ({len(cols0)}x{len(cols0)}).')


def main():
    selftest()
    p = (1 << 61) - 1
    Rp = Ring(p)
    rng = random.Random(11)
    # economic point: g fixed positive integers, u_t(q) = w_q^(t+1)
    g = [[1, 1, 1], [1, 2, 4], [1, 4, 17]]
    w = [1, 2, 5]
    import time
    for n in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 7):
        t0 = time.time()
        A = economic_blocks(n, Rp, g, w, [t + 3 for t in range(n)])
        if not geometry_ok(A, n):
            print(f'n={n}: economic point fails geometry mod p; skipped')
            continue
        M = R_matrix(A, n, Rp)
        rk = M.rank()
        print(f'n={n} (T={n + 2}): economic point u_t=(1,2,5)^(t+3): rank R_n = {rk}/{M.nrows()}'
              f'{"  FULL" if rk == M.nrows() else ""}   [{time.time() - t0:.1f}s]')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
