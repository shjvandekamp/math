#!/usr/bin/env python3
"""Canonical B-coordinates of arbitrary word vectors  sum_k c_k h_{tab} (I - W_k).

h_{tab} = X_a K_t(a,b) e_b.  A column is (t, a, b, [(c_k, word_k), ...]) with
sum_k c_k in {0, 1} (so the vector lies in W_n) and words of distinct blocks
different from t.  The double residue at P = L_{uc} cap L_{vd} of h W is
nonzero only if both poles are present (block u is t with c = a, or occurs
in W; same for v); the residue rows of K_u, K_v are substituted in W.

Families provided:
  F    : source columns F_{t,s,a,b} = h (I - K_s P_{(s,t)})            (equation 24)
  G    : standard-tail columns G_{t,r,a,b} = B_{t,r,a,b} K_{>r, != t}
         = h (I - K_r P) - h (I - P),  P = increasing product of u > r, u != t
Self-test: the F family reproduces hq_fresh_fast.build_R exactly.
"""
import itertools as it
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import (Ring, cross, dot, kernel_at, residue_kernel, matmul,  # noqa: E402
                           row_index, product_blocks)

Q = 3


def word_res_product(word, mats, R):
    P = None
    for u in word:
        P = mats[u] if P is None else matmul(P, mats[u])
    if P is None:
        one, zero = R(1), R(0)
        P = [[one if i == j else zero for j in range(Q)] for i in range(Q)]
    return P


def build_cols(A, n, R, columns):
    """columns: list of (t, a, b, terms). Returns dict rows[(u,v,c,d)] -> list over columns."""
    zero = R(0)
    rows = {key: [zero] * len(columns) for key in row_index(n)}
    for u, v in it.combinations(range(n), 2):
        for c, d in it.product(range(Q), repeat=2):
            P = cross(A[u][c], A[v][d])
            U = [A[u][c][i] * P[i] for i in range(Q)]
            V = [A[v][d][i] * P[i] for i in range(Q)]
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
            ruv, rvu = rows[(u, v, c, d)], rows[(v, u, d, c)]
            cache = {}
            for j, (t, a, b, terms) in enumerate(columns):
                if t == u and a != c:
                    continue
                if t == v and a != d:
                    continue
                pref = A[t][a][b] * P[b]
                if t not in (u, v):
                    pref = pref / dot(A[t][a], P)
                sc = -P[a] * pref
                acc = [zero, zero, zero]
                for coef, word in terms:
                    cov_u = (t == u) or (u in word)
                    cov_v = (t == v) or (v in word)
                    if not (cov_u and cov_v):
                        continue
                    key = tuple(word)
                    if key not in cache:
                        cache[key] = word_res_product(word, mats, R)
                    Wb = cache[key][b]
                    acc = [acc[i] + coef * Wb[i] for i in range(Q)]
                if acc[0] == 0 and acc[1] == 0 and acc[2] == 0:
                    continue
                x = [sc * y for y in acc]
                al = (x[i0] * V[j0] - x[j0] * V[i0]) / det
                be = (U[i0] * x[j0] - U[j0] * x[i0]) / det
                ruv[j] = be / norm_uv
                rvu[j] = al / norm_vu
    return rows


def F_columns(n):
    cols = []
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            word = [s] + [u for u in range(n) if u not in (s, t)]
            for a in range(Q):
                for b in range(Q):
                    cols.append(((t, s, a, b), (t, a, b, [(1, word)])))
    return cols


def G_columns(n):
    cols = []
    for t in range(n):
        for r in range(n):
            if r == t:
                continue
            tail = [u for u in range(n) if u > r and u != t]
            for a in range(Q):
                for b in range(Q):
                    cols.append(((t, r, a, b), (t, a, b, [(1, [r] + tail), (-1, tail)])))
    return cols


def matrix_of(A, n, R, labelled_cols):
    cols = [c for _, c in labelled_cols]
    rows = build_cols(A, n, R, cols)
    keys = row_index(n)
    return keys, rows


def selftest():
    import random
    from hq_fresh_fast import build_R
    R = Ring(None)
    for n in (2, 3, 4):
        A = product_blocks(n, R, random.Random(n))
        cols0, rows0 = build_R(A, n, R)
        lab = F_columns(n)
        assert [k for k, _ in lab] == cols0
        rows1 = build_cols(A, n, R, [c for _, c in lab])
        assert all(rows0[k] == rows1[k] for k in rows0)
    print('selftest: generic word builder reproduces build_R for the F family (n=2,3,4).')


if __name__ == '__main__':
    selftest()
    import random
    p = (1 << 61) - 1
    R = Ring(p)
    for n in range(2, 8):
        A = product_blocks(n, R, random.Random(100 + n))
        lab = G_columns(n)
        rows = build_cols(A, n, R, [c for _, c in lab])
        keys = [k for k, _ in lab]
        M = flint.nmod_mat([[int(x) for x in rows[k]] for k in keys], p)
        print(f'n={n}: standard-tail family G: rank {M.rank()}/{M.nrows()}', flush=True)
