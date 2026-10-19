#!/usr/bin/env python3
"""Shared helpers for the agent_lie_* experiments (word families, GW conjecture).

Column convention (as in hq_fresh_words.build_cols): a column is
(t, a, b, [(coef, word), ...]) and represents sum_k coef_k h_{tab}(I - W_k),
h_{tab} = X_a K_t(a,b) e_b; rows are canonical coordinates (u, v, c, d) =
coefficient of B_{u,v,c,d} (double residue at L_uc cap L_vd, v_vd-direction).
"Head block" of a column = t; "first slot" of a row = u.

Run directly for a self-test: the word family with all single letters is the
canonical basis (identity up to scaling) and the DHW family has full rank.
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, product_blocks, row_index  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402

Q = 3
P61 = (1 << 61) - 1


def words_on(letters, max_len=None):
    """All nonempty injective words (tuples) on the given letters."""
    letters = list(letters)
    out = []
    top = len(letters) if max_len is None else min(max_len, len(letters))
    for k in range(1, top + 1):
        out.extend(it.permutations(letters, k))
    return out


def dhw_word(t, s, n):
    return (s,) + tuple(u for u in range(n) if u not in (s, t))


def family_columns(n, words_per_head):
    """words_per_head[t] = list of words (same for all (a,b)); a key (t,a,b)
    overrides it for that (t,a,b) (per-(t,a,b) choice)."""
    cols, labels = [], []
    for t in range(n):
        for a in range(Q):
            for b in range(Q):
                ws = words_per_head[(t, a, b)] if (t, a, b) in words_per_head else words_per_head[t]
                for w in ws:
                    cols.append((t, a, b, [(1, list(w))]))
                    labels.append((t, a, b, tuple(w)))
    return cols, labels


def matrix_from_rows(rows, keys, ncols, R):
    if R.p is None:
        return flint.fmpq_mat([[rows[k][j] for j in range(ncols)] for k in keys])
    return flint.nmod_mat([[int(rows[k][j]) for j in range(ncols)] for k in keys], R.p)


def family_matrix(A, n, R, words_per_head):
    cols, labels = family_columns(n, words_per_head)
    rows = build_cols(A, n, R, cols)
    keys = row_index(n)
    return matrix_from_rows(rows, keys, len(cols), R), keys, labels


def random_point(n, R, seed, lo=1, hi=None):
    if hi is None:
        hi = 60 if R.p is None else R.p - 1
    return product_blocks(n, R, random.Random(seed), lo=lo, hi=hi)


def gw1_matrix(A, n, R, t, a, words):
    """One-head block D_{t,a}: rows (t,v,a,d) (v != t), columns (b, w)."""
    cols = []
    for b in range(Q):
        for w in words:
            cols.append((t, a, b, [(1, list(w))]))
    rows = build_cols(A, n, R, cols)
    keys = [(t, v, a, d) for v in range(n) if v != t for d in range(Q)]
    return matrix_from_rows(rows, keys, len(cols), R)


if __name__ == '__main__':
    R = Ring(P61)
    for n in (3, 4):
        A = random_point(n, R, 1 + n)
        canon = {t: [(s,) for s in range(n) if s != t] for t in range(n)}
        M, keys, lab = family_matrix(A, n, R, canon)
        nz = sum(1 for i in range(M.nrows()) for j in range(M.ncols()) if int(M[i, j]) != 0)
        dhw = {t: [dhw_word(t, s, n) for s in range(n) if s != t] for t in range(n)}
        M2, _, _ = family_matrix(A, n, R, dhw)
        print(f'n={n}: canonical family nonzeros={nz} (= size {M.nrows()}), rank {M.rank()}; '
              f'DHW rank {M2.rank()}/{M2.nrows()}')
