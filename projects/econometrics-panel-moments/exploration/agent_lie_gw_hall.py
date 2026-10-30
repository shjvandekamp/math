#!/usr/bin/env python3
"""Word families: GW is false; the one-head block is a transversal matroid (Hall).

Checks (mod p = 2^61-1 at random product-form points unless stated; a full
modular rank at an F_p point is a certificate of generic full rank for that
family and n; a rank drop is evidence only, except where a structural zero
pattern is exhibited):

 (S)  support rule: the canonical coordinate (u,v,c,d) of the column
      h_{tab}(I - W), W = K_{x1}...K_{xk}, extended word x = (t, x1, ..., xk),
      is nonzero iff u, v in x, u != last(x), the head letter t carries state a,
      and the letter in position 1 carries state b whenever the earlier of
      u, v sits in position 0 together with the later in position 1, or the
      earlier sits in position 1.  (Compared with the computed zero pattern.)
 (C)  counterexample to Conjecture GW (n = 4): head 0 words {(1),(2),(1,2)},
      other heads single letters.  The 9 coordinates (0,3,a,d) vanish on every
      column (structural), so the family is NOT a basis.
 (G1) one-head block D_{t,a} (rows (t,v,a,d), columns (b,w)): for distinct
      words, full rank iff Hall's condition (letters vs words, v ~ w iff v in w).
      n = 4 exhaustive over all 455 three-word sets, n = 5 sampled.
 (T)  transversal matroid: for random sets of columns (b,w) (any b's, any
      words), rank D = structural rank (max matching of the support graph).
 (H)  balanced families (n-1 distinct words per head) with Hall per head are
      bases (random and adversarial choices, n = 4..7).
 (N)  Hall per head is not necessary in the full problem (other heads can
      compensate), and rank < structural rank occurs (cross-head relations).
 (M)  mixed families "DHW words on a head set H, single letters elsewhere" are
      bases for all 2^n sets H (n <= 6): every principal head-block minor of the
      DHW matrix in canonical coordinates is nonzero.
"""
import itertools as it
import random
import sys
import time
from collections import Counter
from pathlib import Path

import flint
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_lie_common import (P61, Q, Ring, dhw_word, family_matrix, gw1_matrix,  # noqa: E402
                              random_point, words_on)
from hq_fresh_fast import row_index  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402

R = Ring(P61)


def hall(words, letters):
    letters = list(letters)
    for k in range(1, len(letters) + 1):
        for V in it.combinations(letters, k):
            if sum(1 for w in words if set(w) & set(V)) < k:
                return False
    return True


def struct_rank(M):
    S = np.array([[1 if int(M[i, j]) else 0 for j in range(M.ncols())] for i in range(M.nrows())],
                 dtype=np.int8)
    m = maximum_bipartite_matching(csr_matrix(S), perm_type='column')
    return int((m >= 0).sum())


def predicted_support(t, a, b, w, key):
    x = [t] + list(w)
    u, v, c, d = key
    if u not in x or v not in x or u == x[-1]:
        return False
    st = {u: c, v: d}
    if t in st and st[t] != a:
        return False
    pos = {y: i for i, y in enumerate(x)}
    i, j = sorted((pos[u], pos[v]))
    if (i == 0 and j == 1) or i == 1:
        if st[x[1]] != b:
            return False
    return True


def check_support():
    out = []
    for n in (3, 4, 5):
        A = random_point(n, R, 30 + n)
        rng = random.Random(n)
        cols = []
        for _ in range(200):
            t, a, b = rng.randrange(n), rng.randrange(Q), rng.randrange(Q)
            cols.append((t, a, b, [(1, list(rng.choice(words_on([u for u in range(n) if u != t]))))]))
        rows = build_cols(A, n, R, cols)
        bad = sum(1 for j, (t, a, b, terms) in enumerate(cols) for k in row_index(n)
                  if (int(rows[k][j]) != 0) != predicted_support(t, a, b, terms[0][1], k))
        out.append(f'n={n}: {bad} mismatches/{len(cols) * len(row_index(n))}')
    print('(S) support rule vs computed zero pattern: ' + '; '.join(out))


def check_counterexample():
    n = 4
    wph = {t: [(s,) for s in range(n) if s != t] for t in range(n)}
    wph[0] = [(1,), (2,), (1, 2)]
    ranks = []
    for seed in (1, 2, 3):
        A = random_point(n, R, 100 + seed)
        M, keys, _ = family_matrix(A, n, R, wph)
        zero_rows = [k for i, k in enumerate(keys) if all(int(M[i, j]) == 0 for j in range(M.ncols()))]
        ranks.append((M.rank(), len(zero_rows), all(k[0] == 0 and k[1] == 3 for k in zero_rows)))
    print(f'(C) GW counterexample n=4, head 0 words (1),(2),(1,2), others canonical: '
          f'(rank/108, #zero rows, all zero rows are (0,3,a,d)) = {ranks}')


def check_gw1_hall():
    n = 4
    stats = Counter()
    for seed in (24, 99):
        A = random_point(n, R, seed)
        allw = words_on([1, 2, 3])
        for ws in it.combinations(allw, n - 1):
            full = all(gw1_matrix(A, n, R, 0, a, ws).rank() == 3 * (n - 1) for a in range(Q))
            stats[(hall(ws, [1, 2, 3]), full)] += 1
    print(f'(G1) n=4 exhaustive (2 points x 455 word sets): (Hall, full rank) counts {dict(stats)}')
    n = 5
    A = random_point(n, R, 77)
    letters = [1, 2, 3, 4]
    allw = words_on(letters)
    rng = random.Random(3)
    stats = Counter()
    trials = [rng.sample(allw, 4) for _ in range(300)]
    short = [w for w in allw if len(w) <= 2]
    trials += [rng.sample(short, 4) for _ in range(300)]
    for x, y in it.combinations(letters, 2):        # covering but not Hall
        z, u = [l for l in letters if l not in (x, y)]
        for trip in it.combinations(words_on([z, u]), 3):
            trials.append(list(trip) + [(x, y)])
    for ws in trials:
        full = all(gw1_matrix(A, n, R, 0, a, ws).rank() == 12 for a in range(Q))
        stats[(hall(ws, letters), full)] += 1
    print(f'(G1) n=5 sampled ({len(trials)} word sets): (Hall, full rank) counts {dict(stats)}')


def check_transversal():
    res = []
    for n in (4, 5, 6):
        A = random_point(n, R, 1500 + n)
        t, a = 0, 1
        S = [u for u in range(n) if u != t]
        allw = words_on(S, max_len=4)
        keys = [(t, v, a, d) for v in S for d in range(Q)]
        rng = random.Random(n)
        st = Counter()
        for _ in range(150):
            ws = rng.sample(allw, rng.randint(n - 1, 3 * (n - 1)))
            pool = [(b, w) for w in ws for b in range(Q)]
            sel = rng.sample(pool, min(len(pool), 3 * (n - 1)))
            cols = [(t, a, b, [(1, list(w))]) for b, w in sel]
            rows = build_cols(A, n, R, cols)
            M = flint.nmod_mat([[int(rows[k][j]) for j in range(len(cols))] for k in keys], P61)
            st[M.rank() == struct_rank(M)] += 1
        # exhaustive: all 6-subsets of the 12 columns of words on two letters
        L = [1, 2]
        cols = [(t, a, b, [(1, list(w))]) for w in words_on(L) for b in range(Q)]
        rows = build_cols(A, n, R, cols)
        k2 = [(t, v, a, d) for v in L for d in range(Q)]
        full = [[int(rows[k][j]) for j in range(len(cols))] for k in k2]
        ex = Counter()
        for cs in it.combinations(range(len(cols)), 6):
            M = flint.nmod_mat([[full[i][j] for j in cs] for i in range(6)], P61)
            ex[M.rank() == struct_rank(M)] += 1
        res.append(f'n={n}: random {dict(st)}, two-letter exhaustive {dict(ex)}')
    print('(T) rank == structural rank for column subsets of D_{t,a}: ' + '; '.join(res))


def random_hall_family(n, rng, mode):
    wph = {}
    for t in range(n):
        S = [u for u in range(n) if u != t]
        allw = words_on(S)
        while True:
            if mode == 0:
                ws = rng.sample(allw, n - 1)
            elif mode == 1:
                ws = rng.sample([w for w in allw if len(w) <= 2], n - 1)
            elif mode == 2:          # permutations with a common first letter (n >= 5)
                f = rng.choice(S)
                perms = [(f,) + p for p in it.permutations([x for x in S if x != f])]
                ws = rng.sample(perms if len(perms) >= n - 1 else allw, n - 1)
            else:                    # a block of words with identical support + short filler
                f, lst = rng.sample(S, 2)
                same = [(f,) + m + (lst,) for m in it.permutations([x for x in S if x not in (f, lst)])]
                k = min(len(same), rng.randint(2, n - 1))
                ws = rng.sample(same, k) + rng.sample([w for w in allw if len(w) <= 2], n - 1 - k)
            if len(set(ws)) == n - 1 and hall(ws, S):
                break
        wph[t] = ws
    return wph


def check_balanced_hall():
    res = []
    for n, ntr in ((4, 60), (5, 40), (6, 16), (7, 12), (8, 4)):
        t0 = time.time()
        A = random_point(n, R, 600 + n)
        rng = random.Random(19 + n)
        st = Counter()
        for trial in range(ntr):
            mode = trial % 4 if n >= 4 else trial % 2
            if n == 4 and mode == 3:
                mode = 1
            M, _, _ = family_matrix(A, n, R, random_hall_family(n, rng, mode))
            st[M.rank() == M.nrows()] += 1
        res.append(f'n={n}: {dict(st)} [{time.time() - t0:.0f}s]')
    print('(H) balanced per-head-Hall families, full rank counts: ' + '; '.join(res))


def check_not_necessary():
    res = []
    for n in (4, 5):
        A = random_point(n, R, 700 + n)
        rng = random.Random(29 + n)
        st = Counter()
        for trial in range(40):
            bad = rng.randrange(n)
            wph = {}
            for t in range(n):
                S = [u for u in range(n) if u != t]
                pool = words_on(S) if trial % 2 else [w for w in words_on(S) if len(w) <= 2]
                while True:
                    ws = rng.sample(pool, n - 1)
                    if hall(ws, S) != (t == bad):
                        break
                wph[t] = ws
            M, _, _ = family_matrix(A, n, R, wph)
            st[M.nrows() - M.rank()] += 1
        res.append(f'n={n}: deficit counts {dict(st)}')
    # rank < structural rank (balanced, one head non-covering)
    n = 4
    wph = {0: [(2,), (3,), (2, 3)], 1: [(3, 0), (2, 3), (0, 3)], 2: [(0, 3, 1), (1, 0), (3, 0, 1)],
           3: [(2,), (2, 0), (0, 2)]}
    M, _, _ = family_matrix(random_point(n, R, 44), n, R, wph)
    print('(N) exactly one head violating Hall: ' + '; '.join(res) +
          f'; example rank {M.rank()} < structural rank {struct_rank(M)} (n=4)')


def check_mixed():
    res = []
    for n in (3, 4, 5, 6):
        A = random_point(n, R, 8100 + n)
        ok = tot = 0
        for k in range(n + 1):
            for H in it.combinations(range(n), k):
                wph = {t: ([dhw_word(t, s, n) for s in range(n) if s != t] if t in H
                           else [(s,) for s in range(n) if s != t]) for t in range(n)}
                M, _, _ = family_matrix(A, n, R, wph)
                tot += 1
                ok += M.rank() == M.nrows()
        res.append(f'n={n}: {ok}/{tot}')
    print('(M) DHW on head set H, canonical elsewhere, bases: ' + '; '.join(res))


def check_dhw_is_hall():
    ok = all(hall([dhw_word(t, s, n) for s in range(n) if s != t], [u for u in range(n) if u != t])
             for n in range(2, 9) for t in range(n))
    print(f'DHW words satisfy Hall per head (they are permutations), n<=8: {ok}')


if __name__ == '__main__':
    t0 = time.time()
    check_support()
    check_counterexample()
    check_gw1_hall()
    check_transversal()
    check_balanced_hall()
    check_not_necessary()
    check_mixed()
    check_dhw_is_hall()
    print(f'total {time.time() - t0:.0f}s')
