#!/usr/bin/env python3
"""Cross-head relations among word vectors, and failure of head-block dominance.

 (R1) Relation C (exact, fmpq, n = 3): for heads t != s, state a and tail r,
      the six vectors h_{taa}(I - K_s K_r), h_{saa}(I - K_t K_r), h_{tad}(I - K_r),
      h_{sad}(I - K_r) (d != a) are independent in W_n/E but dependent modulo
      span{B_{t,s,a,a}, B_{s,t,a,a}} (rank 5 of 6).  Heuristic source: the
      diagonal steps K_t(a,a) K_s(a,a) = K_s(a,a) K_t(a,a) commute.
 (R2) per-(t,a,b) word choices at n = 3 (two distinct words for each (t,a,b)):
      failures occur; every failure's kernel lives on two heads and one head
      state a, i.e. it is a Relation-C type dependency.
 (R3) DHW in head blocks: rows grouped by first slot u, columns by head t.  The
      block-Jacobi matrix J = D^{-1}(R - D) (D = head-diagonal blocks, i.e. the
      one-head blocks D_{t,a}) has spectral radius >> 1 at random positive
      product-form points: no block diagonal dominance by heads.
"""
import random
import sys
from collections import Counter
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_lie_common import P61, Q, Ring, dhw_word, family_matrix, random_point, words_on  # noqa: E402
from hq_fresh_fast import row_index  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402


def r1():
    Rq = Ring(None)
    n, t, s, a, r = 3, 0, 1, 1, 2
    out = []
    for seed in (1, 2, 3):
        A = random_point(n, Rq, 5000 + seed, lo=1, hi=40)
        cols = ([(t, a, a, [(1, [s, r])]), (s, a, a, [(1, [t, r])])] +
                [(t, a, d, [(1, [r])]) for d in range(Q) if d != a] +
                [(s, a, d, [(1, [r])]) for d in range(Q) if d != a])
        rows = build_cols(A, n, Rq, cols)
        full = flint.fmpq_mat([[rows[k][j] for j in range(6)] for k in row_index(n)])
        keys = [k for k in row_index(n) if k not in ((t, s, a, a), (s, t, a, a))]
        red = flint.fmpq_mat([[rows[k][j] for j in range(6)] for k in keys])
        out.append((full.rank(), red.rank()))
    print(f'(R1) Relation C, n=3, 3 rational points: (rank in W/E, rank mod B_tsaa,B_staa) = {out}')


def r2():
    R = Ring(P61)
    n = 3
    A = random_point(n, R, 4242)
    rng = random.Random(8)
    st = Counter()
    for _ in range(400):
        wph = {}
        for t in range(n):
            allw = words_on([u for u in range(n) if u != t])
            for a in range(Q):
                for b in range(Q):
                    wph[(t, a, b)] = rng.sample(allw, 2)
        M, keys, lab = family_matrix(A, n, R, wph)
        if M.rank() == M.nrows():
            st['basis'] += 1
            continue
        K, nul = M.nullspace()
        for j in range(nul):
            supp = [lab[i] for i in range(M.ncols()) if int(K[i, j]) != 0]
            heads = {x[0] for x in supp}
            states = {x[1] for x in supp}
            st['kernel on 2 heads, 1 head state' if len(heads) == 2 and len(states) == 1 else 'other kernel'] += 1
    print(f'(R2) per-(t,a,b) choices, n=3, 400 random: {dict(st)}')


def r3():
    Rq = Ring(None)
    res = []
    for n in (3, 4, 5):
        rhos = []
        for seed in range(6):
            A = random_point(n, Rq, 7000 + seed, lo=1, hi=50)
            dhw = {t: [dhw_word(t, s, n) for s in range(n) if s != t] for t in range(n)}
            M, keys, lab = family_matrix(A, n, Rq, dhw)
            X = np.array([[float(M[i, j]) for j in range(M.ncols())] for i in range(M.nrows())])
            rh = np.array([k[0] for k in keys])
            ch = np.array([x[0] for x in lab])
            D = np.where(rh[:, None] == ch[None, :], X, 0.0)
            J = np.linalg.solve(D, X - D)
            rhos.append(float(max(abs(np.linalg.eigvals(J)))))
        res.append(f'n={n}: min {min(rhos):.1f}, max {max(rhos):.1f}')
    print('(R3) DHW block-Jacobi spectral radius over heads (6 positive points each): ' + '; '.join(res))


if __name__ == '__main__':
    r1()
    r2()
    r3()
