#!/usr/bin/env python3
"""agent_ag: exact identities around the head map (mod p = 2^61-1, random product points).

Q1  Phi_n(w) = H(w) + (w - H(w)) K_N  with H(w) = sum_tab Lambda_n(w)_tab h_tab, where
    Phi_n(w) := sum f F'_{tsab} + sum e (E_{s,a} - E_{N,a}), F' = h (I - W K_N)  (w = sum f F + sum e E).
Q2  Lambda_{n+1}(Phi_n(w)) = (Lambda_n(w), eps_n(w)),  eps_n(w)_a = sum_s e_{s,a}(w)  (new head N).
Q3  dim(W_n + Head_n) = 9n^2 + 3, i.e. Head_n cap W_n = span{E_{t,a} - E_{t',a}} (dim 3n-3), and
    Q(n): the 9n^2 + 3 functions {h_tab} u {h_tab W_{t,s}} u {X_a e_a} are linearly independent
    (equivalent to the goal P(n) = basis property of {E} u {F}).
What this does not show: Q(n) for n beyond those printed.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_ag_lib import (P, Q, Basis, PointEval, kernels_at, rand_point, product_config, family,  # noqa: E402
                          head_map_matrix, dhw_word, combine)


def points(A, m, rng):
    pts = []
    while len(pts) < m:
        X = rand_point(rng)
        try:
            kernels_at(A, X)
        except ZeroDivisionError:
            continue
        pts.append(X)
    return pts


def q1_q2(rng):
    for n in (2, 3, 4):
        A, g, us = product_config(n + 1, rng)
        N = n
        An = A[:n]
        labs, specs = family(n)
        f = [rng.randrange(P) for _ in specs]                     # random w in W_n
        w = combine(specs, f)
        Bn = Basis(An, specs, rng)
        heads, L = head_map_matrix(labs, Bn.coords([w]), n)
        lam = {h: int(L[i, 0]) for i, h in enumerate(heads)}
        # Phi_n(w) from the coefficients
        phi = []
        for k, lab in enumerate(labs):
            if lab[0] == 'F':
                _, t, s, a, b = lab
                phi.append((f[k], a, [(t, b)], b, dhw_word(t, s, list(range(n))) + [N]))
            else:
                _, s, a = lab
                phi.append((f[k], a, [], a, [s]))
                phi.append((-f[k] % P, a, [], a, [N]))
        ok1 = True
        for X in points(A, 6, rng):
            pe, pn = PointEval(A, X), PointEval(An, X)
            lhs = pe.vec(phi)
            wv = pn.vec(w)
            Ks = pe.Ks
            H = [0, 0, 0]
            for (t, a, b), c in lam.items():
                H[b] = (H[b] + c * X[a] % P * Ks[t][a][b]) % P
            body = [(wv[j] - H[j]) % P for j in range(Q)]
            rhs = [(H[j] + sum(body[i] * Ks[N][i][j] for i in range(Q))) % P for j in range(Q)]
            ok1 &= (lhs == rhs)
        labs1, specs1 = family(n + 1)
        B1 = Basis(A, specs1, rng)
        heads1, L1 = head_map_matrix(labs1, B1.coords([phi]), n + 1)
        eps = [sum(f[k] for k, lab in enumerate(labs) if lab[0] == 'E' and lab[2] == a) % P for a in range(Q)]
        ok2 = all(int(L1[i, 0]) == (lam[h] if h[0] < n else eps[h[1]]) for i, h in enumerate(heads1))
        print(f'Q1 n={n}: Phi_n(w) = H(w) + (w - H(w)) K_N at random points: {ok1};  '
              f'Q2: Lambda_(n+1)(Phi_n w) = (Lambda_n w, eps_n w): {ok2}')


def q3(rng):
    for n in (2, 3, 4, 5):
        A, g, us = product_config(n, rng)
        npts = (9 * n * n - 6 * n) // 2 + 10
        rowsWH, rowsQ = [], []
        labs, specs = family(n)
        for X in points(A, npts, rng):
            pe = PointEval(A, X)
            Ks = pe.Ks
            heads = [[X[a] * Ks[t][a][b] % P if j == b else 0 for j in range(Q)]
                     for t in range(n) for a in range(Q) for b in range(Q)]
            fam = [pe.vec(sp) for sp in specs]
            bodies = []
            for t in range(n):
                for s in range(n):
                    if s != t:
                        Wm = pe.word(dhw_word(t, s, list(range(n))))
                        bodies += [[X[a] * Ks[t][a][b] % P * Wm[b][j] % P for j in range(Q)]
                                   for a in range(Q) for b in range(Q)]
            coords = [[X[a] if j == a else 0 for j in range(Q)] for a in range(Q)]
            for j in range(Q):
                rowsWH.append([v[j] for v in fam + heads])
                rowsQ.append([v[j] for v in heads + bodies + coords])
        rWH = flint.nmod_mat(rowsWH, P).rank()
        rQ = flint.nmod_mat(rowsQ, P).rank()
        print(f'Q3 n={n}: dim(W_n + Head)={rWH} (9n^2+3={9 * n * n + 3}); Q(n): rank of heads+bodies+X_a e_a = '
              f'{rQ} / {9 * n * n + 3}')


if __name__ == '__main__':
    rng = random.Random(7)
    q1_q2(rng)
    q3(rng)
