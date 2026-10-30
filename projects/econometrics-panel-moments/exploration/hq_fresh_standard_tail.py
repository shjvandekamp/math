#!/usr/bin/env python3
"""Theorem A check: the standard-tail family is a basis with a product formula.

G_{t,r,a,b} = B_{t,r,a,b} K_{>r}   (K_{>r} = increasing product of blocks u > r, u != t)

Appending the latest block n (old blocks 0..n-1) gives, in canonical
coordinates (rows old | N_h | N_s; columns old G K_n | B_{t,n} | B_{n,r} K_{>r}),
a block-triangular matrix, hence
    det R^G_{n+1} = +- det Gamma * det R^G_n * prod_{u,c,d} kappa_{u,c,d},
    kappa_{u,c,d} = [(v_uc(P) K_{>u}(P)) ^ v_nd(P)] / [v_uc(P) ^ v_nd(P)],
    P = L_uc cap L_nd,
with Gamma = prod over old unordered cross pairs of det K_n(P).

Checked exactly over Q (fmpq) at random product-form points:
  (G1) the ratio det R^G_{n+1} / (det Gamma det R^G_n prod kappa) is +-1;
  (G2) the N_h block of B_{n,r,d,b} K_{>r} is lower triangular in (u >= r) with
       diagonal 3x3 blocks equal to diag(kappa_{u,c,d}).
What this does not show: the equation-(24) family F (see the notes).
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, product_blocks, cross, kernel_at, matmul  # noqa: E402
from hq_fresh_words import build_cols, G_columns  # noqa: E402

Q = 3


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def wedge(x, y):
    return x[0] * y[1] - x[1] * y[0]


def tail(A, u, n_old, P, R):
    M = None
    for w in range(u + 1, n_old):
        K = kernel_at(A[w], P, R)
        M = K if M is None else matmul(M, K)
    return M


def kappa(A, n_old, u, c, d, R):
    new = n_old
    P = cross(A[u][c], A[new][d])
    vuc = [A[u][c][i] * P[i] for i in range(Q)]
    vnd = [A[new][d][i] * P[i] for i in range(Q)]
    T = tail(A, u, n_old, P, R)
    x = vuc if T is None else [sum(vuc[k] * T[k][j] for k in range(Q)) for j in range(Q)]
    return wedge(x, vnd) / wedge(vuc, vnd)


def detG(A, n, R):
    lab = G_columns(n)
    rows = build_cols(A, n, R, [c for _, c in lab])
    keys = [k for k, _ in lab]
    return flint.fmpq_mat([rows[k] for k in keys]).det(), rows, keys


def main():
    R = Ring(None)
    for n_old in (1, 2, 3, 4):
        for trial in range(2):
            A = product_blocks(n_old + 1, R, random.Random(1000 * n_old + trial), lo=1, hi=12)
            d_new, rows, keys = detG(A, n_old + 1, R)
            d_old = detG(A[:n_old], n_old, R)[0] if n_old >= 2 else flint.fmpq(1)
            gam = flint.fmpq(1)
            for (u, c), (v, e) in it.combinations([(t, a) for t in range(n_old) for a in range(Q)], 2):
                if u != v:
                    gam *= det3(kernel_at(A[n_old], cross(A[u][c], A[v][e]), R))
            kap = flint.fmpq(1)
            for u in range(n_old):
                for c in range(Q):
                    for d in range(Q):
                        kap *= kappa(A, n_old, u, c, d, R)
            ratio = d_new / (gam * d_old * kap)
            # (G2): N_h rows (new,u,d,c) on columns G_{new,r,d,b}
            new = n_old
            ok = True
            for d in range(Q):
                for (u, c) in [(u, c) for u in range(n_old) for c in range(Q)]:
                    for (r, b) in [(r, b) for r in range(n_old) for b in range(Q)]:
                        j = keys.index((new, r, d, b))
                        x = rows[(new, u, d, c)][j]
                        if u < r and x != 0:
                            ok = False
                        if u == r and b != c and x != 0:
                            ok = False
                        if u == r and b == c and x != kappa(A, n_old, u, c, d, R) and x != -kappa(A, n_old, u, c, d, R):
                            ok = False
            print(f'old blocks {n_old}, trial {trial}: det ratio = {ratio}  (G1 {"ok" if ratio in (1, -1) else "FAIL"}); '
                  f'(G2) triangular N_h block with kappa diagonal: {"ok" if ok else "FAIL"}', flush=True)


if __name__ == '__main__':
    main()
