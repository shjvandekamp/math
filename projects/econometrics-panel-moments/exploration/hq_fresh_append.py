#!/usr/bin/env python3
"""Exact check of the append-at-the-end structure of R_{n+1}.

Blocks 0..n-1 are old, block n is appended as the LAST time, so every old
column F_{t,s,a,b} (t,s < n) acquires K_n as the final factor of its word.
Claims checked exactly (Fraction arithmetic, product-form blocks
A_t(a,i) = g(i,a) u_t(i), i.e. points of the Zariski closure of the
economic family):

 (A1) at every old cross point P (both lines old) the double residue of the
      appended old column is the old double residue times K_n(P):
          rho_P(F'_{t,s,a,b}) = rho_P(F_{t,s,a,b}) K_n(P);
      hence the old-row/old-column block of R_{n+1} is Gamma R_n with
      Gamma block diagonal (one 2x2 block per old unordered cross pair,
      the matrix of x -> x K_n(P) on the zero-sum plane, det = det K_n(P));
 (A2) at every new cross point P = L_{uc} cap L_{nd} the double residue of
      an old column is a multiple of v_{nd}(P): the new-head rows
      B_{n,u,d,c} vanish on all old columns.

What this does not show: anything about the remaining (new-column) block.
"""
import itertools as it
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hq_fresh_lib as lib  # noqa: E402

Q = 3


def product_blocks(n, rng):
    while True:
        g = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(n)]
        A = [[[Fraction(g[i][a] * us[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
        if lib.check_geometry(A, n)[0] and all(lib.det_fraction(A[t]) != 0 for t in range(n)):
            return A


def wedge(x, y):
    """Exterior coordinate on the zero-sum plane (coordinates 0,1)."""
    return x[0] * y[1] - x[1] * y[0]


def main():
    ns = [int(a) for a in sys.argv[1:]] or [2, 3]
    for n in ns:
        rng = random.Random(100 + n)
        A = product_blocks(n + 1, rng)
        old = A[:n]
        checked_a1 = checked_a2 = 0
        for (t, s) in [(t, s) for t in range(n) for s in range(n) if s != t]:
            for a, b in it.product(range(Q), repeat=2):
                # (A1) old cross points
                for (u, c), (v, d) in it.combinations([(w, e) for w in range(n) for e in range(Q)], 2):
                    if u == v:
                        continue
                    P = lib.cross(A[u][c], A[v][d])
                    r_old = lib.double_residue_of_F(old, n, t, s, a, b, u, c, v, d, P)
                    r_new = lib.double_residue_of_F(A, n + 1, t, s, a, b, u, c, v, d, P)
                    Kn = lib.kernel_at(A[n], P)
                    assert r_new == lib.vecmat(r_old, Kn), ('A1 fails', n, t, s, a, b, u, c, v, d)
                    checked_a1 += 1
                # (A2) new cross points
                for u in range(n):
                    for c, d in it.product(range(Q), repeat=2):
                        P = lib.cross(A[u][c], A[n][d])
                        r = lib.double_residue_of_F(A, n + 1, t, s, a, b, u, c, n, d, P)
                        vnd = [A[n][d][i] * P[i] for i in range(Q)]
                        assert wedge(r, vnd) == 0, ('A2 fails', n, t, s, a, b, u, c, d)
                        checked_a2 += 1
        print(f'n={n} -> n+1={n + 1}: (A1) {checked_a1} old-cross-point identities, '
              f'(A2) {checked_a2} new-cross-point proportionalities: all exact.')


if __name__ == '__main__':
    main()
