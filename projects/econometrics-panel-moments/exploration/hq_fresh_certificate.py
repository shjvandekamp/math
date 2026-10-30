#!/usr/bin/env python3
"""Finite certificate: det R_n != 0 at one genuine economic point, n = 2..N.

Economic point: pi_t(q,r) = exp(gamma_qr + x_t beta_q) with exp(gamma) = g (integers
below), exp(beta) = w = (1,3,7), x_t = t+1 (one-based block index).  R_n is built by
hq_fresh_fast (cross-checked entrywise against the Fraction implementation and, at
T <= 7, against the raw path matrix).  Full rank modulo p = 2^61-1 of the rational
matrix R_n (all denominators are p-units, else nmod division would fail) implies
det R_n != 0 over Q at this point, hence det R_n is not the zero function on the
economic domain.  With the proved reduction (lifts + quotient, L1-L2) and the
four-period base, this proves: the equation-(24) family is a basis of M_T for
every T <= N+2, for parameters in an open dense subset of the economic domain.
It proves nothing for larger T.
Usage: ../../../.venv/bin/python hq_fresh_certificate.py [N]   (default N = 12; N = 18 passes in ~2 min)
"""
import random
import sys
import time

from hq_fresh_fast import Ring, economic_blocks, geometry_ok, R_matrix

P = (1 << 61) - 1


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    R = Ring(P)
    rng = random.Random(3)
    g = [[rng.randint(2, 40) for _ in range(3)] for _ in range(3)]
    w = [1, 3, 7]
    print(f'economic point: g = {g}, u_t(q) = w_q^(t+1), w = {w}')
    allfull = True
    for n in range(2, N + 1):
        t0 = time.time()
        A = economic_blocks(n, R, g, w, [t + 1 for t in range(n)])
        assert geometry_ok(A, n), 'geometry conditions fail at this point'
        M = R_matrix(A, n, R)
        rk = M.rank()
        full = rk == M.nrows()
        allfull &= full
        print(f'n={n:2d} (T={n + 2:2d}): rank R_n = {rk}/{M.nrows()} {"FULL" if full else "DEFICIENT"}'
              f'  [{time.time() - t0:.1f}s]', flush=True)
    print('certificate', 'PASSED' if allfull else 'FAILED', f'for T <= {N + 2}')


if __name__ == '__main__':
    main()
