#!/usr/bin/env python3
"""Independent cross-check of E1 through the project's canonical-coordinate code.

E1 (agent_per_e1): eps * L_B' ⊆ L_F' for the normalised canonical / DHW lattices.  With
R_n = canonical matrix (F_j = sum_i B_i R_ij mod E; hq_fresh_fast.R_matrix, rows and columns
both labelled (t,s,a,b)) and the normalisations n_(t,s,a,b) ~ eps^(1 + [a != b]), the
normalised matrix is the CONJUGATE  R' = D R_n D^{-1},  D = diag(eps^[a != b]).  Hence
    E1  <=>  all Smith exponents of R' lie in {0, 1}
(and then #ones = v(det R_n) = delta_n), whereas R_n itself has exponents in {0,1,2}.
Here eps = l = 10007 (l-adic valuations, hq_fresh_smith), persistence point from
hq_fresh_global_degen.make('persist') (g = D_0 + eps H; row scaling makes it I + eps H').
This uses cross-point (blown-up) coordinates only as a computational device; it is an
independent code path from the eps-series/evaluation method of agent_per_e1.
What this does not show: anything beyond the n run; l-adic valuations equal eps-orders
barring accidental cancellation mod l.
"""
import argparse
import random
import sys
import time
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, col_index  # noqa: E402
from hq_fresh_global_degen import make  # noqa: E402
from hq_fresh_smith import smith_exponents, summarize  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4])
    ap.add_argument('--l', type=int, default=10007)
    ap.add_argument('--seed', type=int, default=5)
    args = ap.parse_args()
    l = args.l
    for n in args.n:
        t0 = time.time()
        A = make('persist', n, l, random.Random(args.seed + 100 * n))
        R = R_matrix(A, n, Ring(None))
        labs = col_index(n)
        N = len(labs)
        w = [1 if a != b else 0 for (_, _, a, b) in labs]
        Rp = flint.fmpq_mat(N, N)
        for i in range(N):
            for j in range(N):
                x = R[i, j]
                if x != 0:
                    Rp[i, j] = x * flint.fmpq(l) ** (w[i] - w[j])
        eR = smith_exponents(R, l, K=60)
        eRp = smith_exponents(Rp, l, K=60)
        print(f'n={n}: Smith exponents of R_n: {summarize(eR)} (sum {sum(eR)}); '
              f'of R\' = D R_n D^-1: {summarize(eRp)} (sum {sum(eRp)}); '
              f'E1 <=> exponents of R\' in {{0,1}}: {set(eRp) <= {0, 1}}  [{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
