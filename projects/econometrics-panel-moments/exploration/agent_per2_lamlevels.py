#!/usr/bin/env python3
"""Task (2): the leading head map Lambda'_n(.)(0) along the pole-order (valuation) filtration.

F_k^(n) := constant G'-coefficients of the elements of L_G'^(n) of valuation >= k
(agent_per2_stepstruct.valuation_filtration).  The step only needs Lambda'_n(0) through the
classes eps x K_N, and its target sits at the top levels, so the question is whether
Lambda'_n(0) is simple on F_k for large k.  Prints, for each k: dim F_k,
rank(Lambda'_n(0) restricted to F_k), and rank of the first-order E-coefficient sums
(sum_s gamma1_{s,a}) on F_k.  Also the rank of Lambda'_n(0) on F_k modulo the explicit head
values of L_F'^(n) is not a meaningful quotient (they span all heads), so it is not printed.
What this does not show: a formula for the nonzero part.
"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per2_lib import P, System, coords_peel, nm, shift  # noqa: E402
from agent_per2_headmap0 import head_maps  # noqa: E402
from agent_per2_stepstruct import valuation_filtration  # noqa: E402
from agent_per2_step import rank  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--seed', type=int, default=101)
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        kmax = 2 * n + 1
        npts = max(9 * n * n // 2 + 30, 3 * (kmax + 1) ** 2 + 5)
        sysn = System(n, seed=args.seed, npts=npts, kinds=('F', 'G'))
        eF = sysn.emax('F')
        if sysn.K < 2 * eF + 4:
            sysn = System(n, seed=args.seed, K=2 * eF + 4, npts=npts, kinds=('F', 'G'))
        F, G = sysn.rows['F'], sysn.rows['G']
        gam = coords_peel(F, shift(G, 1), 2)
        heads, L0, L1, E0, E1 = head_maps(sysn, gam, sysn.lab['F'])
        Fk = valuation_filtration(G, kmax)
        out = []
        for k, B in enumerate(Fk):
            if B.shape[1] == 0:
                out.append((k, 0, 0, 0))
                break
            rl = rank(np.array((nm(L1) * nm(B)).tolist(), dtype=np.int64))
            re = rank(np.array((nm(E1) * nm(B)).tolist(), dtype=np.int64))
            out.append((k, B.shape[1], rl, re))
        print(f'n={n}: (k, dim F_k, rank Lambda\'(0)|F_k, rank Esum1|F_k) = {out}  [{time.time() - t0:.0f}s]',
              flush=True)


if __name__ == '__main__':
    main()
