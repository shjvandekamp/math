#!/usr/bin/env python3
"""Task (2)/(3): the leading head map Lambda'_n(.)(0) on L_B' = L_G', and condition (**).

For every generator x of L_B'^(n) (eta, beta) and of L_G'^(n) (eta, G'), compute the F'/eta
coordinates of eps*x modulo eps^2 (E1(n) says eps*x in L_F'), by agent_per2_lib.coords_peel.
With alpha = alpha0 + eps alpha1 (F'-coefficients), gamma = gamma0 + eps gamma1 (eta-coefficients):
  Lambda'(eps x)_{tab} = sum_s alpha_{tsab} - [a=b] gamma_ta - [a!=b] eps c_tab gamma_ta, so
  order 0:  sum_s alpha0_{tsab} - [a=b] gamma0_ta          (= 0 is condition (*))
  order 1:  Lambda'(x)(0)_{tab} = sum_s alpha1_{tsab} - [a=b] gamma1_ta - [a!=b] c_tab gamma0_ta.
(**) (E-coefficient sums regular, needed to propagate (*) through AG 1.2): sum_s gamma0_{s,a} = 0.
Structure tests on the 9n x d matrix Lambda'(.)(0):
  * support of each column (which heads (t,a,b) are hit), against the generator's own head;
  * G'-columns: is Lambda'(G'_{t,r,a,b})(0) a multiple of e_{tab}?  (sum over r is e_{tab}
    exactly, since sum_r G'_{t,r} = I'_t = F'_{t,s_min(t)})
  * rank, density.
What this does not show: a formula, unless the structure tests say so; one random point mod P.
"""
import argparse
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per2_lib import P, Q, System, coords_peel, nm, shift  # noqa: E402


def head_maps(sysn, gam, labF):
    n = sysn.m
    heads = [(t, a, b) for t in range(n) for a in range(Q) for b in range(Q)]
    hpos = {h: i for i, h in enumerate(heads)}
    nt = gam.shape[2]
    L0 = np.zeros((len(heads), nt), dtype=np.int64)
    L1 = np.zeros((len(heads), nt), dtype=np.int64)
    Esum0 = np.zeros((Q, nt), dtype=np.int64)
    Esum1 = np.zeros((Q, nt), dtype=np.int64)
    c = sysn.model.c
    for i, lab in enumerate(labF):
        if lab[0] == 'F':
            _, t, s, a, b = lab
            L0[hpos[(t, a, b)]] += gam[0][i]
            L1[hpos[(t, a, b)]] += gam[1][i]
        else:
            _, s, a = lab
            L0[hpos[(s, a, a)]] -= gam[0][i]
            L1[hpos[(s, a, a)]] -= gam[1][i]
            for b in range(Q):
                if b != a:
                    L1[hpos[(s, a, b)]] -= (c[s][a][b] * gam[0][i]) % P
            Esum0[a] += gam[0][i]
            Esum1[a] += gam[1][i]
    return heads, L0 % P, L1 % P, Esum0 % P, Esum1 % P


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--seed', type=int, default=101)
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        sysn = System(n, seed=args.seed, K=None, npts=9 * n * n // 2 + 30)
        # precision for peeling: K >= 2*smax + 3 (smax = max shift of F')
        eF = sysn.emax('F')
        if sysn.K < 2 * eF + 4:
            sysn = System(n, seed=args.seed, K=2 * eF + 4, npts=9 * n * n // 2 + 30)
        F = sysn.rows['F']
        out = {}
        for kind in ('B', 'G'):
            X = sysn.rows[kind]
            gam = coords_peel(F, shift(X, 1), 2)
            heads, L0, L1, E0, E1 = head_maps(sysn, gam, sysn.lab['F'])
            out[kind] = (heads, L0, L1, E0, E1)
        print(f'n={n}: eF={eF}, K={sysn.K}  [{time.time() - t0:.0f}s]', flush=True)
        for kind in ('B', 'G'):
            heads, L0, L1, E0, E1 = out[kind]
            labs = sysn.lab[kind]
            hpos = {h: i for i, h in enumerate(heads)}
            print(f'  {kind}: (*) order-0 head sums zero: {not L0.any()}; (**) E-coefficient sums zero mod eps: '
                  f'{not E0.any()}; rank Lambda\'(0) = {nm(L1).rank()}, density {np.count_nonzero(L1) / L1.size:.3f}',
                  flush=True)
            # support analysis
            own_only, own_head_only, sizes = 0, 0, Counter()
            ncols = 0
            for j, lab in enumerate(labs):
                col = L1[:, j]
                sup = [heads[i] for i in np.nonzero(col)[0]]
                if lab[0] == 'E':
                    _, s, a = lab
                    ok = sup == [(s, a, a)] and col[hpos[(s, a, a)]] == P - 1
                    own_only += ok
                    continue
                ncols += 1
                _, t, r, a, b = lab
                sizes[len(sup)] += 1
                if all(h == (t, a, b) for h in sup):
                    own_only += 1
                if all(h[0] == t for h in sup):
                    own_head_only += 1
            print(f'    columns with support exactly own (t,a,b) [eta: = -e_(s,a,a)]: {own_only}/{len(labs)}; '
                  f'support inside own head block t: {own_head_only}/{ncols}; support sizes {dict(sorted(sizes.items()))}',
                  flush=True)
            if kind == 'G':
                # values of the own-head entry for G'_{t,r,a,b}, grouped by (t, r)
                vals = {}
                for j, lab in enumerate(labs):
                    if lab[0] == 'G':
                        _, t, r, a, b = lab
                        vals.setdefault((t, r), set()).add(int(L1[hpos[(t, a, b)], j]))
                nsingle = sum(1 for v in vals.values() if len(v) == 1)
                print(f'    G\': own-head entry constant in (a,b) for fixed (t,r): {nsingle}/{len(vals)} pairs', flush=True)


if __name__ == '__main__':
    main()
