#!/usr/bin/env python3
"""Task (2) in the form that matters for the step: does the generic part of Lambda'_n(0) enter?

In m-system G'-coordinates mod eps (agent_per2_step), the denominator Z1 contains the graph of
Lambda'_n(0) over the old coordinates O = {eta_s, G'_{t,r} : s, t, r < N} (because
eps L_B'^(n), appended, lies in L1).  Lambda'_n(0) is explicit only on the explicit part
X := O-components of Z0 = Im Psi_0^(n) (order-0 coordinates of the appended old DHW columns and
eta's, on which the head values are units / -e_(s,a,a)).
Canonical part of the step's source: the order-0 coordinates g0(v) of the 18n new columns.
Test: are their O-components inside X?  (If yes, the pi-part of the step only uses explicit
head values.)  Prints dim X, dim O, and rank of [X | O-components of g0(new)] - dim X, also
split by new-column type F'_{t,N} / F'_{N,s}.
With --levels: the level filtration of the excess space E = (X + Y)/X, using the valuation
filtration F_k^(n) of the OLD system (same model restricted to the first n blocks; same label
order): dim((X + Y) ∩ (X + F_k)) - dim X for each k.
What this does not show: the K0-part, whose old components are only defined modulo the full graph.
"""
import argparse
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per2_step import colbasis, rank, step_data  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, nargs='+', default=[5, 6])
    ap.add_argument('--seed', type=int, default=101)
    ap.add_argument('--levels', action='store_true')
    args = ap.parse_args()
    for m in args.m:
        res = step_data(m, args.seed, verbose=False)
        g0, g1, labG, labF = res['g']
        N = m - 1
        O = [i for i, l in enumerate(labG) if (l[0] == 'E' and l[1] < N) or (l[0] == 'G' and l[1] < N and l[2] < N)]
        L1 = [j for j, l in enumerate(labF) if l[0] == 'E' or (l[1] < N and l[2] < N)]
        tN = [j for j, l in enumerate(labF) if l[0] == 'F' and l[2] == N]
        Ns = [j for j, l in enumerate(labF) if l[0] == 'F' and l[1] == N]
        X = colbasis(g0[np.ix_(O, L1)])
        dX = X.shape[1]
        out = {}
        for name, cols in (('all new', tN + Ns), ('F_tN', tN), ('F_Ns', Ns)):
            Y = g0[np.ix_(O, cols)]
            out[name] = rank(np.hstack([X, Y])) - dX
        print(f'm={m}: dim O = {len(O)}, dim X (explicit part) = {dX}; excess rank of the new columns\' order-0 '
              f'old components beyond X: {out}', flush=True)
        if args.levels:
            from agent_per2_lib import System
            from agent_per2_stepstruct import valuation_filtration, dim_cap_mod
            n = N
            kmax = 2 * n + 1
            sysn = System(n, seed=args.seed, npts=max(9 * n * n // 2 + 30, 3 * (kmax + 1) ** 2 + 5), kinds=('G',))
            assert [l for l in sysn.lab['G']] == [labG[i] for i in O], 'label order mismatch'
            Fk = valuation_filtration(sysn.rows['G'], kmax)
            Y = g0[np.ix_(O, tN + Ns)]
            XY = np.hstack([X, Y])
            lev = []
            for k, Fb in enumerate(Fk):
                if Fb.shape[1] == 0:
                    lev.append((k, 0))
                    break
                lev.append((k, dim_cap_mod(XY, Fb, X)))
            print(f'   levels of the excess E: (k, dim E ∩ (X + F_k)/X) = {lev}', flush=True)


if __name__ == '__main__':
    main()
