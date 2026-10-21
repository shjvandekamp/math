#!/usr/bin/env python3
"""Task 4 probe: where do the new canonical vectors come from when the latest block N is appended?

System with m = n+1 blocks, N = n the newest.  Normalised DHW sub-lattices:
  L1 = span{eta_all, F'_{t,s} : t,s < N}         (= Phi_n(L_F'^(n)) + eta: the appended old columns)
  L2 = L1 + span{F'_{t,N}}                       (old head, new first letter;  F'_{t,N} - Phi_n(I'_t)
                                                  = normalised commutator h_tab [Pi_(t), K_N])
  L3 = L1 + span{F'_{N,s}}                       (new head)
  L  = all of L_F'^(m).
Tested (exact membership mod P via agent_per_e1.containment; X := targets):
  (ii)   eps * B'_{t,N,a,b}  in L2 ?   in L1 ?   in L ?
  (iii)  eps * B'_{N,s,a,b}  in L3 ?   in L1 ?   in L ?
  (old)  eps * B'_{t,s,a,b} (t,s<N) in L ?  and in L1 + eps*span{B'_{t,N}} ?
         (the latter is what E1(n) + (*)(n) give through the append map)
Every lattice used contains eps^(e_B+2) L_sat only after adding eps^2 L_B'; to keep the
truncation valid each test is run against  (lattice) + eps^2 L_B'^(m)  (marked "+e2B"),
and against the lattice itself only when it contains L_F' (so eps^e L_sat ⊆ it).
What this does not show: a proof of any of the containments.
"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import Model, PointSeries, saturate  # noqa: E402
from agent_per_reduced import normalised_rows  # noqa: E402
from agent_per_e1 import containment  # noqa: E402


def shift(rows, k):
    out = np.zeros_like(rows)
    out[:, k:, :] = rows[:, :rows.shape[1] - k, :]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--seed', type=int, default=31)
    args = ap.parse_args()
    for mblk in args.m:
        t0 = time.time()
        N = mblk - 1
        d = 9 * mblk * mblk - 6 * mblk
        emax_guess = 2 * mblk + 2
        K = emax_guess + 5
        npts = max(d // 2 + 12, 3 * (emax_guess + 2) ** 2 + 10)
        mod = Model(mblk, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(mod, npts, K, seed=args.seed + 1)
        labF, F = normalised_rows(ps, 'F')
        labB, B = normalised_rows(ps, 'B')
        F = F[:, :K - 1, :].copy()
        B = B[:, :K - 1, :].copy()
        eF = int(saturate(F, K - 2)['shifts'].max())
        eB = int(saturate(B, K - 2)['shifts'].max())
        e2 = eB + 2
        sel = lambda labs, pred: [i for i, l in enumerate(labs) if pred(l)]  # noqa: E731
        iE = sel(labF, lambda l: l[0] == 'E')
        iold = sel(labF, lambda l: l[0] == 'F' and l[1] < N and l[2] < N)
        itN = sel(labF, lambda l: l[0] == 'F' and l[2] == N)
        iNs = sel(labF, lambda l: l[0] == 'F' and l[1] == N)
        L1 = F[iE + iold]
        L2 = F[iE + iold + itN]
        L3 = F[iE + iold + iNs]
        e2B = shift(B, 2)
        jtN = sel(labB, lambda l: l[0] == 'B' and l[2] == N)
        jNs = sel(labB, lambda l: l[0] == 'B' and l[1] == N)
        jold = sel(labB, lambda l: l[0] == 'B' and l[1] < N and l[2] < N)
        epsB = shift(B, 1)
        X_ii, X_iii, X_old = epsB[jtN], epsB[jNs], epsB[jold]
        assert len(jtN) == 9 * N and len(jNs) == 9 * N and len(jold) == 9 * N * (N - 1)

        def test(L, X, with_e2B=True):
            Lr = np.concatenate([L, e2B]) if with_e2B else L
            e = e2 if with_e2B else eF
            r = containment(Lr, X, e)
            return r[0] == r[1]
        res = {
            '(ii) in L2+e2B': test(L2, X_ii), '(ii) in L1+e2B': test(L1, X_ii), '(ii) in L': test(F, X_ii, False),
            '(iii) in L3+e2B': test(L3, X_iii), '(iii) in L1+e2B': test(L1, X_iii), '(iii) in L': test(F, X_iii, False),
            '(old) in L': test(F, X_old, False),
            '(old) in L1+eps*B_tN+e2B': test(np.concatenate([L1, epsB[jtN]]), X_old),
        }
        print(f'm={mblk} blocks (append to n={N}): eF={eF}, eB={eB}  [{time.time() - t0:.0f}s]')
        for k, v in res.items():
            print(f'    {k:28s}: {v}', flush=True)


if __name__ == '__main__':
    main()
