#!/usr/bin/env python3
"""Task (1), structure: the step versus the pole-order (valuation) filtration.

Valuation filtration of L_G'^(m)/eps L_G'^(m) in G'-coordinates mod eps:
  F_k := { alpha_0 : sum_{l<k} eps^l alpha_l . G' = O(eps^k) }   (constant coefficients of the
         elements of valuation >= k);  F_0 = C^d, dim F_k = d - dim Pi_{k-1} (A_k(L_G') = Pi_k).
It induces T_k := (F_k + Z1)/Z1 on T (the class of eps x, x in F_k) and M0_k on M_0 = C^d/Z0.
The step has two parts (agent_per2_step): P := pi(Im S00) = (V0 + Z1)/Z1 (order-0 image of the
new columns times eps) and Kp := Step(K0).  Printed per level k:
  dim gr_k T, dim gr_k P, dim gr_k Kp, and whether gr_k T = gr_k P (+) gr_k Kp
(i.e. T_k = (P ∩ T_k) (+) (Kp ∩ T_k) for all k: the decomposition is a FILTERED splitting and the
step is block-triangular with diagonal blocks gr_k P (+) gr_k Kp -> gr_k T).  Also the levels of
the order-0 image Im S00 in M_0 (pi preserves levels: P ∩ T_k vs Im S00 ∩ M0_k).
What this does not show: an explicit description of the diagonal blocks.
"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per2_lib import P, System, nm, order_coords  # noqa: E402
from agent_per2_step import colbasis, nullspace, rank, step_data  # noqa: E402


def valuation_filtration(rows, kmax):
    d, K1, M = rows.shape
    out = [np.eye(d, dtype=np.int64)]
    for k in range(1, kmax + 1):
        cs = [order_coords(M, mm) for mm in range(k)]
        assert all(len(c) == 2 * (3 * (mm + 1) ** 2 + 5) for mm, c in enumerate(cs)), 'too few points'
        offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
        C = np.zeros((int(offs[-1]), d * k), dtype=np.int64)
        for l in range(k):
            for mm in range(l, k):
                C[int(offs[mm]):int(offs[mm + 1]), l * d:(l + 1) * d] = rows[:, mm - l, cs[mm]].T
        X = nullspace(C)
        Fk = colbasis(X[:d, :] % P) if X.size else np.zeros((d, 0), dtype=np.int64)
        out.append(Fk)
        if Fk.shape[1] == 0:
            break
    return out


def dim_mod(A, Z):
    """dim of (span A + span Z)/span Z."""
    return rank(np.hstack([A, Z])) - Z.shape[1]


def dim_cap_mod(A, B, Z):
    """dim of ((A + Z) ∩ (B + Z))/Z."""
    return dim_mod(A, Z) + dim_mod(B, Z) - dim_mod(np.hstack([A, B]), Z)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, nargs='+', default=[5])
    ap.add_argument('--seed', type=int, default=101)
    args = ap.parse_args()
    for m in args.m:
        t0 = time.time()
        kmax = 2 * m
        res = step_data(m, args.seed, verbose=True)
        # rebuild the G' rows with enough points for the filtration (same model and seed)
        sysm = System(m, seed=args.seed, npts=max(9 * m * m // 2 + 30, 3 * (kmax + 1) ** 2 + 5), kinds=('G',))
        Fk = valuation_filtration(sysm.rows['G'], kmax)
        g0, g1, labG, labF = res['g']
        # recompute Z0, Z1, V0, StepK with the step's coordinates (same model => same G'-basis)
        N = m - 1
        L1 = [j for j, l in enumerate(labF) if l[0] == 'E' or (l[1] < N and l[2] < N)]
        new = [j for j, l in enumerate(labF) if l[0] == 'F' and (l[2] == N or l[1] == N)]
        Z0 = colbasis(g0[:, L1])
        kL1 = nullspace(g0[:, L1])
        Z1 = colbasis(np.hstack([Z0, np.array((nm(g1[:, L1]) * nm(kL1)).tolist(), dtype=np.int64)]))
        V0 = g0[:, new]
        V1 = g1[:, new]
        NS = nullspace(np.hstack([V0, g0[:, L1]]))
        StepK = (np.array((nm(V1) * nm(NS[:len(new)])).tolist(), dtype=np.int64)
                 + np.array((nm(g1[:, L1]) * nm(NS[len(new):])).tolist(), dtype=np.int64)) % P
        dimsF = [F.shape[1] for F in Fk]
        print(f'  dim F_k = {dimsF}  [{time.time() - t0:.0f}s]', flush=True)
        rows_out = []
        prevT = prevP = prevK = prevS = None
        levels = []
        for k, F in enumerate(Fk + [np.zeros((sysm.d, 0), dtype=np.int64)]):
            Tk = dim_mod(F, Z1) if F.shape[1] else 0
            PTk = dim_cap_mod(V0, F, Z1) if F.shape[1] else 0
            KTk = dim_cap_mod(StepK, F, Z1) if F.shape[1] else 0
            STk = dim_cap_mod(V0, F, Z0) if F.shape[1] else 0
            levels.append((k, Tk, PTk, KTk, STk))
        print('   k | dim T_k  dim(P∩T_k)  dim(Kp∩T_k)  dim(ImS00∩M0_k) | gr_k T = gr P + gr Kp ?')
        ok_all = True
        for i, (k, Tk, PTk, KTk, STk) in enumerate(levels[:-1]):
            _, Tn, Pn, Kn, Sn = levels[i + 1]
            grT, grP, grK = Tk - Tn, PTk - Pn, KTk - Kn
            ok = grT == grP + grK
            ok_all &= ok
            print(f'   {k} | {Tk:6d} {PTk:10d} {KTk:11d} {STk:14d}   | {grT:3d} = {grP:3d} + {grK:3d} : {ok}', flush=True)
            if Tk == 0:
                break
        print(f'  m={m}: filtered splitting T_k = (P∩T_k) (+) (Kp∩T_k) at every level: {ok_all}  '
              f'[{time.time() - t0:.0f}s]', flush=True)


if __name__ == '__main__':
    main()
