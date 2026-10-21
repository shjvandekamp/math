#!/usr/bin/env python3
"""Task 3b: the leading map Psi_0 of the Smith-reduced DHW problem.

Psi_0 : span_C(normalised DHW family) -> L_B' / eps L_B'  (B'-coordinates at eps = 0).
Under E1 (eps L_B' ⊆ L_F'), L_F' = Psi_0^{-1}(Im Psi_0) and rank Psi_0 = d - delta_n.
The DHW family is split as in the project (HQ brief, "Lambda-free filtration"):
    eta_sb,   I'_{t,a,b} := F'_{t,s_min(t),a,b} (= sum_r G'_{t,r,a,b}),
    D'_{t,s,a,b} := F'_{t,s,a,b} - F'_{t,s_min(t),a,b}   (s != s_min(t)),
and D' is split by a = b / a != b and by whether t < s.
rank Psi_0|_S = rank[S | eps*B' Toeplitz] - rank[eps*B' Toeplitz]  (orders 0..eB, exact mod P;
eps^(eB+1) L_sat ⊆ eps L_B').
Prints the ranks for the nested subfamilies and compares with 12n and
f(n) = 3(n^2 + 5n + 2)/2 = 12n + 3 C(n-1, 2).
With --classes: tests of naive descriptions of the D'-classes modulo eps L_B':
  (C1) independence of the head state a  (rank of D'_{t,s,a,b} - D'_{t,s,0,b});
  (C2) independence of the head t for t > s (rank of D'_{t,s,a,b} - D'_{t',s,a,b});
  (C3) pair-locality: the single-commutator columns D'_{t,s2(t),a,b} = h_tab [K_smin, K_s2] K_{>s2}
       (s2(t) = second smallest block != t): rank per head and union over heads with the same pair.
What this does not show: why the ranks are what they are.
"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Model, PointSeries, saturate  # noqa: E402
from agent_per_reduced import normalised_rows  # noqa: E402
from agent_per_e1 import nm, order_coords  # noqa: E402


def psi0_rank(S, B, eB):
    """S: (k, orders, M) DHW-type rows; B: canonical rows. Returns rank of S modulo eps L_B'."""
    d, _, M = B.shape
    e = eB + 1
    cs = [order_coords(M, mm) for mm in range(e)]
    offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
    nrow = int(offs[-1])
    TB = np.zeros((nrow, d * e), dtype=np.int64)       # eps^(l+1) B'_i, l = 0..e-1
    TS = np.zeros((nrow, S.shape[0]), dtype=np.int64)
    for mm in range(e):
        r0, r1 = int(offs[mm]), int(offs[mm + 1])
        for l in range(e):
            o = mm - l - 1
            if o >= 0:
                TB[r0:r1, l * d:(l + 1) * d] = B[:, o, cs[mm]].T
        TS[r0:r1, :] = S[:, mm, cs[mm]].T
    rB = nm(TB).rank()
    rSB = nm(np.hstack([TS, TB])).rank()
    return rSB - rB


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, nargs='+', default=[3, 4, 5])
    ap.add_argument('--seed', type=int, default=51)
    ap.add_argument('--classes', action='store_true')
    args = ap.parse_args()
    for n in args.n:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        K = 2 * n + 6
        npts = max(d // 2 + 12, 3 * (2 * n + 3) ** 2 + 10)
        m = Model(n, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(m, npts, K, seed=args.seed + 1)
        lab, F = normalised_rows(ps, 'F')
        _, B = normalised_rows(ps, 'B')
        F = F[:, :K - 1, :].copy()
        B = B[:, :K - 1, :].copy()
        eB = int(saturate(B, K - 2)['shifts'].max())
        pos = {l: i for i, l in enumerate(lab)}
        smin = {t: min(u for u in range(n) if u != t) for t in range(n)}
        eta = F[[pos[('E', s, a)] for s in range(n) for a in range(3)]]
        I = F[[pos[('F', t, smin[t], a, b)] for t in range(n) for a in range(3) for b in range(3)]]
        Dl = [(t, s, a, b) for t in range(n) for s in range(n) if s not in (t, smin[t])
              for a in range(3) for b in range(3)]
        D = np.array([(F[pos[('F', t, s, a, b)]] - F[pos[('F', t, smin[t], a, b)]]) % P for (t, s, a, b) in Dl])
        Ddiag = D[[i for i, l in enumerate(Dl) if l[2] == l[3]]]
        Doff = D[[i for i, l in enumerate(Dl) if l[2] != l[3]]]
        r = {}
        r['eta'] = psi0_rank(eta, B, eB)
        r['eta+I'] = psi0_rank(np.concatenate([eta, I]), B, eB)
        r['eta+I+Ddiag'] = psi0_rank(np.concatenate([eta, I, Ddiag]), B, eB)
        r['eta+I+Doff'] = psi0_rank(np.concatenate([eta, I, Doff]), B, eB)
        r['all'] = psi0_rank(F, B, eB)
        r['D alone'] = psi0_rank(D, B, eB)
        f = 3 * (n * n + 5 * n + 2) // 2
        print(f'n={n}: ' + ', '.join(f'{k} {v}' for k, v in r.items())
              + f'  | 3n={3 * n}, 12n={12 * n}, f(n)={f}, #D={len(Dl)}  [{time.time() - t0:.0f}s]', flush=True)
        if args.classes:
            Dd = {l: D[i] for i, l in enumerate(Dl)}
            C1 = np.array([(Dd[(t, s, a, b)] - Dd[(t, s, 0, b)]) % P for (t, s, a, b) in Dl if a != 0])
            C2 = [(Dd[(t, s, a, b)] - Dd[(t2, s, a, b)]) % P for (t, s, a, b) in Dl for t2 in range(n)
                  if t2 > t > s and (t2, s, a, b) in Dd]
            c2 = psi0_rank(np.array(C2), B, eB) if C2 else 'n/a'
            print(f'   (C1) a-independence: rank {psi0_rank(C1, B, eB)} (0 would mean independent); '
                  f'(C2) t-independence for t > s: rank {c2}', flush=True)
            others = {t: [u for u in range(n) if u != t] for t in range(n)}
            bypair = {}
            for t in range(n):
                s2 = others[t][1]
                rows = np.array([Dd[(t, s2, a, b)] for a in range(3) for b in range(3)])
                bypair.setdefault((others[t][0], s2), []).append((t, rows))
            for pair, lst in sorted(bypair.items()):
                per = [psi0_rank(rr, B, eB) for _, rr in lst]
                uni = psi0_rank(np.concatenate([rr for _, rr in lst]), B, eB)
                print(f'   (C3) pair {pair}: heads {[t for t, _ in lst]}, rank per head {per}, union {uni}', flush=True)


if __name__ == '__main__':
    main()
