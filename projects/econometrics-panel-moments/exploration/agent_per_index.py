#!/usr/bin/env python3
"""Indices of the persistence lattices relative to their saturation; A_k(B') = Pi_k; delta_n.

For a C[[eps]]-lattice L of full rank in W_n(eps) (g = I + eps H), [L_sat : L] = sum of the
intrinsic Smith exponents (computed by agent_per_lib.saturate on eps-series evaluated at
random points; only the SUM of the greedy shifts is an invariant, not the multiset).

Checks:
 (I1) RAW families (E with B, G or DHW F, no normalisation): [L_sat : L] for B and G are
      EQUAL (the lattices coincide, L_G = L_B, consistent with Theorem A), and DHW exceeds
      them by the known canonical defect (30, 63 at n = 3, 4).  So G is as degenerate
      intrinsically as the canonical family B; it is "nondegenerate" only relative to B.
 (I2) NORMALISED families (agent_per_reduced.normalised_rows): A_k(L_B') ⊆ Pi_k is PROVED
      (each eps^i-coefficient of eta, beta has pole order <= i), so
      [L_sat : L_B'] = sum_k (d - dim A_k(B')) >= sum_k (d - dim Pi_k),
      with equality iff A_k(B') = Pi_k for every k.  The script compares the two sides.
 (I3) delta_n = [L_B' : L_F'] = [L_sat:L_F'] - [L_sat:L_B'] against 3(5n^2 - 9n - 2)/2.
 (I4) --lg: L_G' = L_B' for the NORMALISED lattices, by two exact containments
      (agent_per_e1.containment); needed in the inductive reduction (agent_per_induction).
What this does not show: anything for n not run; values are at one random point mod P
(the generic index can only be smaller than or equal to the value at a special point).
"""
import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import Model, PointSeries, family_rows, saturate  # noqa: E402
from agent_per_flatlimit import naive_basis  # noqa: E402
from agent_per_reduced import laurent_pole_filtration, normalised_rows  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--raw', type=int, nargs='*', default=[2, 3, 4])
    ap.add_argument('--n', type=int, nargs='*', default=[3, 4, 5, 6])
    ap.add_argument('--seed', type=int, default=41)
    ap.add_argument('--lg', type=int, nargs='*', default=[])
    args = ap.parse_args()
    for n in args.raw:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        K = 2 * n + 4
        m = Model(n, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(m, d // 2 + 20, K, seed=args.seed + 2)
        sums = {}
        for kind in ('B', 'G', 'F'):
            _, rows = family_rows(ps, kinds=(kind,))
            sums[kind] = int(saturate(rows, K)['shifts'].sum())
        print(f'(I1) n={n} raw families: [L_sat:L] B {sums["B"]}, G {sums["G"]}, F(DHW) {sums["F"]}; '
              f'B == G: {sums["B"] == sums["G"]}; F - B = {sums["F"] - sums["B"]}  [{time.time() - t0:.0f}s]',
              flush=True)
    for n in args.n:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        K = 2 * n + 4
        m = Model(n, seed=args.seed, hi=10 ** 6)
        info, basis = naive_basis(m)
        dims = [len(b) for b in laurent_pole_filtration(m, info, basis, 2 * n + 2)]
        pisum = sum(d - x for x in dims)
        ps = PointSeries(m, d // 2 + 20, K, seed=args.seed + 2)
        ind = {}
        for kind in ('B', 'G', 'F'):
            _, rows = normalised_rows(ps, kind)
            ind[kind] = int(saturate(rows[:, :K - 1, :].copy(), K - 2)['shifts'].sum())
        print(f'(I2) n={n}: dim Pi_k = {dims}; sum_k(d - dim Pi_k) = {pisum}; [L_sat:L_B\'] = {ind["B"]}, '
              f'[L_sat:L_G\'] = {ind["G"]}  -> A_k(B\') = Pi_k for all k: {pisum == ind["B"]}', flush=True)
        print(f'(I3) n={n}: delta_n = {ind["F"] - ind["B"]}; 3(5n^2-9n-2)/2 = {3 * (5 * n * n - 9 * n - 2) // 2}  '
              f'[{time.time() - t0:.0f}s]', flush=True)

    from agent_per_e1 import containment
    for n in args.lg:
        t0 = time.time()
        d = 9 * n * n - 6 * n
        K = 2 * n + 5
        m = Model(n, seed=args.seed, hi=10 ** 6)
        ps = PointSeries(m, max(d // 2 + 20, 3 * (2 * n + 3) ** 2 + 10), K, seed=args.seed + 2)
        _, Bn = normalised_rows(ps, 'B')
        _, Gn = normalised_rows(ps, 'G')
        Bn, Gn = Bn[:, :K - 1, :].copy(), Gn[:, :K - 1, :].copy()
        eB = int(saturate(Bn, K - 2)['shifts'].max())
        eG = int(saturate(Gn, K - 2)['shifts'].max())
        r1 = containment(Bn, Gn, eB)
        r2 = containment(Gn, Bn, eG)
        print(f'(I4) n={n}: L_G\' ⊆ L_B\': {r1[0] == r1[1]}; L_B\' ⊆ L_G\': {r2[0] == r2[1]}  [{time.time() - t0:.0f}s]',
              flush=True)


if __name__ == '__main__':
    main()
