#!/usr/bin/env python3
"""agent_col2 task (1): an explicit, order-free description of S_0 (collision u_N = u_0, delta = 0).

S_0 = span of the distinct delta = 0 members of the cyclic configuration (0, sigma(1..m-1), 0').  Ambient:
f = (X_i g_i / D_lim)_i, D_lim = D_0^2 prod_{t>=1} D_t, g_i of degree d = 3n (n = m+1), sum_i X_i g_i = 0.
Candidate local conditions (they involve only the lines of the blocks, never the time order):
  (a)  g_i(z) = 0 at the 6 base points z of every block t >= 1                        [standard, as in W_n]
  (b)  g_i in m_z^2 at the 3 interior base points z_cd = L_0c cap L_0d of block 0       [fat points]
  (c1) g_i(z_c) = 0 and d/dT g_i(z_c) = 0 at the boundary base points z_c = L_0c cap {X_c = 0}, T along {X_c=0}
  (c2) d/dL g_i(z_c) = 0 for i != c, L along L_0c                                       [phi1 of AGENT_COL 3.4]
  (c3) the eps^2-coefficient of (X_i g_i)(z_c + eps Q), Q on L_0c, is parallel to v_c(z_c)   [phi2]
S_loc := {g : syzygy, (a), (b), (c1), (c2), (c3)}.  Prints dim S_loc versus |fam| - 12 = dim S_0, whether every
family member satisfies every condition, and the dimensions obtained when single condition groups are
dropped (which conditions are needed).  Also: the flat-limit space (a)+(b)+(c1) (= nu-independent part).
Exact mod p = 2^61-1, one random product-form point per m.
What this does not show: a proof of the dimension formula; anything beyond the printed m.
"""
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, make_A, s_const)  # noqa: E402
from agent_col_cyclic import cyc_family  # noqa: E402
from agent_col2_lib import (monomials, eval_monomials, taylor_rows, g_functional, syzygy_rows, base_points,  # noqa
                            line_coeffs, other_point_on_line, Numerators, apply_rows, rank)


def conditions(A, m, d, rng):
    """Returns dict name -> list of functional rows on g (3 * #monomials)."""
    nm = len(monomials(d)[0])
    cond = {'a': [], 'b': [], 'c1': [], 'c2': [], 'c3': []}
    for t in range(1, m):
        inter, bound = base_points(A, t)
        for z in list(inter.values()) + list(bound.values()):
            ev = eval_monomials(d, z)
            for comp in range(Q):
                cond['a'].append(g_functional(d, comp, ev))
    inter, bound = base_points(A, 0)
    for (c, dd), z in inter.items():
        ev = eval_monomials(d, z)
        for comp in range(Q):
            cond['b'].append(g_functional(d, comp, ev))
        for _ in range(2):
            Y = [rng.randrange(1, P) for _ in range(Q)]
            rows = taylor_rows(d, z, Y, 2)
            for comp in range(Q):
                cond['b'].append(g_functional(d, comp, rows[1]))
    for c, z in bound.items():
        ev = eval_monomials(d, z)
        for comp in range(Q):
            cond['c1'].append(g_functional(d, comp, ev))
        e = [1 if i == c else 0 for i in range(Q)]
        T = other_point_on_line(e, rng) if False else None
        # a second point on {X_c = 0}
        T = [rng.randrange(1, P) for _ in range(Q)]
        T[c] = 0
        rowsT = taylor_rows(d, z, T, 2)
        for comp in range(Q):
            cond['c1'].append(g_functional(d, comp, rowsT[1]))
        Lc = line_coeffs(A, 0, c)
        Qp = other_point_on_line(Lc, rng)
        rowsL = taylor_rows(d, z, Qp, 3)
        for comp in range(Q):
            if comp != c:
                cond['c2'].append(g_functional(d, comp, rowsL[1]))
        # phi2: eps^2 coefficient of X_i g_i along z + eps Qp, i = 0, 1; wedge with v_c(z)
        v = [A[0][c][i][0] * z[i] % P for i in range(Q)]
        def coef2(comp):
            # [eps^2](X_comp g_comp)(z + eps Qp) = z_comp [eps^2] g + Qp_comp [eps^1] g
            return [(z[comp] * rowsL[2][k] + Qp[comp] * rowsL[1][k]) % P for k in range(nm)]
        r0 = g_functional(d, 0, coef2(0))
        r1 = g_functional(d, 1, coef2(1))
        cond['c3'].append([(r0[k] * v[1] - r1[k] * v[0]) % P for k in range(3 * nm)])
    return cond


def main(ms):
    for m in ms:
        t0 = time.time()
        n = m + 1
        d = 3 * n
        rng = random.Random(12000 + m)
        g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
        A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
        fam = cyc_family([0] + list(range(1, m)) + [0], n)
        num = Numerators(A, {0: 2, **{t: 1 for t in range(1, m)}}, d, rng)
        G = num.g_vectors(fam)
        syz = syzygy_rows(d)
        cond = conditions(A, m, d, rng)
        nm = len(monomials(d)[0])
        ok = {k: all(x == 0 for gv in G for x in apply_rows(rows, gv)) for k, rows in cond.items()}
        okz = all(x == 0 for gv in G for x in apply_rows(syz, gv))
        rG = rank(G)

        def dim_with(keys):
            rows = list(syz)
            for k in keys:
                rows += cond[k]
            return 3 * nm - rank(rows)

        allk = ['a', 'b', 'c1', 'c2', 'c3']
        dfull = dim_with(allk)
        dV0 = 3 * nm - rank(syz)
        target = 3 * n * (3 * n - 2) - 12
        print(f'm={m} (n={n}): |fam|-12 = {target}, rank of family numerators = {rG}; dim V_0 (syzygy) = {dV0}; '
              f'dim S_loc = {dfull}  [S_0 = S_loc: {dfull == rG == target}]', flush=True)
        print(f'   family satisfies: syzygy {okz}, ' + ', '.join(f'({k}) {v}' for k, v in ok.items()), flush=True)
        print(f'   independent conditions: (a) {rank(syz + cond["a"]) - rank(syz)}, '
              f'block 0 total {rank(syz + cond["a"] + cond["b"] + cond["c1"] + cond["c2"] + cond["c3"]) - rank(syz + cond["a"])}',
              flush=True)
        for drop in allk:
            keys = [k for k in allk if k != drop]
            print(f'   without ({drop}): dim = {dim_with(keys)}', flush=True)
        print(f'   flat-limit conditions (a)+(b)+(c1): dim = {dim_with(["a", "b", "c1"])} (|fam|-6 = {target + 6})  '
              f'[{time.time() - t0:.1f}s]', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [4, 5])
