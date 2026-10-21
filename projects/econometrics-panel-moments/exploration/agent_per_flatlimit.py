#!/usr/bin/env python3
"""Task 2a: the flat limit W^0 of W_n under g = I + eps H, as an explicit space.

As eps -> 0, D(eps) = prod_{t,a} u_t(a) (X_a + eps lam_ta) -> D_0 = c (X0 X1 X2)^n and the
6n base points of W_n degenerate to
  * P_ta = {X_a = 0, lam_ta = 0}  (FIXED points: n on each coordinate line), and
  * the n within-block points l_ta ∩ l_tb  ->  vertex e_c ({a,b,c} = {0,1,2}); in local
    coordinates (X_a, X_b) at X_c = 1 they are eps q_t + O(eps^2), q_t = (-c_{t,a,c}, -c_{t,b,c}).
    Their limit scheme zeta_c has the inverse system spanned by the functionals
    G -> sum_t alpha_t G_j(q_t), alpha orthogonal to all monomials of degree < j at the q_t
    (G_j = local degree-j part).
NAIVE LIMIT SPACE  N^naive := {(g_0,g_1,g_2) in S_3n^3 : sum X_i g_i = 0, g_i in I(Z_0)}, and
W^naive := D_0^{-1} N^naive  (vectors (X_i g_i / (X0X1X2)^n)_i, Laurent polynomials).

Checks:
 (N1) dim N^naive = 9n^2 - 6n  (n = 1..14): the 12n limit conditions are independent, which
      PROVES W^0 = W^naive for that n (W^0 ⊆ W^naive by semicontinuity of the incidence
      conditions, equality by dimension).  The check is mod P at one random point with
      parameters of size up to 1e8.  (With SMALL integer parameters, e.g. up to 60, two
      blocks can share a ratio u_t(c)/u_t(b), so two points P_ta coincide and the naive
      space is too big: such excesses of 2 or 4 were seen at n = 9..12 and are artefacts.)
 (N2) cross-check with the saturation of the DHW (and B) family: the leading rows of the
      saturated family, evaluated at random points, span the same space as W^naive
      evaluated at the same points (n = 2, 3, 4).
What this does not show: the dimension statement for n > 10, or anything about DHW.
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Q, Model, PointSeries, family_rows, saturate, rank, inv  # noqa: E402


def monomials(deg):
    return [(i, j, deg - i - j) for i in range(deg + 1) for j in range(deg + 1 - i)]


def vertex_functionals(model, c, deg):
    """Inverse system of zeta_c on forms of degree deg: list of dicts monomial -> coeff."""
    n = model.n
    a, b = [x for x in range(Q) if x != c]
    qs = [((-model.c[t][a][c]) % P, (-model.c[t][b][c]) % P) for t in range(n)]
    funcs = []
    total = 0
    j = 0
    while total < n:
        # alpha orthogonal to all monomials of local degree < j at the q_t
        lower = [(p, q) for d in range(j) for p in range(d + 1) for q in [d - p]]
        if lower:
            Mrows = [[pow(qt[0], p, P) * pow(qt[1], q, P) % P for qt in qs] for (p, q) in lower]
            Mt = flint.nmod_mat(Mrows, P)
            X, nul = Mt.nullspace()
            alphas = [[int(X[i, k]) for i in range(n)] for k in range(nul)]
        else:
            alphas = [[1] * n] + [[1 if i == k else 0 for i in range(n)] for k in range(1, n)]
            alphas = [[1 if i == k else 0 for i in range(n)] for k in range(n)]
        # functional on local degree-j part: sum_t alpha_t G_j(q_t)
        cand = []
        for al in alphas:
            f = {}
            for p in range(j + 1):
                q = j - p
                v = sum(al[t] * pow(qs[t][0], p, P) * pow(qs[t][1], q, P) for t in range(n)) % P
                if v:
                    mono = [0, 0, 0]
                    mono[a], mono[b], mono[c] = p, q, deg - j
                    f[tuple(mono)] = v
            cand.append(f)
        # keep an independent set (as vectors on the j+1 local monomials)
        basis_rows = []
        for f in cand:
            row = []
            for p in range(j + 1):
                mono = [0, 0, 0]
                mono[a], mono[b], mono[c] = p, j - p, deg - j
                row.append(f.get(tuple(mono), 0))
            if any(row):
                trial = basis_rows + [row]
                if flint.nmod_mat(trial, P).rank() == len(trial):
                    basis_rows.append(row)
                    funcs.append(f)
        total += len(basis_rows)
        j += 1
    return funcs


def naive_space(model):
    """Returns (unknown index, kernel basis as list of (g0,g1,g2) dicts), and dims."""
    n = model.n
    deg = 3 * n
    mons = monomials(deg)
    idx = {}
    for i in range(Q):
        for m in mons:
            idx[(i, m)] = len(idx)
    N = len(idx)
    eqs = []
    # (Z) sum_i X_i g_i = 0
    for m in monomials(deg + 1):
        row = {}
        for i in range(Q):
            if m[i] >= 1:
                mm = list(m)
                mm[i] -= 1
                row[idx[(i, tuple(mm))]] = 1
        eqs.append(row)
    # (P) g_i(P_ta) = 0
    for t in range(n):
        for a in range(Q):
            b, c = [x for x in range(Q) if x != a]
            pt = [0, 0, 0]
            pt[b], pt[c] = model.c[t][a][c], (-model.c[t][a][b]) % P
            for i in range(Q):
                row = {}
                for m in mons:
                    v = pow(pt[0], m[0], P) * pow(pt[1], m[1], P) * pow(pt[2], m[2], P) % P
                    if v:
                        row[idx[(i, m)]] = v
                eqs.append(row)
    # (V) vertex schemes, applied to all three components
    for c in range(Q):
        for f in vertex_functionals(model, c, deg):
            for i in range(Q):
                eqs.append({idx[(i, m)]: v for m, v in f.items()})
    M = flint.nmod_mat([[r.get(j, 0) for j in range(N)] for r in eqs], P)
    rk = M.rank()
    return dict(N=N, rank=rk, dim=N - rk, M=M, idx=idx, mons=mons)


def naive_basis(model):
    info = naive_space(model)
    X, nul = info['M'].nullspace()
    N = info['N']
    basis = [[int(X[i, k]) for i in range(N)] for k in range(nul)]
    return info, basis


def eval_naive(model, info, basis, Xpts):
    """Evaluate v = (X_i g_i / (X0X1X2)^n) at points; rows (components 1, 2)."""
    n = model.n
    idx, mons = info['idx'], info['mons']
    pts = [[int(x) for x in X] for X in Xpts]
    out = []
    for vec in basis:
        r1, r2 = [], []
        for X in pts:
            D = pow(X[0] * X[1] % P * X[2] % P, n, P)
            Di = inv(D)
            comps = []
            for i in range(Q):
                s = 0
                for m in mons:
                    cf = vec[idx[(i, m)]]
                    if cf:
                        s += cf * pow(X[0], m[0], P) * pow(X[1], m[1], P) % P * pow(X[2], m[2], P)
                comps.append(s % P * X[i] % P * Di % P)
            r1.append(comps[1])
            r2.append(comps[2])
        out.append(r1 + r2)
    return np.array(out, dtype=np.int64)


def main():
    print('(N1) dim N^naive vs 9n^2 - 6n:')
    for n in range(1, 15):
        m = Model(n, seed=100 + n, hi=10 ** 8)
        info = naive_space(m)
        print(f'  n={n}: unknowns {info["N"]}, rank {info["rank"]}, dim {info["dim"]}, '
              f'9n^2-6n = {9 * n * n - 6 * n}  {"OK" if info["dim"] == 9 * n * n - 6 * n else "MISMATCH"}',
              flush=True)
    print('(N2) saturated leading rows (DHW and B families) vs W^naive at the same points:')
    for n in (2, 3, 4):
        d = 9 * n * n - 6 * n
        m = Model(n, seed=11, hi=10 ** 6)
        K = 10
        ps = PointSeries(m, d // 2 + 12, K, seed=5)
        info, basis = naive_basis(m)
        Wn = eval_naive(m, info, basis, ps.X)
        rW = rank(Wn)
        for kind in ('B', 'F'):
            labels, rows = family_rows(ps, kinds=(kind,))
            res = saturate(rows, K)
            Lead = res['lead']
            rL = rank(Lead)
            rboth = rank(np.vstack([Lead, Wn]))
            print(f'  n={n} {kind}: rank(lead) {rL}, rank(W^naive eval) {rW}, rank(both) {rboth}  '
                  f'{"SAME SPACE" if rL == rW == rboth == d else "DIFFERENT"}', flush=True)


if __name__ == '__main__':
    main()
