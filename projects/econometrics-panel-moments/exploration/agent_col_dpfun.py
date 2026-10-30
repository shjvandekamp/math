#!/usr/bin/env python3
"""agent_col task 2: the double-pole coefficients along a doubled line L_{0c} as exact rational functions.

Parametrise L_{0c} by X0(theta) = Q1 + theta Q2 (Q1, Q2 on L_{0c}), fix a transverse direction Yd, and
compute dp_c(f)(theta) = coefficient of eps^-2 of f(X0(theta) + eps Yd) for f a delta = 0 family member or a
jet; reconstruct alpha_c (longitudinal, v_{0c}-coefficient) and tau_c (transverse) as rational functions of
theta (mod p = 2^61-1) and locate their poles and zeros among the special points of L_{0c}:
   P_{t,d} = L_{0c} cap L_{td} (t >= 1), z_{cc'} = L_{0c} cap L_{0c'} (interior base points),
   z_c = L_{0c} cap {X_c = 0} (boundary base point), the coordinate points X_i = 0 (i != c),
   p_c(nu) = L_{0c} cap {L'_c = 0} (the point where the merging lines L_{0c}, L_{Nc}(delta) meet).
Prints, per vector type, the multiset of (special point, order) for numerator and denominator.
What this does not show: anything beyond the sampled vectors and n.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, T_E, T_F, jet_terms, point_on_line,  # noqa: E402
                           polar_kernels_with_D, polar_vec)
from hq_fresh_univariate import ratrecon  # noqa: E402


def line_param(A0, c, rng):
    Q1 = point_on_line(A0, 0, c, rng)
    Q2 = point_on_line(A0, 0, c, rng)
    return Q1, Q2


def special_points(A0, c, Q1, Q2, nu, m):
    """theta values of special points: solve lin(Q1 + theta Q2) = 0 for a linear form lin."""
    def root(lin):
        a = sum(lin[i] * Q1[i] for i in range(Q)) % P
        b = sum(lin[i] * Q2[i] for i in range(Q)) % P
        if b == 0:
            return None
        return (-a) * pow(b, P - 2, P) % P
    pts = {}
    for t in range(1, m):
        for d in range(Q):
            pts[root([A0[t][d][i][0] for i in range(Q)])] = f'P{t}{d}'
    for cc in range(Q):
        if cc != c:
            pts[root([A0[0][cc][i][0] for i in range(Q)])] = f'z{c}{cc}'
    for i in range(Q):
        e = [1 if j == i else 0 for j in range(Q)]
        pts[root(e)] = f'X{i}=0' + ('(z_c)' if i == c else '')
    pts[root([A0[0][c][i][0] * nu[i] % P for i in range(Q)])] = 'p_c(nu)'
    return pts


def describe(poly, pts):
    out = {}
    for f, e in poly.factor()[1]:
        if f.degree() == 1:
            r = (-int(f.coeffs()[0])) * pow(int(f.coeffs()[1]), P - 2, P) % P
            out[pts.get(r, 'other')] = out.get(pts.get(r, 'other'), 0) + e
        else:
            out[f'deg{f.degree()}'] = out.get(f'deg{f.degree()}', 0) + e
    return out


def analyse(n, c, vecs, names, seed=7, npts=None):
    m = n - 1
    N = n - 1
    rng = random.Random(seed)
    A2, info = collision_config(n, 0, rng, 2)
    nu = info['nu']
    A0 = [[[[x[0]] for x in row] for row in blk] for blk in A2]
    Q1, Q2 = line_param(A0, c, rng)
    Yd = [rng.randrange(1, P) for _ in range(Q)]
    sp = special_points(A0, c, Q1, Q2, nu, m)
    npts = npts or (12 * m + 40)
    thetas, vals = [], {nm: ([], []) for nm in names}
    th = 0
    while len(thetas) < npts:
        th += 1
        X0 = [(Q1[i] + th * Q2[i]) % P for i in range(Q)]
        if th % P in sp or any(x == 0 for x in X0):
            continue
        try:
            pk, Xs = polar_kernels_with_D(A0, X0, Yd, c, {0, N}, 4, 0, nu)
        except (ZeroDivisionError, AssertionError):
            continue
        v0c = [A0[0][c][i][0] * X0[i] % P for i in range(Q)]
        thetas.append(th)
        for nm, terms in zip(names, vecs):
            out = polar_vec(pk, Xs, terms, 4, order=3)
            d = [out[i][1] for i in range(Q)]
            tau = (d[0] * v0c[1] - d[1] * v0c[0]) % P
            # alpha: d = alpha v0c + tau-part; use a fixed transverse w = (1,-1,0)-ish projection:
            # alpha := (d . v0c_perp-free) -> d0*1 + ... choose alpha = (d0*w1 - d1*w0)/(v0c0*w1 - v0c1*w0), w=(1,0,-1)
            w = (1, 0)
            den = (v0c[0] * w[1] - v0c[1] * w[0]) % P
            alpha = (d[0] * w[1] - d[1] * w[0]) * pow(den, P - 2, P) % P
            vals[nm][0].append(alpha)
            vals[nm][1].append(tau)
    res = {}
    for nm in names:
        r = {}
        for kind, vv in (('alpha', vals[nm][0]), ('tau', vals[nm][1])):
            if all(x == 0 for x in vv):
                r[kind] = 'zero'
                continue
            num, den = ratrecon(vv, thetas, P, npts // 2)
            r[kind] = (num.degree(), describe(num, sp), den.degree(), describe(den, sp))
        res[nm] = r
    return res


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    m = n - 1
    N = n - 1
    c = 0
    jl, jt = jet_terms(n, 0)
    vecs = [jt[0], jt[1], jt[3], jt[4], jt[7]]
    names = ['JE_0', 'JE_1', 'JF_00', 'JF_01', 'JF_11']
    vecs += [T_F(1, N, 0, 0, n), T_F(1, N, 2, 1, n), T_F(N, 1, 0, 0, n), T_F(N, 1, 0, 2, n), T_F(0, N, 0, 0, n),
             T_F(0, N, 1, 0, n), T_F(1, 2, 0, 0, n), T_F(0, 1, 0, 0, n), T_F(1, 0, 0, 0, n), T_E(0, 0)]
    names += ['F_1N00', 'F_1N21', 'F_N100', 'F_N102', 'F_0N00', 'F_0N10', 'F_1200', 'F_0100', 'F_1000', 'E_00']
    res = analyse(n, c, vecs, names)
    print(f'n={n}, line L_0{c}: alpha / tau as rational functions on the line (num deg, zeros; den deg, poles)')
    for nm in names:
        print(f'  {nm}:')
        for kind in ('alpha', 'tau'):
            print(f'     {kind}: {res[nm][kind]}')


if __name__ == '__main__':
    main()
