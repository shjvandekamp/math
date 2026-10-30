#!/usr/bin/env python3
"""agent_col task 2: twelve LOCAL functionals separating the jets from S_0 (collision u_N = u_0, delta = 0).

On the doubled line L_{0c} let dp_c(f) = coefficient of eps^-2 of f(X0 + eps Yd) (X0 on L_{0c}, Yd fixed),
alpha_c = longitudinal coefficient (dp_c = alpha_c v_{0c} + tau_c-part), tau_c = dp_c ^ v_{0c}.
Special points of L_{0c}: z_c = L_{0c} cap {X_c = 0} (boundary base point of block 0),
z_{cc'} = L_{0c} cap L_{0c'} (interior base points).  Candidate functionals (4 per line, 12 total):
   phi1_c = d/dtheta alpha_c at z_c            (S_0: alpha_c vanishes to order >= 2 at z_c)
   phi2_c = (d/dtheta)^2 tau_c at z_c / 2      (S_0: tau_c vanishes to order >= 3 at z_c)
   phi3_{cc'} = residue of tau_c, alpha_c at z_{cc'}  (S_0: no pole at z_{cc'})
They are computed from the exact rational functions alpha_c(theta), tau_c(theta) on L_{0c} (reconstructed
mod p = 2^61-1 from point values), and checked to vanish on every distinct delta = 0 family member; the
matrix of the functionals on the 12 jets is printed (rank, zero pattern).
What this does not show: proofs; uniformity in n beyond the printed cases; that the zero pattern
persists at other points.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, T_E, T_F, jet_terms, point_on_line,  # noqa: E402
                           polar_kernels_with_D, polar_vec, rank)
from agent_col_dpfun import special_points  # noqa: E402
from hq_fresh_univariate import ratrecon  # noqa: E402


def taylor_at(num, den, r, order):
    """Taylor (or Laurent) coefficients of num/den at theta = r: returns (valuation, [c_v, c_{v+1}, ...])."""
    # shift theta -> r + s
    def shift(poly):
        cs = [int(x) for x in poly.coeffs()]
        out = [0] * len(cs)
        # Horner-type Taylor shift
        for k in range(len(cs) - 1, -1, -1):
            # out = out * (s + r) + cs[k]
            new = [0] * len(cs)
            for i, o in enumerate(out):
                if o:
                    new[i] = (new[i] + o * r) % P
                    if i + 1 < len(new):
                        new[i + 1] = (new[i + 1] + o) % P
            new[0] = (new[0] + cs[k]) % P
            out = new
        return out
    a, b = shift(num), shift(den)
    va = next(i for i, x in enumerate(a) if x)
    vb = next(i for i, x in enumerate(b) if x)
    a, b = a[va:], b[vb:]
    # series a/b up to 'order' terms
    binv = pow(b[0], P - 2, P)
    out = []
    for k in range(order):
        acc = a[k] if k < len(a) else 0
        for j in range(1, k + 1):
            if j < len(b):
                acc -= b[j] * out[k - j]
        out.append(acc % P * binv % P)
    return va - vb, out


def coeff_at(fun, r, k):
    """coefficient of s^k in the Laurent expansion of fun = (num, den) at theta = r (0 if fun is zero)."""
    if fun is None:
        return 0
    num, den = fun
    v, cs = taylor_at(num, den, r, k + 6)
    idx = k - v
    if idx < 0:
        return 0
    return cs[idx] if idx < len(cs) else 0


def functions_on_line(A0, n, c, vecs, nu, rng):
    m = n - 1
    N = n - 1
    Q1 = point_on_line(A0, 0, c, rng)
    Q2 = point_on_line(A0, 0, c, rng)
    Yd = [rng.randrange(1, P) for _ in range(Q)]
    sp = special_points(A0, c, Q1, Q2, nu, m)
    npts = 12 * m + 40
    thetas, al, ta = [], [[] for _ in vecs], [[] for _ in vecs]
    th = 0
    while len(thetas) < npts:
        th += 1
        X0 = [(Q1[i] + th * Q2[i]) % P for i in range(Q)]
        if th in sp or any(x == 0 for x in X0):
            continue
        pk, Xs = polar_kernels_with_D(A0, X0, Yd, c, {0, N}, 4, 0, nu)
        v0c = [A0[0][c][i][0] * X0[i] % P for i in range(Q)]
        thetas.append(th)
        for r, terms in enumerate(vecs):
            out = polar_vec(pk, Xs, terms, 4, order=3)
            d = [out[i][1] for i in range(Q)]
            tau = (d[0] * v0c[1] - d[1] * v0c[0]) % P
            # longitudinal coefficient: project along the fixed transverse direction e_0 - e_2 ... use
            # alpha = (d ^ w)/(v0c ^ w) with w = (1, 0, -1): in comps (0,1): w01 = (1, 0)
            alpha = (d[1] * pow(v0c[1], P - 2, P)) % P       # d = alpha v + beta (1,0,-1)  => d_1 = alpha v_1
            al[r].append(alpha)
            ta[r].append(tau)
    funs = []
    for r in range(len(vecs)):
        fr = {}
        for kind, vv in (('alpha', al[r]), ('tau', ta[r])):
            if all(x == 0 for x in vv):
                fr[kind] = None
            else:
                num, den = ratrecon(vv, thetas, P, npts // 2)
                fr[kind] = (num, den)
        funs.append(fr)
    inv = {v: k for k, v in sp.items()}
    zc = inv[f'X{c}=0(z_c)']
    zs = [inv[f'z{c}{cc}'] for cc in range(Q) if cc != c]
    return funs, zc, zs


def functionals(funs, zc, zs):
    rows = []
    for fr in funs:
        row = [coeff_at(fr['alpha'], zc, 1), coeff_at(fr['tau'], zc, 2)]
        for z in zs:
            row += [coeff_at(fr['alpha'], z, -1), coeff_at(fr['tau'], z, -1)]
        # lower-order checks: alpha order 0 at zc, tau orders 0,1 at zc
        row += [coeff_at(fr['alpha'], zc, 0), coeff_at(fr['tau'], zc, 0), coeff_at(fr['tau'], zc, 1)]
        for z in zs:
            row += [coeff_at(fr['alpha'], z, -2), coeff_at(fr['tau'], z, -2)]
        rows.append(row)
    return rows


def main(ns):
    for n in ns:
        m = n - 1
        N = n - 1
        rng = random.Random(7700 + n)
        A2, info = collision_config(n, 0, rng, 2)
        nu = info['nu']
        A0 = [[[[x[0]] for x in row] for row in blk] for blk in A2]
        Es = [T_E(s, a) for s in range(m) for a in range(Q)]
        S0 = Es + [T_F(t, s, a, b, n) for t in range(m) for s in range(m) if s != t for a in range(Q) for b in range(Q)]
        S0 += [T_F(t, N, a, b, n) for t in range(1, m) for a in range(Q) for b in range(Q)]
        S0 += [T_F(N, s, a, b, n) for s in range(1, m) for a in range(Q) for b in range(Q)]
        S0 += [T_F(0, N, a, b, n) for a in range(Q) for b in range(Q)]
        jl, jt = jet_terms(n, 0)
        allrows_S0 = [[] for _ in S0]
        allrows_J = [[] for _ in jt]
        for c in range(Q):
            funs, zc, zs = functions_on_line(A0, n, c, S0 + jt, nu, rng)
            rows = functionals(funs, zc, zs)
            for r in range(len(S0)):
                allrows_S0[r] += rows[r]
            for r in range(len(jt)):
                allrows_J[r] += rows[len(S0) + r]
        # columns: per line c: [phi1, phi2, res_alpha z1, res_tau z1, res_alpha z2, res_tau z2, checks...]
        main_cols = [c * 13 + j for c in range(Q) for j in range(6)]
        check_cols = [c * 13 + j for c in range(Q) for j in range(6, 13)]
        S0_main_zero = all(row[j] == 0 for row in allrows_S0 for j in main_cols)
        S0_check_zero = all(row[j] == 0 for row in allrows_S0 for j in check_cols)
        J = [[row[j] for j in main_cols] for row in allrows_J]
        print(f'n={n}: the 18 local functionals (6 per line) vanish on all {len(S0)} delta=0 family members: '
              f'{S0_main_zero}; lower-order checks vanish too: {S0_check_zero}', flush=True)
        print(f'   rank of the jets under these functionals: {rank(J)} (of 12)')
        names = ['phi1(a@zc)', 'phi2(t@zc)', 'resA z1', 'resT z1', 'resA z2', 'resT z2']
        print('   nonzero pattern (rows = jets JE_0..2, JF_ab; columns = line c x functional):')
        print('          ' + ' '.join(f'c{c}:{nm:>10s}' for c in range(Q) for nm in names))
        for lab, row in zip(jl, J):
            print(f'   {str(lab):12s} ' + ' '.join(('     X       ' if x else '     .       ') for x in row))


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [5])
