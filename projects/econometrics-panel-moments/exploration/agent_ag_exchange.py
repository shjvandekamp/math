#!/usr/bin/env python3
"""agent_ag: split of the append step into a Lambda-free collocation and an exchange matrix.

Mixed family M_{n+1} = {E (all), F'_{t,s} = F_{t,s} K_N + B_{t,N} (old), B_{t,N,a,b}, F_{N,s,a,b}}.
In canonical coordinates it is block lower triangular, so
    det R^M_{n+1} = det Gamma * det R_n * prod_a det D_{N,a}           (D = collocation of J^{[n]})
and the DHW family differs from M_{n+1} only by F_{t,N,a,b} = B_{t,N,a,b} + kappa_{tab},
kappa_{tab} = h_{tab} K_N (I - Pi_(t)), hence
    det R_{n+1} = det Gamma * det R_n * det D_N * det(I + C_n),
C_n = B_{t,N}-coordinates of kappa in the basis M_{n+1}  (9n x 9n).
Checks (mod p): (1) the identity det R_{n+1} / det R^M_{n+1} = det(I + C_n);
(2) n = 2: factorisation over F_p of det(I + C_n) and of det R^M_{n+1} (prop. det Gamma det D_N) as
rational functions of theta = u_N(1) (newest block), via rational reconstruction from 400 values
(degrees well below the reconstruction bound 200, so the factor degrees are reliable).
What this does not show: nonvanishing for all n.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_ag_lib import P, Q, Basis, E_spec, product_config, dhw_word  # noqa: E402
from hq_fresh_fast import Ring, row_index  # noqa: E402
from hq_fresh_words import build_cols  # noqa: E402
from hq_fresh_univariate import ratrecon  # noqa: E402


def mixed_specs(n):
    """Basis M_{n+1} of W_{n+1} (blocks 0..n, N = n newest) and the DHW old-head new columns."""
    N = n
    blocks = list(range(n + 1))
    labs, specs = [], []
    for s in blocks:
        for a in range(Q):
            labs.append(('E', s, a))
            specs.append(E_spec(s, a))
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            w = dhw_word(t, s, list(range(n))) + [N]
            for a in range(Q):
                for b in range(Q):
                    labs.append(('Fp', t, s, a, b))
                    specs.append([(1, a, [(t, b)], b, w)])
    for t in range(n):
        for a in range(Q):
            for b in range(Q):
                labs.append(('BtN', t, a, b))
                specs.append([(1, a, [(t, b)], b, [N])])
    for s in range(n):
        w = dhw_word(N, s, blocks)
        for a in range(Q):
            for b in range(Q):
                labs.append(('FNs', s, a, b))
                specs.append([(1, a, [(N, b)], b, w)])
    new = []
    for t in range(n):
        w = dhw_word(t, N, blocks)
        for a in range(Q):
            for b in range(Q):
                new.append([(1, a, [(t, b)], b, w)])
    return labs, specs, new


def exchange_det(A, n, rng):
    labs, specs, new = mixed_specs(n)
    B = Basis(A, specs, rng)
    if not B.ok:
        return None
    C = B.coords(new)
    rows = [i for i, l in enumerate(labs) if l[0] == 'BtN']
    M = flint.nmod_mat([[int(C[i, j]) for j in range(C.ncols())] for i in rows], P)
    return M.det()


def canon_det(A, n_blocks, cols):
    R = Ring(P)
    rows = build_cols(A, n_blocks, R, cols)
    keys = row_index(n_blocks)
    return flint.nmod_mat([[int(rows[k][j]) for j in range(len(cols))] for k in keys], P).det()


def dhw_cols(nb):
    out = []
    for t in range(nb):
        for s in range(nb):
            if s != t:
                w = dhw_word(t, s, list(range(nb)))
                for a in range(Q):
                    for b in range(Q):
                        out.append((t, a, b, [(1, w)]))
    return out


def mixed_cols(n):
    N = n
    out = []
    for t in range(n):
        for s in range(n):
            if s != t:
                w = dhw_word(t, s, list(range(n))) + [N]
                for a in range(Q):
                    for b in range(Q):
                        out.append((t, a, b, [(1, w)]))
    for t in range(n):
        for a in range(Q):
            for b in range(Q):
                out.append((t, a, b, [(1, [N])]))
    for s in range(n):
        w = dhw_word(N, s, list(range(n + 1)))
        for a in range(Q):
            for b in range(Q):
                out.append((N, a, b, [(1, w)]))
    return out


def to_ring(A):
    R = Ring(P)
    return [[[R(x) for x in row] for row in blk] for blk in A]


def main():
    rng = random.Random(5)
    for n in (2, 3, 4):
        A, g, us = product_config(n + 1, rng)
        Ar = to_ring(A)
        dR = canon_det(Ar, n + 1, dhw_cols(n + 1))
        dM = canon_det(Ar, n + 1, mixed_cols(n))
        dX = exchange_det(A, n, rng)
        ok = (dM != 0) and (dR == dM * dX or dR == -(dM * dX))
        print(f'n={n}: det R_(n+1) = +-det R^M_(n+1) * det(I + C_n): {ok}  (det R^M != 0: {dM != 0}, det(I+C) != 0: {dX != 0})')
    # factorisation in theta = u_N(1)
    for n in (2,):
        rng = random.Random(77 + n)
        g = [[rng.randrange(1, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, 10 ** 6) for _ in range(Q)] for _ in range(n + 1)]
        xs, vX, vM = [], [], []
        theta = 1
        npts = 400
        while len(xs) < npts:
            theta += 1
            us[n][1] = theta
            A, _, _ = product_config(n + 1, rng, g=g, us=[r[:] for r in us])
            try:
                dX = exchange_det(A, n, rng)
                Ar = to_ring(A)
                dM = canon_det(Ar, n + 1, mixed_cols(n))
            except ZeroDivisionError:
                continue
            if not dX or not dM:
                continue
            xs.append(theta)
            vX.append(int(dX))
            vM.append(int(dM))
        for name, vals in (('det(I+C_n)', vX), ('det R^M_(n+1)', vM)):
            num, den = ratrecon(vals, xs, P, len(xs) // 2)
            fn = sorted(f.degree() for f, e in num.factor()[1] for _ in range(e))
            fd = sorted(f.degree() for f, e in den.factor()[1] for _ in range(e))
            print(f'n={n} {name:16s} in theta=u_N(1): num deg {num.degree()} factor degs {fn}; den deg {den.degree()} factor degs {fd}')


if __name__ == '__main__':
    main()
