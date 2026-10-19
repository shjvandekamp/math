#!/usr/bin/env python3
"""agent_ag: collision of the two LATEST blocks (u_N = u_{N-1} * (1 + eps*nu), eps = l).

Prints (exact fmpq arithmetic, l-adic valuations, l = 10007 by default):
  (1) Smith exponents of R_m(eps) for m blocks (python-flint, hq_fresh_smith);
  (2) for one parameter theta (an entry of u_t, nu or g), the leading l-adic coefficient
      c_m of det R_m divided by det R_{m-1}(blocks 0..m-2), reconstructed mod l as a rational
      function of theta and factored over F_l.  Linear factors only = natural product formula.
  (3) with --intrinsic: coordinate-free Smith exponents of the evaluation matrix of {E} u {F} at fixed
      generic points (as in hq_fresh_coalesce.py), for m = 3, 4, 5; compares the number of exponent-1
      entries with the number 18m - 24 of family pairs that coincide at the collision.
Usage:  agent_ag_collision.py --m 4 --param nu,1   (or u,T,i  or g,i,a)  [--smith] [--intrinsic]
What this does not show: anything beyond the sampled sizes; c_m != 0 for all m.
"""
import argparse
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402
from hq_fresh_smith import smith_exponents, summarize  # noqa: E402
from hq_fresh_univariate import ratrecon  # noqa: E402

Q = 3


def vl(x, l):
    num, den = int(x.p), int(x.q)
    v = 0
    while num % l == 0:
        num //= l
        v += 1
    while den % l == 0:
        den //= l
        v -= 1
    return v, num * pow(den, -1, l) % l


def config(m, g, us, nu, l, R):
    """blocks 0..m-2 from us, block m-1 = block m-2 times (1 + l*nu)."""
    A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(m - 1)]
    un = [us[m - 2][i] * (1 + R(l) * nu[i]) for i in range(Q)]
    A.append([[g[i][a] * un[i] for i in range(Q)] for a in range(Q)])
    return A


def intrinsic(l):
    from hq_fresh_coalesce import family_eval
    R = Ring(None)
    rng = random.Random(8)
    for m in (3, 4, 5):
        while True:
            g = [[R(rng.randint(2, 60)) for _ in range(Q)] for _ in range(Q)]
            us = [[R(rng.randint(2, 60)) for _ in range(Q)] for _ in range(m - 1)]
            nu = [R(rng.randint(2, 60)) for _ in range(Q)]
            A = config(m, g, us, nu, l, R)
            if geometry_ok(A, m):
                break
        N = 3 * m + 9 * m * (m - 1)
        pts = [[R(rng.randint(1, 50)) for _ in range(Q)] for _ in range(N // 2 + 6)]
        rows = [[] for _ in range(N)]
        for X in pts:
            vals = family_eval(A, m, X, R, 'F')
            for k in range(N):
                rows[k].extend([vals[k][0], vals[k][1]])
        e = smith_exponents(flint.fmpq_mat(rows), l, K=60)
        print(f'm={m}: intrinsic Smith exponents at the latest-pair collision {summarize(e)}; '
              f'coinciding pairs 18m-24 = {18 * m - 24}', flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, default=4)
    ap.add_argument('--param', default='nu,1')
    ap.add_argument('--npts', type=int, default=80)
    ap.add_argument('--l', type=int, default=10007)
    ap.add_argument('--smith', action='store_true')
    ap.add_argument('--seed', type=int, default=17)
    ap.add_argument('--intrinsic', action='store_true')
    args = ap.parse_args()
    if args.intrinsic:
        intrinsic(args.l)
        return
    m, l = args.m, args.l
    R = Ring(None)
    rng = random.Random(args.seed)
    g0 = [[R(rng.randint(2, 200)) for _ in range(Q)] for _ in range(Q)]
    us0 = [[R(rng.randint(2, 200)) for _ in range(Q)] for _ in range(m - 1)]
    nu0 = [R(rng.randint(2, 200)) for _ in range(Q)]
    if args.smith:
        A = config(m, g0, us0, nu0, l, R)
        assert geometry_ok(A, m)
        ex = smith_exponents(R_matrix(A, m, R), l, K=30)
        print(f'm={m}: Smith exponents of R_m at the latest-pair collision: {summarize(ex)} (sum {sum(ex)})')
    kind, x = args.param.split(',')[0], [int(z) for z in args.param.split(',')[1:]]
    xs, vals, vset = [], [], {}
    theta = 1
    while len(xs) < args.npts:
        theta += 1
        g = [row[:] for row in g0]
        us = [row[:] for row in us0]
        nu = nu0[:]
        if kind == 'nu':
            nu[x[0]] = R(theta)
        elif kind == 'u':
            us[x[0]][x[1]] = R(theta)
        else:
            g[x[0]][x[1]] = R(theta)
        A = config(m, g, us, nu, l, R)
        try:
            if not geometry_ok(A, m):
                continue
            d = R_matrix(A, m, R).det()
            d1 = R_matrix(A[:m - 1], m - 1, R).det() if m - 1 >= 2 else flint.fmpq(1)
        except ZeroDivisionError:
            continue
        if d == 0 or d1 == 0:
            continue
        v, c = vl(d, l)
        v1, c1 = vl(d1, l)
        if v1 != 0:
            continue
        c = c * pow(c1, -1, l) % l
        vset[v] = vset.get(v, 0) + 1
        xs.append(theta % l)
        vals.append((v, c))
    vmin = max(vset, key=vset.get)
    keep = [(x_, c) for x_, (v, c) in zip(xs, vals) if v == vmin]
    num, den = ratrecon([c for _, c in keep], [x_ for x_, _ in keep], l, len(keep) // 2)
    print(f'm={m} param={args.param}: valuations of det R_m {vset}; ratio lead(det R_m)/det R_(m-1): '
          f'num deg {num.degree()}, den deg {den.degree()}')
    for name, poly in (('num', num), ('den', den)):
        fac = poly.factor()[1]
        print(f'  {name}: ' + ' '.join(f'[deg {f.degree()}]^{e}' for f, e in sorted(fac, key=lambda fe: fe[0].degree())))


if __name__ == '__main__':
    main()
