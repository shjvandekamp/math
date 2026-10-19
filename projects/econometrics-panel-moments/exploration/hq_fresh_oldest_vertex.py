#!/usr/bin/env python3
"""Oldest block to a vertex: does lead(det R_n) / det R_{n-1}(blocks 1..n-1) factor nicely?

u_0(0) -> eps * u_0(0) (block 0's three lines become concurrent at the vertex e_0;
its kernel never enters state 0 in the limit).  Smith exponents are -1^{3(n-1)},
0^{...}, 1^{3(n-1)} (sum 0), so c_n := leading l-adic coefficient of det R_n is the
determinant of the limit.  We reconstruct the ratio r = c_n / det R_{n-1}(1..n-1) mod l
as a rational function of one parameter theta and factor it over F_l.
Only linear factors (natural quantities) would mean a product formula for the
limit relative to the shorter system, i.e. an induction step.
"""
import argparse
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=3)
    ap.add_argument('--param', default='u,-1,1', help='u,t,i (t=-1 newest) or g,i,a')
    ap.add_argument('--npts', type=int, default=120)
    ap.add_argument('--l', type=int, default=10007)
    ap.add_argument('--nvert', type=int, default=1, help='number of oldest blocks sent to distinct vertices e_0, e_1, e_2')
    args = ap.parse_args()
    n, l = args.n, args.l
    R = Ring(None)
    rng = random.Random(41)
    g0 = [[R(rng.randint(2, l - 1)) for _ in range(Q)] for _ in range(Q)]
    us0 = [[R(rng.randint(2, l - 1)) for _ in range(Q)] for _ in range(n)]
    kind, x, y = args.param.split(',')
    x, y = int(x), int(y)
    xs, vals, vset = [], [], {}
    theta = 1
    while len(xs) < args.npts:
        theta += 1
        g = [row[:] for row in g0]
        us = [row[:] for row in us0]
        if kind == 'u':
            us[x][y] = R(theta)
        else:
            g[x][y] = R(theta)
        for k in range(args.nvert):
            us[k] = [us[k][i] * (R(l) if i == k else R(1)) for i in range(Q)]
        A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        try:
            if not geometry_ok(A, n):
                continue
            d = R_matrix(A, n, R).det()
            rest = A[args.nvert:]
            d1 = R_matrix(rest, len(rest), R).det() if len(rest) >= 2 else None
        except ZeroDivisionError:
            continue
        v, c = vl(d, l)
        if d1 is not None:
            v1, c1 = vl(d1, l)
            if v1 != 0:
                continue
            c = c * pow(c1, -1, l) % l
        vset[v] = vset.get(v, 0) + 1
        xs.append(theta % l)
        vals.append((v, c))
    vmin = max(vset, key=vset.get)  # generic (most common) valuation
    keep = [(x_, c) for x_, (v, c) in zip(xs, vals) if v == vmin]
    num, den = ratrecon([c for _, c in keep], [x_ for x_, _ in keep], l, len(keep) // 2)
    print(f'n={n} param={args.param}: valuations {vset}; ratio lead(det R_n)/det R(remaining blocks): '
          f'num deg {num.degree()}, den deg {den.degree()}')
    for name, poly in (('num', num), ('den', den)):
        fac = poly.factor()[1]
        print(f'  {name}: ' + ' '.join(f'[deg {f.degree()}]^{e}' for f, e in sorted(fac, key=lambda fe: fe[0].degree())))


if __name__ == '__main__':
    main()
