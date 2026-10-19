#!/usr/bin/env python3
"""Univariate factor probe: is a determinant a product of low-degree factors?

Fix all product-form parameters except theta = u_{n-1}(1) (newest block, state 1).
(i)  generic:  f(theta) = det R_n over F_p, reconstructed as a rational function
     num/den from many evaluations, num factored over F_p.
(ii) persist:  G = D + eps H with eps = l (l-adic); c(theta) = leading l-adic
     coefficient of det R_n mod l, reconstructed over F_l and factored.
A high-degree irreducible factor means no product formula along this line.
What this does not show: anything about other parameter directions or other n.
"""
import argparse
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402

Q = 3


def ratrecon(vals, xs, p, maxdeg):
    """Rational reconstruction num/den over F_p from point values (EEA on interpolant)."""
    P = flint.nmod_poly([1], p)
    for x in xs:
        P *= flint.nmod_poly([-x % p, 1], p)
    # Lagrange interpolation
    f = flint.nmod_poly([0], p)
    for i, xi in enumerate(xs):
        li = flint.nmod_poly([1], p)
        den = 1
        for j, xj in enumerate(xs):
            if j != i:
                li *= flint.nmod_poly([-xj % p, 1], p)
                den = den * (xi - xj) % p
        f += li * (vals[i] * pow(den, -1, p) % p)
    r0, r1 = P, f
    s0, s1 = flint.nmod_poly([0], p), flint.nmod_poly([1], p)
    while r1.degree() > maxdeg:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    return r1, s1


BUILD_WHICH = [('u', -1, 1)]


def build(n, theta, p_or_l, mode, base):
    R = Ring(None) if mode == 'persist' else Ring(p_or_l)
    g0, us0 = base
    if mode == 'persist':
        l = p_or_l
        g = [[(R(g0[i][a]) if i == a else R(0)) + R(l) * R(g0[i][a] + 7 * i + 3 * a + 1) for a in range(Q)] for i in range(Q)]
    else:
        g = [[R(g0[i][a]) for a in range(Q)] for i in range(Q)]
    us = [[R(x) for x in row] for row in us0]
    which = BUILD_WHICH[0]
    if which[0] == 'u':
        us[which[1]][which[2]] = R(theta)
    else:
        g[which[1]][which[2]] = R(theta)
    A = [[[g[i][a] * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
    return A, R


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
    ap.add_argument('--mode', choices=['generic', 'persist'], default='generic')
    ap.add_argument('--npts', type=int, default=260)
    ap.add_argument('--prime', type=int, default=0)
    ap.add_argument('--param', default='u,-1,1', help='u,t,i or g,i,a')
    args = ap.parse_args()
    kind, x, y = args.param.split(',')
    BUILD_WHICH[0] = (kind, int(x), int(y))
    rng = random.Random(17)
    g0 = [[rng.randint(2, 50) for _ in range(Q)] for _ in range(Q)]
    us0 = [[rng.randint(2, 50) for _ in range(Q)] for _ in range(args.n)]
    p = args.prime if args.prime else (1000003 if args.mode == 'generic' else 10007)
    xs, vals, vset = [], [], set()
    theta = 1
    while len(xs) < args.npts:
        theta += 1
        A, R = build(args.n, theta, p, args.mode, (g0, us0))
        try:
            if not geometry_ok(A, args.n):
                continue
            d = R_matrix(A, args.n, R).det()
        except ZeroDivisionError:
            continue
        if args.mode == 'generic':
            xs.append(theta % p)
            vals.append(int(d))
        else:
            if d == 0:
                continue
            v, c = vl(d, p)
            vset.add(v)
            xs.append(theta % p)
            vals.append((v, c))
    if args.mode == 'persist':
        from collections import Counter
        vc = Counter(v for v, _ in vals)
        vmin = min(vc)
        print(f'persist valuations seen: {dict(vc)}; using v = {vmin}')
        keep = [(x, c) for x, (v, c) in zip(xs, vals) if v == vmin]
        xs, vals = [x for x, _ in keep], [c for _, c in keep]
    num, den = ratrecon(vals, xs, p, args.npts // 2)
    print(f'mode={args.mode} n={args.n}: num degree {num.degree()}, den degree {den.degree()}')
    for name, poly in (('num', num), ('den', den)):
        fac = poly.factor()[1]
        degs = sorted([(f.degree(), e) for f, e in fac])
        print(f'  {name} factors (degree, multiplicity) over F_{p}: {degs}')
        if name == 'num':
            big = [f for f, e in fac if f.degree() >= 3]
            if len(big) >= 2:
                print(f'  large factors pairwise equal: {[[bool(a == b) for b in big] for a in big]}')


if __name__ == '__main__':
    main()
