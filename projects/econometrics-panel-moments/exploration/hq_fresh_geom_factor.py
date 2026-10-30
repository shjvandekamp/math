#!/usr/bin/env python3
"""det R_n along shift-invariant economic points u_t = lam^(t+1), lam = (1, theta, c).

These points (linear time trend x_t = t+1) carry the torus shift X -> lam X mapping block t
to block t+1.  det R_n(theta) is reconstructed over F_p (p = 1000003) as a rational function
of theta from many evaluations and its numerator and denominator are factored.
Usage: hq_fresh_geom_factor.py n npts   (n = 3: 600 points; n = 4: 1600 points).
Observed: n = 3 numerator [1]^18 [2]^3 [3]^3 [17]^3 (the cube persists); n = 4 has
irreducible factors of degrees 11, 17, 46, 58, 92, 154: no product formula on this family.
"""
import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_fast import Ring, R_matrix, geometry_ok  # noqa: E402
from hq_fresh_univariate import ratrecon  # noqa: E402

P = 1000003
Q = 3


def main():
    n, npts = int(sys.argv[1]), int(sys.argv[2])
    R = Ring(P)
    rng = random.Random(11)
    g0 = [[rng.randint(2, P - 1) for _ in range(Q)] for _ in range(Q)]
    c = rng.randint(2, P - 1)
    xs, vals, th = [], [], 1
    while len(xs) < npts:
        th += 1
        lam = [R(1), R(th), R(c)]
        us = [[lam[i] ** (t + 1) for i in range(Q)] for t in range(n)]
        A = [[[R(g0[i][a]) * us[t][i] for i in range(Q)] for a in range(Q)] for t in range(n)]
        try:
            if not geometry_ok(A, n):
                continue
            d = int(R_matrix(A, n, R).det())
        except ZeroDivisionError:
            continue
        xs.append(th)
        vals.append(d)
    num, den = ratrecon(vals, xs, P, len(xs) // 2)

    def fmt(poly):
        cnt = Counter((f.degree(), e) for f, e in poly.factor()[1])
        return ' '.join(f'[{d}]^{e}x{m}' for (d, e), m in sorted(cnt.items()))
    print(f'n={n}: num deg {num.degree()}: {fmt(num)} | den deg {den.degree()}: {fmt(den)}')


if __name__ == '__main__':
    main()
