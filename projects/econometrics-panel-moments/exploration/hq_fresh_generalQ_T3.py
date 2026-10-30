#!/usr/bin/env python3
"""General Q, T = 3: single-block statements behind exhaustiveness (dim M_3 = Q).

Block series H = span{h_r = eta_r prod_{s != r} L_s} (degree Q forms in Q variables),
D = prod_s L_s, base locus B = union of the codimension-2 spaces {L_s = L_s' = 0} and
{eta_r = L_r = 0}.  Checks mod p = 2^61-1 at random lines:
  (i)   eta_i h_r (i, r) are linearly independent (S_1 (x) H -> S_{Q+1} injective);
  (ii)  dim I(B)_{Q+1} = Q^2 (so S_1 H = I(B)_{Q+1});
  (iii) dim I(B)_Q = Q+1 and H + <D> has rank Q+1 (so I(B)_Q = H ⊕ <D>).
With eta_s D = L_s h_s these give dim ker(S_1 (x) H_2 (x) H_3 -> S) = Q (notes sec. 6.3).
Vanishing on B is imposed at enough random points of each component.
"""
import itertools as it
import random
from math import comb

import flint

P = (1 << 61) - 1


def monos(Q, d):
    return [m for m in it.product(range(d + 1), repeat=Q) if sum(m) == d]


def polymul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = (out.get(m, 0) + ca * cb) % P
    return out


def lin(coefs):
    Q = len(coefs)
    return {tuple(1 if j == i else 0 for j in range(Q)): c % P for i, c in enumerate(coefs) if c % P}


def evalm(m, x):
    v = 1
    for xi, e in zip(x, m):
        v = v * pow(xi, e, P) % P
    return v


def main():
    rng = random.Random(1)
    for Q in (3, 4, 5, 6):
        A = [[rng.randint(1, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
        L = [lin(A[s]) for s in range(Q)]
        eta = [lin([1 if j == i else 0 for j in range(Q)]) for i in range(Q)]
        H = []
        for r in range(Q):
            f = eta[r]
            for s in range(Q):
                if s != r:
                    f = polymul(f, L[s])
            H.append(f)
        D = L[0]
        for s in range(1, Q):
            D = polymul(D, L[s])

        def rank_polys(polys, d):
            ms = monos(Q, d)
            return flint.nmod_mat([[pl.get(m, 0) for m in ms] for pl in polys], P).rank()

        def vecs(l):
            return [l.get(tuple(1 if j == i else 0 for j in range(Q)), 0) for i in range(Q)]

        comps = [(vecs(L[s]), vecs(L[t])) for s, t in it.combinations(range(Q), 2)] + \
                [(vecs(eta[r]), vecs(L[r])) for r in range(Q)]

        def ideal_dim(d):
            ms = monos(Q, d)
            k = comb(d + Q - 3, Q - 3) + 4          # points needed on a P^{Q-3}
            rows = []
            for a, b in comps:
                for _ in range(k):
                    x = [rng.randint(1, 10 ** 6) for _ in range(Q)]
                    for i0, i1 in it.combinations(range(Q), 2):
                        det = (a[i0] * b[i1] - a[i1] * b[i0]) % P
                        if det:
                            break
                    ra = -sum(a[i] * x[i] for i in range(Q) if i not in (i0, i1)) % P
                    rb = -sum(b[i] * x[i] for i in range(Q) if i not in (i0, i1)) % P
                    inv = pow(det, -1, P)
                    x[i0] = (ra * b[i1] - rb * a[i1]) * inv % P
                    x[i1] = (a[i0] * rb - b[i0] * ra) * inv % P
                    rows.append([evalm(m, x) for m in ms])
            return len(ms) - flint.nmod_mat(rows, P).rank()

        r1 = rank_polys([polymul(eta[i], H[r]) for i in range(Q) for r in range(Q)], Q + 1)
        dQ, dQ1 = ideal_dim(Q), ideal_dim(Q + 1)
        rHD = rank_polys(H + [D], Q)
        ok = r1 == Q * Q and dQ == Q + 1 and rHD == Q + 1 and dQ1 == Q * Q
        print(f'Q={Q}: (i) rank {r1}/{Q * Q}; (iii) dim I(B)_Q={dQ} (want {Q + 1}), rank(H,D)={rHD}; '
              f'(ii) dim I(B)_(Q+1)={dQ1} (want {Q * Q})  {"ALL OK" if ok else "FAIL"}', flush=True)


if __name__ == '__main__':
    main()


def raw_moment_dim(Q, T, rng):
    """Independent check: dim M_T = Q^T - rank{F_y} from the raw likelihood polynomials at an
    economic point (rank of the path-likelihood vectors evaluated at many random eta)."""
    g = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
    w = [rng.randint(2, 10 ** 6) for _ in range(Q)]
    xs = [rng.randint(1, 30) for _ in range(T)]
    pi = [[[g[q][r] * pow(w[q], xs[t], P) % P for r in range(Q)] for q in range(Q)] for t in range(T)]
    paths = list(it.product(range(Q), repeat=T))
    npts = Q ** T + 5
    cols = []
    for _ in range(npts):
        eta = [rng.randint(1, P - 1) for _ in range(Q)]
        K = []
        for t in range(T):
            Kt = []
            for a in range(Q):
                Lv = sum(pi[t][j][a] * eta[j] for j in range(Q)) % P
                inv = pow(Lv, -1, P)
                Kt.append([pi[t][i][a] * eta[i] % P * inv % P for i in range(Q)])
            K.append(Kt)
        col = []
        for y in paths:
            v, prev = 1, 0
            for t in range(T):
                v = v * K[t][prev][y[t]] % P
                prev = y[t]
            col.append(v)
        cols.append(col)
    rk = flint.nmod_mat(cols, P).rank()
    return Q ** T - rk


if __name__ == '__main__':
    rng = random.Random(4)
    for Q in (2, 3, 4, 5, 6):
        print(f'independent check Q={Q}, T=3: dim M_3 = {raw_moment_dim(Q, 3, rng)} (theorem: {Q})', flush=True)
