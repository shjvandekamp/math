#!/usr/bin/env python3
"""General Q, T = 4: checks behind the dimension theorem dim M_4 = 3Q^2 + 2Q (notes sec. 6.4).

Blocks 3 and 4 (degree-Q block series H_t = span{h_tr = eta_r prod_{s != r} L_ts}, D_t = prod_s L_ts),
B_t = base locus of block t, W_r = {eta_r = L_3r = L_4r = 0}.  Mod p = 2^61-1 at an economic point
(g(j,r) = w_r^j, u_t(j) = z_t^j: the uniform genericity witness of sec. 6.4) and at random lines:
  (a) dim J_{2Q} <= (Q+1)^2, J = I(B_3) ∩ I(B_4) ∩ ∩_r I(W_r)^(2) (vanishing imposed at random points,
      double vanishing via all first partial derivatives at random points of W_r);
  (b) the (Q+1)^2 products (H_3 + <D_3>)(H_4 + <D_4>) are independent and lie in J;
  (c) dim S_1 H_3 H_4 = Q^3 - Q;
  (d) for comparison, dim I(B_3 ∪ B_4)_{2Q} (no double vanishing) = (Q+1)^2 + Q(Q-3);
  (e) independent check: dim M_4 = Q^4 - rank of the raw path-likelihood vectors at an economic point.
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


def point_on(forms, Q, rng):
    """random point of the linear space {forms = 0} (forms: list of coefficient vectors)."""
    k = len(forms)
    for piv in it.combinations(range(Q), k):
        A = flint.nmod_mat([[f[i] for i in piv] for f in forms], P)
        if A.rank() == k:
            break
    else:
        raise ValueError('degenerate')
    free = [i for i in range(Q) if i not in piv]
    x = [0] * Q
    for i in free:
        x[i] = rng.randint(1, P - 1)
    rhs = flint.nmod_mat([[-sum(f[i] * x[i] for i in free) % P] for f in forms], P)
    sol = A.solve(rhs)
    for j, i in enumerate(piv):
        x[i] = int(sol[j, 0])
    return x


def deriv_rows(ms, x, Q):
    rows = []
    for i in range(Q):
        r = []
        for m in ms:
            if m[i] == 0:
                r.append(0)
                continue
            mm = list(m)
            mm[i] -= 1
            r.append(m[i] * evalm(tuple(mm), x) % P)
        rows.append(r)
    return rows


def run(Q, rng, witness=True):
    if witness:
        w = [2 ** r for r in range(Q)]
        z = {3: 2 ** (3 * Q), 4: 2 ** (4 * Q)}
        g = [[pow(w[r], j, P) for r in range(Q)] for j in range(Q)]          # g[j][r]
        A = {t: [[g[j][r] * pow(z[t], j, P) % P for j in range(Q)] for r in range(Q)] for t in (3, 4)}
    else:
        A = {t: [[rng.randint(1, 10 ** 6) for _ in range(Q)] for _ in range(Q)] for t in (3, 4)}
    eta = [[1 if j == i else 0 for j in range(Q)] for i in range(Q)]
    L = {t: [lin(A[t][r]) for r in range(Q)] for t in (3, 4)}
    H, D = {}, {}
    for t in (3, 4):
        H[t] = []
        for r in range(Q):
            f = lin(eta[r])
            for s in range(Q):
                if s != r:
                    f = polymul(f, L[t][s])
            H[t].append(f)
        d = L[t][0]
        for s in range(1, Q):
            d = polymul(d, L[t][s])
        D[t] = d
    comps = []
    for t in (3, 4):
        comps += [[A[t][s], A[t][s2]] for s, s2 in it.combinations(range(Q), 2)]
        comps += [[eta[r], A[t][r]] for r in range(Q)]
    Ws = [[eta[r], A[3][r], A[4][r]] for r in range(Q)]

    def rank_polys(polys, d):
        ms = monos(Q, d)
        return flint.nmod_mat([[pl.get(m, 0) for m in ms] for pl in polys], P).rank()

    def ideal_dim(d, double):
        ms = monos(Q, d)
        rows = []
        k = comb(d + Q - 3, Q - 3) + 4
        for c in comps:
            for _ in range(k):
                x = point_on(c, Q, rng)
                rows.append([evalm(m, x) for m in ms])
        if double and Q >= 4:
            kw = comb(d + Q - 4, Q - 4) + 4
            for c in Ws:
                for _ in range(kw):
                    x = point_on(c, Q, rng)
                    rows += deriv_rows(ms, x, Q)
        return len(ms) - flint.nmod_mat(rows, P).rank()

    prods = [polymul(a, b) for a in H[3] + [D[3]] for b in H[4] + [D[4]]]
    r_prods = rank_polys(prods, 2 * Q)
    dJ = ideal_dim(2 * Q, True)
    dI = ideal_dim(2 * Q, False)
    lin_forms = [lin(eta[i]) for i in range(Q)]
    s1h3h4 = [polymul(e, polymul(a, b)) for e in lin_forms for a in H[3] for b in H[4]]
    r_v = rank_polys(s1h3h4, 2 * Q + 1)
    return r_prods, dJ, dI, r_v


def raw_dim_M4(Q, rng):
    g = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
    w = [rng.randint(2, 10 ** 6) for _ in range(Q)]
    xs = rng.sample(range(1, 31), 4)   # distinct covariate values (repeats are special points)
    pi = [[[g[q][r] * pow(w[q], xs[t], P) % P for r in range(Q)] for q in range(Q)] for t in range(4)]
    paths = list(it.product(range(Q), repeat=4))
    cols = []
    for _ in range(Q ** 4 + 5):
        eta = [rng.randint(1, P - 1) for _ in range(Q)]
        K = []
        for t in range(4):
            Kt = []
            for a in range(Q):
                inv = pow(sum(pi[t][j][a] * eta[j] for j in range(Q)) % P, -1, P)
                Kt.append([pi[t][i][a] * eta[i] % P * inv % P for i in range(Q)])
            K.append(Kt)
        col = []
        for y in paths:
            v, prev = 1, 0
            for t in range(4):
                v = v * K[t][prev][y[t]] % P
                prev = y[t]
            col.append(v)
        cols.append(col)
    return Q ** 4 - flint.nmod_mat(cols, P).rank()


def main():
    rng = random.Random(2)
    for Q in (3, 4, 5):
        for wit in (True, False):
            rp, dJ, dI, rv = run(Q, rng, wit)
            print(f'Q={Q} ({"witness" if wit else "random"} lines): products rank {rp} (want {(Q + 1) ** 2}); '
                  f'dim J_2Q={dJ} (<= {(Q + 1) ** 2}); dim I(B3∪B4)_2Q={dI} (= {(Q + 1) ** 2 + Q * (Q - 3)}?); '
                  f'dim S1H3H4={rv} (want {Q ** 3 - Q})', flush=True)
    for Q in (3, 4, 5):
        print(f'independent check Q={Q}: dim M_4 = {raw_dim_M4(Q, rng)} (theorem: {3 * Q * Q + 2 * Q})', flush=True)


if __name__ == '__main__':
    main()
