#!/usr/bin/env python3
"""Exact rational toolkit for the quotient vectors of equation (24), Q = 3.

Standard library only (fractions.Fraction).  Notation follows
research/SOURCE24_INDUCTION.md and research/HQ_FRESH_APPROACH.md:

  blocks t in range(n); A[t] is a 3x3 rational matrix, row a = coefficients
  of the line L_{ta} = sum_i A[t][a][i] X_i;
  K_t(X) = diag(L_t)^{-1} A[t] diag(X)   (row stochastic);
  E_{s,a}     = X_a e_a (I - K_s);
  B_{t,s,a,b} = X_a K_t(a,b) e_b (I - K_s);
  F_{t,s,a,b} = X_a K_t(a,b) e_b (I - K_s prod_{u not in {s,t}, increasing} K_u).

The canonical basis {E, B} of the quotient space W_n is dual to
(single-line residues, double-pole residues).  The B coefficient of a
vector v at the ordered pair (t,s,a,b) is obtained from the double residue
rho = (L_{ta} L_{sb} v)|_P at P = L_{ta} x L_{sb}, written in the basis
(v_{ta}(P), v_{sb}(P)): v = ... + c B_{t,s,a,b} + c' B_{s,t,b,a} with
rho(B_{t,s,a,b}) = -A_t(a,b) X_a X_b v_{sb}(P), rho(B_{s,t,b,a}) = -A_s(b,a) X_a X_b v_{ta}(P).

Everything is evaluated exactly at rational points; no symbolic algebra.
"""
from fractions import Fraction
import itertools as it

Q = 3


def frac_matrix(rows):
    return [[Fraction(x) for x in row] for row in rows]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def identity():
    return [[Fraction(int(i == j)) for j in range(Q)] for i in range(Q)]


def matmul(a, b):
    cols = list(zip(*b))
    return [[dot(r, c) for c in cols] for r in a]


def vecmat(v, m):
    return [sum(v[i] * m[i][j] for i in range(Q)) for j in range(Q)]


def kernel_at(A_t, X):
    """K_t evaluated at the point X (must not lie on a line of block t)."""
    K = []
    for a in range(Q):
        L = dot(A_t[a], X)
        if L == 0:
            raise ZeroDivisionError('kernel evaluated on its own line')
        K.append([A_t[a][i] * X[i] / L for i in range(Q)])
    return K


def residue_kernel(A_t, a, X):
    """(L_{ta} K_t)|_{L_{ta}=0}: only row a survives, equal to v_{ta}(X)."""
    M = [[Fraction(0)] * Q for _ in range(Q)]
    M[a] = [A_t[a][i] * X[i] for i in range(Q)]
    return M


def word(blocks_in_order, mats):
    P = identity()
    for u in blocks_in_order:
        P = matmul(P, mats[u])
    return P


def increasing_word(s, excluded, n):
    """[s] followed by all blocks not in excluded ∪ {s}, increasing."""
    return [s] + [u for u in range(n) if u != s and u not in excluded]


def family_index(n):
    """Ordered list of (t, s, a, b) with t != s: the j=1 columns."""
    return [(t, s, a, b) for t in range(n) for s in range(n) if s != t
            for a in range(Q) for b in range(Q)]


def check_geometry(A, n):
    """Cross points have nonzero coordinates and lie on no third line."""
    for (u, c), (v, d) in it.combinations([(t, a) for t in range(n) for a in range(Q)], 2):
        if u == v:
            continue
        P = cross(A[u][c], A[v][d])
        if any(x == 0 for x in P):
            return False, f'zero coordinate at cross point {(u, c, v, d)}'
        for t in range(n):
            for a in range(Q):
                if (t, a) not in ((u, c), (v, d)) and dot(A[t][a], P) == 0:
                    return False, f'third line {(t, a)} through cross point {(u, c, v, d)}'
    return True, 'ok'


def double_residue_of_F(A, n, t, s, a, b, u, c, v, d, P=None):
    """rho_{(u,c),(v,d)}(F_{t,s,a,b}) as an exact 3-vector at P = L_{uc} x L_{vd}."""
    if P is None:
        P = cross(A[u][c], A[v][d])
    # the prefactor X_a K_t(a,b) has pole L_{ta}; it must be one of the two lines if t in {u,v}
    if (t == u and a != c) or (t == v and a != d):
        return [Fraction(0)] * Q
    mats = {}
    for w in range(n):
        if w == u:
            mats[w] = residue_kernel(A[u], c, P)
        elif w == v:
            mats[w] = residue_kernel(A[v], d, P)
        else:
            mats[w] = kernel_at(A[w], P)
    pref = A[t][a][b] * P[b]           # residue or value of K_t(a,b) numerator
    if t not in (u, v):
        pref = pref / dot(A[t][a], P)
    W = word(increasing_word(s, {t}, n), mats)
    scalar = -P[a] * pref
    return [scalar * x for x in W[b]]


def coords_in_pair_basis(vec, U, V):
    """Solve vec = alpha U + beta V for zero-sum U, V, vec."""
    for i, j in it.combinations(range(Q), 2):
        det = U[i] * V[j] - U[j] * V[i]
        if det != 0:
            alpha = (vec[i] * V[j] - vec[j] * V[i]) / det
            beta = (U[i] * vec[j] - U[j] * vec[i]) / det
            assert all(alpha * U[k] + beta * V[k] == vec[k] for k in range(Q))
            return alpha, beta
    raise ValueError('pair residue vectors dependent')


def b_coefficient_matrix(A, n):
    """R_n: rows = B_{u,v,c,d} (ordered pairs), columns = F_{t,s,a,b}.

    Entry = coefficient of B_{u,v,c,d} in the expansion of F_{t,s,a,b}
    in the canonical basis.  Returned as dict of rows keyed by (u,v,c,d).
    """
    cols = family_index(n)
    rows = {}
    for u, v in it.combinations(range(n), 2):
        for c, d in it.product(range(Q), repeat=2):
            P = cross(A[u][c], A[v][d])
            U = [A[u][c][i] * P[i] for i in range(Q)]   # v_{uc}(P)
            V = [A[v][d][i] * P[i] for i in range(Q)]   # v_{vd}(P)
            norm_uv = -A[u][c][d] * P[c] * P[d]           # rho(B_{u,v,c,d}) = norm_uv * V
            norm_vu = -A[v][d][c] * P[c] * P[d]           # rho(B_{v,u,d,c}) = norm_vu * U
            row_uv, row_vu = [], []
            for (t, s, a, b) in cols:
                rho = double_residue_of_F(A, n, t, s, a, b, u, c, v, d, P)
                alpha, beta = coords_in_pair_basis(rho, U, V)
                row_uv.append(beta / norm_uv)
                row_vu.append(alpha / norm_vu)
            rows[(u, v, c, d)] = row_uv
            rows[(v, u, d, c)] = row_vu
    return cols, rows


def det_fraction(M):
    """Exact determinant by fraction-free Bareiss on a copy."""
    n = len(M)
    a = [[Fraction(x) for x in row] for row in M]
    sign = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            piv = next((i for i in range(k + 1, n) if a[i][k] != 0), None)
            if piv is None:
                return Fraction(0)
            a[k], a[piv] = a[piv], a[k]
            sign = -sign
        for i in range(k + 1, n):
            f = a[i][k] / a[k][k]
            if f:
                a[i] = [x - f * y for x, y in zip(a[i], a[k])]
    d = Fraction(sign)
    for k in range(n):
        d *= a[k][k]
    return d


def factorize(n):
    """Trial-division factorisation of a positive integer (small inputs)."""
    n = abs(int(n))
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f
