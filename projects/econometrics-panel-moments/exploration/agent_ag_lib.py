#!/usr/bin/env python3
"""agent_ag_lib: evaluation-based exact (mod p) linear algebra in W_n.

Vectors of W_n are rational row-vector functions of X in P^2.  A vector is given
as a list of terms (coef, a0, heads, b, word) meaning

    coef * X_{a0} * K_{t1}(a0,a1) K_{t2}(a1,a2) ... K_{tk}(a_{k-1},a_k) * e_b (I - W),

with heads = [(t1,a1),...,(tk,ak)], b = a_k (b = a0 if heads is empty) and
W = K_{w1} ... K_{wm} for word = [w1,...,wm].  Examples:
    E_{s,a}       = [(1, a, [], a, [s])]
    h_tab (I - W) = [(1, a, [(t,b)], b, W)]
    J_{s,b}       = [(1, b, [], b, [s] + others)]
Coefficients w.r.t. the basis {E} u {F} (equation-24 family) are obtained by
evaluating at random points (components 0 and 1; vectors are zero-sum) and solving
an invertible square system mod p.  Everything is exact mod p = 2^61 - 1.

Run directly for a self-test (consistency of the expansion at extra points, and the
known facts Lambda_n(J) = 0 and the dimension of ker Lambda_n).
"""
import itertools as it
import random
import sys

import flint

P = (1 << 61) - 1
Q = 3


def inv(x):
    return pow(x % P, P - 2, P)


def mm(A, B):
    return [[(A[i][0] * B[0][j] + A[i][1] * B[1][j] + A[i][2] * B[2][j]) % P for j in range(Q)]
            for i in range(Q)]


IDM = [[1 if i == j else 0 for j in range(Q)] for i in range(Q)]


def product_config(n, rng, g=None, us=None, lo=1, hi=10 ** 6):
    """A_t(a,i) = g(i,a) u_t(i) mod P (product form)."""
    gg = g if g is not None else [[rng.randint(lo, hi) for _ in range(Q)] for _ in range(Q)]
    uu = us if us is not None else [[rng.randint(lo, hi) for _ in range(Q)] for _ in range(n)]
    A = [[[gg[i][a] * uu[t][i] % P for i in range(Q)] for a in range(Q)] for t in range(len(uu))]
    return A, gg, uu


def kernels_at(A, X):
    Ks = []
    for At in A:
        K = []
        for a in range(Q):
            L = (At[a][0] * X[0] + At[a][1] * X[1] + At[a][2] * X[2]) % P
            if L == 0:
                raise ZeroDivisionError
            iL = inv(L)
            K.append([At[a][i] * X[i] % P * iL % P for i in range(Q)])
        Ks.append(K)
    return Ks


class PointEval:
    """Evaluate term-list vectors at one point X (caching word products)."""

    def __init__(self, A, X):
        self.X = X
        self.Ks = kernels_at(A, X)
        self.cache = {}

    def word(self, w):
        key = tuple(w)
        if key in self.cache:
            return self.cache[key]
        if len(w) == 0:
            M = IDM
        elif len(w) == 1:
            M = self.Ks[w[0]]
        else:
            M = mm(self.word(w[:-1]), self.Ks[w[-1]])
        self.cache[key] = M
        return M

    def vec(self, terms):
        out = [0, 0, 0]
        X, Ks = self.X, self.Ks
        for coef, a0, heads, b, w in terms:
            sc = coef * X[a0] % P
            prev = a0
            for (t, a) in heads:
                sc = sc * Ks[t][prev][a] % P
                prev = a
            W = self.word(w)
            for j in range(Q):
                out[j] = (out[j] + sc * ((1 if j == b else 0) - W[b][j])) % P
        return out


def dhw_word(t, s, blocks):
    return [s] + [u for u in blocks if u not in (s, t)]


def E_spec(s, a):
    return [(1, a, [], a, [s])]


def F_spec(t, s, a, b, blocks):
    return [(1, a, [(t, b)], b, dhw_word(t, s, blocks))]


def J_spec(s, b, blocks):
    return [(1, b, [], b, [s] + [u for u in blocks if u != s])]


def family(n, blocks=None, word_fn=None):
    """Labels and specs of the basis {E_{s,a}} u {F_{t,s,a,b}} (DHW words by default)."""
    blocks = list(range(n)) if blocks is None else blocks
    word_fn = word_fn or (lambda t, s: dhw_word(t, s, blocks))
    labs, specs = [], []
    for s in blocks:
        for a in range(Q):
            labs.append(('E', s, a))
            specs.append(E_spec(s, a))
    for t in blocks:
        for s in blocks:
            if s == t:
                continue
            for a in range(Q):
                for b in range(Q):
                    labs.append(('F', t, s, a, b))
                    specs.append([(1, a, [(t, b)], b, word_fn(t, s))])
    return labs, specs


def rand_point(rng):
    return [rng.randrange(1, P) for _ in range(Q)]


def eval_matrix(A, specs, points):
    """rows: 2 per point (components 0, 1); columns: specs."""
    rows = []
    for X in points:
        pe = PointEval(A, X)
        vals = [pe.vec(sp) for sp in specs]
        rows.append([v[0] for v in vals])
        rows.append([v[1] for v in vals])
    return rows


class Basis:
    """Exact coordinates w.r.t. a given basis of W_n (list of specs of length dim W_n)."""

    def __init__(self, A, specs, rng, extra=3):
        self.A, self.specs = A, specs
        dim = len(specs)
        npts = (dim + 1) // 2
        for _ in range(5):
            pts = []
            while len(pts) < npts + extra:
                X = rand_point(rng)
                try:
                    kernels_at(A, X)
                except ZeroDivisionError:
                    continue
                pts.append(X)
            rows = eval_matrix(A, specs, pts[:npts])[:dim]
            M = flint.nmod_mat(rows, P)
            if M.rank() == dim:
                self.pts, self.chk = pts[:npts], pts[npts:]
                self.M = M
                self.Minv = M.inv()
                self.ok = True
                return
        self.ok = False  # the specs are not a basis (or bad luck)

    def coords(self, vec_specs, check=True):
        dim = len(self.specs)
        V = flint.nmod_mat(eval_matrix(self.A, vec_specs, self.pts)[:dim], P)
        C = self.Minv * V
        if check:
            Bc = flint.nmod_mat(eval_matrix(self.A, self.specs, self.chk), P)
            Vc = flint.nmod_mat(eval_matrix(self.A, vec_specs, self.chk), P)
            assert Bc * C == Vc, 'vector not in the span of the basis (or not in W_n)'
        return C


def rank_of(A, specs, rng, npts=None):
    """Rank of the span of vector specs (evaluation at many random points)."""
    m = len(specs)
    npts = npts or (m + 4)
    pts = []
    while len(pts) < npts:
        X = rand_point(rng)
        try:
            kernels_at(A, X)
        except ZeroDivisionError:
            continue
        pts.append(X)
    return flint.nmod_mat(eval_matrix(A, specs, pts), P).rank()


def head_map_matrix(labs, C, n, blocks=None):
    """Lambda(w)_{tab} = sum_s f_{tsab} - e_{ta}; returns rows (t,a,b) x columns of C."""
    blocks = list(range(n)) if blocks is None else blocks
    heads = [(t, a, b) for t in blocks for a in range(Q) for b in range(Q)]
    hpos = {h: i for i, h in enumerate(heads)}
    ncol = C.ncols()
    rows = [[0] * ncol for _ in heads]
    for i, lab in enumerate(labs):
        if lab[0] == 'F':
            _, t, s, a, b = lab
            r = rows[hpos[(t, a, b)]]
            for j in range(ncol):
                r[j] = (r[j] + int(C[i, j])) % P
        else:
            _, s, a = lab
            for b in range(Q):
                r = rows[hpos[(s, a, b)]]
                for j in range(ncol):
                    r[j] = (r[j] - int(C[i, j])) % P
    return heads, flint.nmod_mat(rows, P) if rows else None


def nullspace(M):
    """Right kernel basis of an nmod_mat, as a list of python lists."""
    R, rk = M.rref()
    nr, nc = M.nrows(), M.ncols()
    piv, r = [], 0
    for c in range(nc):
        if r < rk and int(R[r, c]) != 0:
            piv.append(c)
            r += 1
    free = [c for c in range(nc) if c not in piv]
    out = []
    for f in free:
        v = [0] * nc
        v[f] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-int(R[i, f])) % P
        out.append(v)
    return out


def selftest():
    rng = random.Random(1)
    for n in (2, 3, 4):
        A, g, us = product_config(n, rng)
        labs, specs = family(n)
        B = Basis(A, specs, rng)
        assert B.ok, 'family not a basis'
        # J_{s,b} expansion: E_{s,b} + sum_d F_{s,r0,b,d}
        Js = [J_spec(s, b, list(range(n))) for s in range(n) for b in range(Q)]
        C = B.coords(Js)
        heads, L = head_map_matrix(labs, C, n)
        zero = all(int(L[i, j]) == 0 for i in range(L.nrows()) for j in range(L.ncols()))
        # ker Lambda dimension: Lambda on the whole basis
        Cid = flint.nmod_mat([[1 if i == j else 0 for j in range(len(specs))] for i in range(len(specs))], P)
        _, Lfull = head_map_matrix(labs, Cid, n)
        kdim = len(specs) - Lfull.rank()
        print(f'n={n}: dim W_n={len(specs)}, family is a basis; Lambda(J)=0: {zero}; '
              f'dim ker Lambda={kdim} (9n^2-15n={9 * n * n - 15 * n})')


if __name__ == '__main__':
    selftest()


# ---------------------------------------------------------------- residues
def point_on_line(A, u, c, rng):
    """Random point on L_{uc} (mod P)."""
    l = A[u][c]
    while True:
        x, y = rng.randrange(1, P), rng.randrange(1, P)
        # solve l0 X0 + l1 X1 + l2 X2 = 0 with X1 = x, X2 = y
        X0 = (-(l[1] * x + l[2] * y)) * inv(l[0]) % P
        X = [X0, x, y]
        if X0 == 0:
            continue
        ok = True
        for t, At in enumerate(A):
            for a in range(Q):
                if (t, a) == (u, c):
                    continue
                if (At[a][0] * X[0] + At[a][1] * X[1] + At[a][2] * X[2]) % P == 0:
                    ok = False
        if ok:
            return X


def residue_vec(A, terms, u, c, X):
    """(L_{uc} * v)|_X for X on the line L_{uc} (single residue, unnormalised)."""
    n = len(A)
    mats = []
    for w in range(n):
        if w == u:
            M = [[0, 0, 0] for _ in range(Q)]
            M[c] = [A[u][c][i] * X[i] % P for i in range(Q)]
            mats.append(M)
        else:
            K = []
            for a in range(Q):
                L = (A[w][a][0] * X[0] + A[w][a][1] * X[1] + A[w][a][2] * X[2]) % P
                iL = inv(L)
                K.append([A[w][a][i] * X[i] % P * iL % P for i in range(Q)])
            mats.append(K)
    out = [0, 0, 0]
    for coef, a0, heads, b, w in terms:
        in_head = any(t == u for t, _ in heads)
        in_word = u in w
        if not (in_head or in_word):
            continue
        sc = coef * X[a0] % P
        prev = a0
        for (t, a) in heads:
            sc = sc * mats[t][prev][a] % P
            prev = a
        Wm = IDM
        for x in w:
            Wm = mm(Wm, mats[x])
        for j in range(Q):
            if in_head:
                out[j] = (out[j] + sc * ((1 if j == b else 0) - Wm[b][j])) % P
            else:
                out[j] = (out[j] - sc * Wm[b][j]) % P
    return out


def cross3(a, b):
    return [(a[1] * b[2] - a[2] * b[1]) % P, (a[2] * b[0] - a[0] * b[2]) % P, (a[0] * b[1] - a[1] * b[0]) % P]


def double_residue_vec(A, terms, u, c, v, d):
    """(L_{uc} L_{vd} * vec)|_X at X = L_{uc} cap L_{vd} (u != v), unnormalised row vector."""
    X = cross3(A[u][c], A[v][d])
    n = len(A)
    mats = []
    for w in range(n):
        if w in (u, v):
            row = c if w == u else d
            M = [[0, 0, 0] for _ in range(Q)]
            M[row] = [A[w][row][i] * X[i] % P for i in range(Q)]
            mats.append(M)
        else:
            K = []
            for a in range(Q):
                L = (A[w][a][0] * X[0] + A[w][a][1] * X[1] + A[w][a][2] * X[2]) % P
                iL = inv(L)
                K.append([A[w][a][i] * X[i] % P * iL % P for i in range(Q)])
            mats.append(K)
    out = [0, 0, 0]
    for coef, a0, heads, b, w in terms:
        hb = [t for t, _ in heads]
        cov_u = (u in hb) or (u in w)
        cov_v = (v in hb) or (v in w)
        if not (cov_u and cov_v):
            continue
        sc = coef * X[a0] % P
        prev = a0
        for (t, a) in heads:
            sc = sc * mats[t][prev][a] % P
            prev = a
        Wm = IDM
        for x in w:
            Wm = mm(Wm, mats[x])
        both_head = (u in hb) and (v in hb)
        for j in range(Q):
            if both_head:
                out[j] = (out[j] + sc * ((1 if j == b else 0) - Wm[b][j])) % P
            else:
                out[j] = (out[j] - sc * Wm[b][j]) % P
    return X, out


def cross_points(n):
    return [((u, c), (v, d)) for u in range(n) for v in range(u + 1, n) for c in range(Q) for d in range(Q)]


def combine(specs, coefvec):
    terms = []
    for k, cf in enumerate(coefvec):
        cf = int(cf) % P
        if cf:
            for (c0, a0, hd, b, w) in specs[k]:
                terms.append((c0 * cf % P, a0, hd, b, w))
    return terms
