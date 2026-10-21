#!/usr/bin/env python3
"""Shared library for the agent_per_* experiments (persistence limit g = I + eps H).

Model (exact).  A_t(a,i) = (delta_ai + eps H(a,i)) u_t(i), H(a,a) = 0, so with
c_{t,a,i} := H(a,i) u_t(i)/u_t(a) (the torus conjugate D_{u_t}^{-1} H D_{u_t}):

    L_ta / u_t(a) = l_ta := X_a + eps lam_ta,   lam_ta = sum_{i != a} c_{t,a,i} X_i,
    mu_ta := lam_ta / X_a = Lam_t(a)            (degree-0 Laurent polynomial),
    f_ta  := X_a / l_ta = 1/(1 + eps mu_ta) = K_t(a,a),
    K_t(a,d) = eps c_{t,a,d} (X_d/X_a) f_ta     (d != a),
    nu_ta := X_a e_a N_t = sum_{i != a} c_{t,a,i} X_i (e_i - e_a)  (linear, zero-sum),
    e_a (I - K_t) = -eps f_ta nu_ta / X_a,   E_{t,a} = -eps f_ta nu_ta.

Numerics.  Everything is evaluated as truncated power series in eps (exact
coefficients mod P = 1073741789) at fixed random points X in F_P^3, vectorised
over the points with numpy (int64, every product reduced before summation).
A family member becomes a (K+1) x M array (order x evaluation coordinate,
M = 2 * npts, components 1 and 2 of the zero-sum vectors).

Saturation.  saturate() runs Gaussian elimination over F_P[[eps]]: normalise
every row by its eps-valuation, find the dependencies of the leading rows,
replace one row per dependency (reduced-echelon pivot) by the combination
and divide by eps; repeat.  The final leading rows are a basis of the flat
limit (evaluated at the points); the shifts record how deep each basis
element sits relative to the input lattice.  sum(shifts) is the length of
L_sat / L_family, i.e. the sum of the intrinsic Smith exponents.

What this library does not do: it proves nothing; ranks are mod P at random
points (a full rank certifies the generic statement for that n, a deficiency is
evidence only).
"""
import itertools as it
import random

import flint
import numpy as np

P = 1073741789          # prime < 2^30: products of two residues fit in int64
Q = 3


def inv(x):
    return pow(int(x) % P, P - 2, P)


def vinv(arr):
    return np.array([inv(x) for x in arr.ravel()], dtype=np.int64).reshape(arr.shape)


class Model:
    """Product-form persistence model: H (off-diagonal), torus elements u_t."""

    def __init__(self, n, seed=1, H=None, u=None, lo=1, hi=60):
        rng = random.Random(seed)
        self.n = n
        self.H = H if H is not None else [[0 if a == i else rng.randint(lo, hi) for i in range(Q)]
                                          for a in range(Q)]
        self.u = u if u is not None else [[rng.randint(lo, hi) for _ in range(Q)] for _ in range(n)]
        self.c = [[[(self.H[a][i] * self.u[t][i] * inv(self.u[t][a])) % P if i != a else 0
                    for i in range(Q)] for a in range(Q)] for t in range(n)]


# ---------------------------------------------------------------- series mod P
def smul(a, b, K):
    """Truncated product of series arrays (last axis = order 0..K), broadcasting."""
    shape = np.broadcast_shapes(a.shape, b.shape)
    out = np.zeros(shape, dtype=np.int64)
    for k1 in range(K + 1):
        ak = a[..., k1]
        if not ak.any():
            continue
        for k2 in range(K + 1 - k1):
            bk = b[..., k2]
            if not bk.any():
                continue
            out[..., k1 + k2] += (ak * bk) % P
    return out % P


def mat_series_mul(A, B, K):
    """(npts,3,3,K+1) x (npts,3,3,K+1)."""
    out = np.zeros(A.shape, dtype=np.int64)
    for k1 in range(K + 1):
        Ak = A[..., k1]
        if not Ak.any():
            continue
        for k2 in range(K + 1 - k1):
            Bk = B[..., k2]
            if not Bk.any():
                continue
            prod = np.zeros(A.shape[:-1], dtype=np.int64)
            for l in range(Q):
                prod += (Ak[:, :, l, None] * Bk[:, None, l, :]) % P
            out[..., k1 + k2] += prod % P
    return out % P


def vec_series_mul(v, B, K):
    """(npts,3,K+1) row vectors times (npts,3,3,K+1)."""
    out = np.zeros(v.shape, dtype=np.int64)
    for k1 in range(K + 1):
        vk = v[..., k1]
        if not vk.any():
            continue
        for k2 in range(K + 1 - k1):
            Bk = B[..., k2]
            if not Bk.any():
                continue
            prod = np.zeros(v.shape[:-1], dtype=np.int64)
            for l in range(Q):
                prod += (vk[:, l, None] * Bk[:, l, :]) % P
            out[..., k1 + k2] += prod % P
    return out % P


class PointSeries:
    """All kernels K_t of a Model as eps-series at npts random points."""

    def __init__(self, model, npts, K, seed=7, X=None):
        self.m = model
        self.K = K
        rng = random.Random(seed)
        if X is None:
            X = np.array([[rng.randint(1, P - 1) for _ in range(Q)] for _ in range(npts)], dtype=np.int64)
        self.X = X
        self.npts = X.shape[0]
        self.Xinv = vinv(X)
        n = model.n
        c = model.c
        # mu[t][a] : (npts,)
        self.mu = [[sum((c[t][a][i] * X[:, i]) % P for i in range(Q) if i != a) % P * self.Xinv[:, a] % P
                    for a in range(Q)] for t in range(n)]
        self.Kmat = [self._kernel(t) for t in range(n)]

    def fseries(self, t, a):
        """f_ta = sum_k (-mu_ta)^k eps^k as (npts, K+1)."""
        K = self.K
        out = np.zeros((self.npts, K + 1), dtype=np.int64)
        m = (-self.mu[t][a]) % P
        cur = np.ones(self.npts, dtype=np.int64)
        for k in range(K + 1):
            out[:, k] = cur
            cur = (cur * m) % P
        return out

    def _kernel(self, t):
        K = self.K
        X, Xi, c = self.X, self.Xinv, self.m.c
        M = np.zeros((self.npts, Q, Q, K + 1), dtype=np.int64)
        for a in range(Q):
            f = self.fseries(t, a)
            M[:, a, a, :] = f
            for d in range(Q):
                if d == a:
                    continue
                coef = (c[t][a][d] * X[:, d]) % P * Xi[:, a] % P
                M[:, a, d, 1:] = (coef[:, None] * f[:, :K]) % P
        return M

    def word(self, letters):
        K = self.K
        W = np.zeros((self.npts, Q, Q, K + 1), dtype=np.int64)
        for i in range(Q):
            W[:, i, i, 0] = 1
        for u in letters:
            W = mat_series_mul(W, self.Kmat[u], K)
        return W

    def nu(self, t, a):
        """nu_ta as (npts, 3) (polynomial, eps-independent)."""
        X, c = self.X, self.m.c
        v = np.zeros((self.npts, Q), dtype=np.int64)
        for i in range(Q):
            if i != a:
                v[:, i] = (c[t][a][i] * X[:, i]) % P
        v[:, a] = (-(v.sum(axis=1))) % P
        return v

    def head(self, t, a, b):
        """h_tab = X_a K_t(a,b) e_b as (npts, 3, K+1)."""
        h = np.zeros((self.npts, Q, self.K + 1), dtype=np.int64)
        h[:, b, :] = (self.X[:, a, None] * self.Kmat[t][:, a, b, :]) % P
        return h


def word_vector(ps, t, a, b, terms, cache=None):
    """sum_k coef_k h_tab (I - W_k) with sum coef in {0,1}: (npts,3,K+1)."""
    h = ps.head(t, a, b)
    tot = sum(cf for cf, _ in terms) % P
    out = (tot * h) % P
    for cf, w in terms:
        key = tuple(w)
        if cache is not None and key in cache:
            W = cache[key]
        else:
            W = ps.word(w)
            if cache is not None:
                cache[key] = W
        out = (out - cf * vec_series_mul(h, W, ps.K)) % P
    return out


def E_vector(ps, s, a):
    h = np.zeros((ps.npts, Q, ps.K + 1), dtype=np.int64)
    h[:, a, 0] = ps.X[:, a]
    return (h - vec_series_mul(h, ps.Kmat[s], ps.K)) % P


# ------------------------------------------------------------------ families
def dhw_word(t, s, n):
    return [s] + [u for u in range(n) if u not in (s, t)]


def family_terms(n, kind):
    """List of (label, (t,a,b,terms)) for kind in F (DHW), G, B, plus E handled separately."""
    out = []
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            for a in range(Q):
                for b in range(Q):
                    if kind == 'F':
                        terms = [(1, dhw_word(t, s, n))]
                    elif kind == 'G':
                        tail = [u for u in range(n) if u > s and u != t]
                        terms = [(1, [s] + tail), (-1, tail)]
                    elif kind == 'B':
                        terms = [(1, [s])]
                    else:
                        raise ValueError(kind)
                    out.append(((kind, t, s, a, b), (t, a, b, terms)))
    return out


def to_rows(vec):
    """(npts,3,K+1) zero-sum vector series -> (K+1, 2*npts) (components 1, 2)."""
    s = vec.sum(axis=1) % P
    assert not s.any(), 'not zero-sum'
    return np.concatenate([vec[:, 1, :].T, vec[:, 2, :].T], axis=1)


def family_rows(ps, kinds=('F',), with_E=True):
    n = ps.m.n
    labels, rows = [], []
    if with_E:
        for s in range(n):
            for a in range(Q):
                labels.append(('E', s, a))
                rows.append(to_rows(E_vector(ps, s, a)))
    cache = {}
    for kind in kinds:
        for lab, (t, a, b, terms) in family_terms(n, kind):
            labels.append(lab)
            rows.append(to_rows(word_vector(ps, t, a, b, terms, cache)))
    return labels, np.array(rows, dtype=np.int64)


# ---------------------------------------------------------------- linear algebra
def nmod(rows):
    rows = np.asarray(rows) % P
    return flint.nmod_mat([[int(x) for x in r] for r in rows], P)


def rank(rows):
    if len(rows) == 0:
        return 0
    return nmod(rows).rank()


def left_kernel(L):
    """Basis of {k : k L = 0} as a list of int arrays, reduced echelon with pivots
    at the LAST nonzero position of each vector (rows late in the list get replaced)."""
    d = L.shape[0]
    MT = nmod(np.asarray(L).T)          # M x d
    X, nul = MT.nullspace()
    if nul == 0:
        return []
    B = [[int(X[i, j]) for i in range(d)] for j in range(nul)]
    # reduced echelon with pivots at the last positions: reverse columns, rref, reverse back
    Rv = flint.nmod_mat([list(reversed(r)) for r in B], P).rref()[0]
    out = []
    for i in range(nul):
        r = [int(Rv[i, j]) for j in range(d)]
        out.append(np.array(list(reversed(r)), dtype=np.int64))
    return out


def valuation(series_row):
    """First order with a nonzero entry; None if all zero."""
    nz = np.nonzero(series_row.any(axis=1))[0]
    return int(nz[0]) if len(nz) else None


def saturate(rows, K, track=False, max_rounds=60, verbose=False):
    """rows: (d, K+1, M) series.  Returns dict with
    shifts (total division count per final row), lead (d x M leading rows),
    prec (remaining precision), rounds, and optionally T (Laurent combination
    coefficients: T[j] = dict order -> coefficient vector over the input rows)."""
    S = np.array(rows, dtype=np.int64) % P
    d = S.shape[0]
    prec = np.full(d, K, dtype=np.int64)       # orders 0..prec are exact
    shifts = np.zeros(d, dtype=np.int64)
    T = None
    if track:
        T = [{0: np.eye(d, dtype=np.int64)[j]} for j in range(d)]
    history = []
    for rnd in range(max_rounds):
        # normalise
        for j in range(d):
            v = valuation(S[j, :prec[j] + 1])
            if v is None:
                raise RuntimeError(f'row {j} vanished to its precision {prec[j]} (increase K)')
            if v > 0:
                S[j, :K + 1 - v] = S[j, v:]
                S[j, K + 1 - v:] = 0
                prec[j] -= v
                shifts[j] += v
                if track:
                    T[j] = {o - v: c for o, c in T[j].items()}
        L = S[:, 0, :]
        ker = left_kernel(L)
        history.append(len(ker))
        if verbose:
            print(f'  round {rnd}: {len(ker)} dependencies, min prec {prec.min()}', flush=True)
        if not ker:
            return dict(shifts=shifts, lead=L.copy(), prec=prec, rounds=rnd, T=T, S=S, history=history)
        newS = S.copy()
        newprec = prec.copy()
        newT = list(T) if track else None
        for kv in ker:
            nzi = np.nonzero(kv)[0]
            j = int(nzi[-1])
            comb = np.zeros_like(S[0])
            for i in nzi:
                comb = (comb + int(kv[i]) * S[i]) % P
            assert not comb[0].any()
            newS[j, :K] = comb[1:]
            newS[j, K] = 0
            newprec[j] = int(prec[nzi].min()) - 1
            shifts[j] += 1
            if track:
                acc = {}
                for i in nzi:
                    for o, cvec in T[i].items():
                        acc[o - 1] = (acc.get(o - 1, 0) + int(kv[i]) * cvec) % P
                newT[j] = acc
        S, prec = newS, newprec
        if track:
            T = newT
        if prec.min() < 0:
            raise RuntimeError('precision exhausted (increase K)')
    raise RuntimeError('too many rounds')


def series_rank_profile(rows, K):
    """Smith exponents of the (d x M) matrix over F_P[[eps]] (truncated at K) via
    saturate(): returns sorted shifts."""
    res = saturate(rows, K)
    return sorted(int(x) for x in res['shifts'])


if __name__ == '__main__':
    # quick self-test: kernels are row-stochastic and match the defining formula
    m = Model(3, seed=2)
    ps = PointSeries(m, 4, 5)
    for t in range(3):
        rs = ps.Kmat[t].sum(axis=2) % P
        assert (rs[:, :, 0] == 1).all() and not rs[:, :, 1:].any()
    # definition: K_t(a,i) * L_ta(eps) = A_t(a,i)(eps) X_i  as series (L_ta = u_t(a) X_a + eps sum H(a,i)u_t(i)X_i)
    K = ps.K
    for t in range(3):
        for a in range(Q):
            L = np.zeros((ps.npts, K + 1), dtype=np.int64)
            L[:, 0] = (m.u[t][a] * ps.X[:, a]) % P
            L[:, 1] = sum((m.H[a][i] * m.u[t][i] * ps.X[:, i]) % P for i in range(Q) if i != a) % P
            for i in range(Q):
                lhs = smul(ps.Kmat[t][:, a, i, :], L, K)
                rhs = np.zeros_like(lhs)
                rhs[:, 0] = (m.u[t][i] * ps.X[:, i]) % P if i == a else 0
                rhs[:, 1] = 0 if i == a else (m.H[a][i] * m.u[t][i] * ps.X[:, i]) % P
                assert (lhs % P == rhs % P).all()
    print('selftest: K_t series are row-stochastic and satisfy K_t(a,i) L_ta = A_t(a,i) X_i to order', K)
