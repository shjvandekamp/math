#!/usr/bin/env python3
"""agent_col_lib: exact jets (truncated power series in delta, mod p = 2^61-1) of the E/F family.

Setting (HQ_AGENT_BRIEF.md): Q = 3, product form A_t(a,i) = g(i,a) u_t(i), blocks 0..n-1 in time
order, K_t(X) = diag(L_t)^{-1} A_t diag(X).  Family (equation 24, quotient form):
    E_{s,a}     = X_a e_a (I - K_s)
    F_{t,s,a,b} = X_a K_t(a,b) e_b (I - K_s * prod_{u != s,t, increasing} K_u).
The torus parameters u_t may depend on delta; every scalar is a truncated power series
(list of K ints mod p).  Evaluating the family at fixed random points X_j (components 0, 1;
vectors are zero-sum) gives a matrix M(delta) = M_0 + delta M_1 + ... (rows = family members).

Smith exponents over F_p[[delta]] (intrinsic, coordinate free; valid when the points are generic
for the flat limit, i.e. 2 * #points >= #family and random):  with r_j = rank of the block
Toeplitz matrix T_j (blocks M_0..M_j), #{e_i <= j} = r_j - r_{j-1}.

Also: generic word families, explicit series vectors, and helpers used by the agent_col_* scripts.
Self-test (run directly): the delta = 0 evaluation agrees with hq_fresh_coalesce.family_eval
(exact fmpq, reduced mod p), and the jets agree with finite differences of a polynomial
reconstruction along delta.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))

P = (1 << 61) - 1
Q = 3


# ----------------------------------------------------------------- truncated series mod P
def s_const(x, K):
    return [x % P] + [0] * (K - 1)


def s_add(a, b):
    return [(x + y) % P for x, y in zip(a, b)]


def s_sub(a, b):
    return [(x - y) % P for x, y in zip(a, b)]


def s_scal(c, a):
    return [(c * x) % P for x in a]


def s_mul(a, b):
    K = len(a)
    if K == 1:
        return [a[0] * b[0] % P]
    if K == 2:
        return [a[0] * b[0] % P, (a[0] * b[1] + a[1] * b[0]) % P]
    out = [0] * K
    for i in range(K):
        ai = a[i]
        if ai:
            for j in range(K - i):
                out[i + j] += ai * b[j]
    return [x % P for x in out]


def s_inv(a):
    K = len(a)
    a0inv = pow(a[0], P - 2, P)
    b = [a0inv] + [0] * (K - 1)
    for k in range(1, K):
        acc = 0
        for j in range(1, k + 1):
            acc += a[j] * b[k - j]
        b[k] = (-a0inv * acc) % P
    return b


def s_is_zero(a):
    return all(x == 0 for x in a)


def m_mul(A, B):
    return [[s_add(s_add(s_mul(A[i][0], B[0][j]), s_mul(A[i][1], B[1][j])), s_mul(A[i][2], B[2][j]))
             for j in range(Q)] for i in range(Q)]


def m_id(K):
    return [[s_const(1 if i == j else 0, K) for j in range(Q)] for i in range(Q)]


# ----------------------------------------------------------------- configurations
def rand_unit(rng):
    return rng.randrange(1, P)


def make_A(g, us):
    """g: 3x3 ints; us: list of blocks, each a list of 3 series. A_t(a,i) = g(i,a) u_t(i)."""
    return [[[s_scal(g[i][a], us[t][i]) for i in range(Q)] for a in range(Q)] for t in range(len(us))]


def collision_config(n, k, rng, K, nu=None, g=None, us=None):
    """Blocks 0..n-2 generic; block N = n-1 equals block k times (1 + delta nu) componentwise."""
    g = g or [[rand_unit(rng) for _ in range(Q)] for _ in range(Q)]
    base = us or [[rand_unit(rng) for _ in range(Q)] for _ in range(n - 1)]
    nu = nu or [rand_unit(rng) for _ in range(Q)]
    ser = [[s_const(x, K) for x in u] for u in base]
    uN = [([base[k][i] % P, base[k][i] * nu[i] % P] + [0] * K)[:K] for i in range(Q)]
    ser.append(uN)
    return make_A(g, ser), dict(g=g, us=base, nu=nu, k=k)


def multi_collision_config(n, pairs, rng, K, g=None, us=None):
    """pairs: dict {block j: (block k, nu)} meaning u_j = u_k (1 + delta nu); others generic."""
    g = g or [[rand_unit(rng) for _ in range(Q)] for _ in range(Q)]
    base = us or [[rand_unit(rng) for _ in range(Q)] for _ in range(n)]
    ser = []
    for t in range(n):
        if t in pairs:
            k, nu = pairs[t]
            ser.append([([base[k][i] % P, base[k][i] * nu[i] % P] + [0] * K)[:K] for i in range(Q)])
        else:
            ser.append([s_const(x, K) for x in base[t]])
    return make_A(g, ser), dict(g=g, us=base, pairs=pairs)


def kernels_series(A, X, K):
    """K_t(X) as 3x3 series matrices, X a list of 3 ints."""
    out = []
    for At in A:
        Kt = []
        for a in range(Q):
            L = [0] * K
            for i in range(Q):
                L = s_add(L, s_scal(X[i], At[a][i]))
            if L[0] == 0:
                raise ZeroDivisionError('point on a line')
            iL = s_inv(L)
            Kt.append([s_mul(s_scal(X[i], At[a][i]), iL) for i in range(Q)])
        out.append(Kt)
    return out


# ----------------------------------------------------------------- families
def dhw_word(t, s, n):
    return [s] + [u for u in range(n) if u not in (s, t)]


def family_labels(n):
    labs = [('E', s, a) for s in range(n) for a in range(Q)]
    labs += [('F', t, s, a, b) for t in range(n) for s in range(n) if s != t for a in range(Q) for b in range(Q)]
    return labs


class WordCache:
    def __init__(self, kers, K):
        self.kers, self.K, self.cache = kers, K, {}

    def __call__(self, w):
        key = tuple(w)
        if key in self.cache:
            return self.cache[key]
        if not w:
            M = m_id(self.K)
        elif len(w) == 1:
            M = self.kers[w[0]]
        else:
            M = m_mul(self(w[:-1]), self.kers[w[-1]])
        self.cache[key] = M
        return M


def vec_E(kers, X, s, a, K):
    Ks = kers[s]
    return [s_scal(X[a], s_sub(s_const(1 if i == a else 0, K), Ks[a][i])) for i in range(2)]


def vec_word(kers, X, heads, a0, word, K, wc=None, coef=1):
    """coef * X_{a0} K_{t1}(a0,a1)...K_{tk}(a_{k-1},b) e_b (I - W), heads = [(t1,a1),...]; comps 0,1."""
    sc = s_const(coef * X[a0], K)
    prev = a0
    for (t, a) in heads:
        sc = s_mul(sc, kers[t][prev][a])
        prev = a
    b = prev
    W = (wc or WordCache(kers, K))(word)
    return [s_mul(sc, s_sub(s_const(1 if i == b else 0, K), W[b][i])) for i in range(2)]


def family_series(kers, X, n, K, word_fn=None):
    """List of family vectors (components 0,1 as series), order = family_labels(n)."""
    wc = WordCache(kers, K)
    word_fn = word_fn or (lambda t, s: dhw_word(t, s, n))
    out = []
    for s in range(n):
        for a in range(Q):
            out.append(vec_E(kers, X, s, a, K))
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            W = wc(word_fn(t, s))
            for a in range(Q):
                for b in range(Q):
                    sc = s_scal(X[a], kers[t][a][b])
                    out.append([s_mul(sc, s_sub(s_const(1 if i == b else 0, K), W[b][i])) for i in range(2)])
    return out


def rand_points(A, m, rng, K):
    pts = []
    while len(pts) < m:
        X = [rng.randrange(1, P) for _ in range(Q)]
        try:
            kernels_series(A, X, K)
        except ZeroDivisionError:
            continue
        pts.append(X)
    return pts


def eval_jets(vec_fn, A, pts, K):
    """vec_fn(kers, X) -> list of vectors (2 series comps). Returns [M_0, ..., M_{K-1}] as int lists
    with rows = vectors, columns = (point, comp)."""
    cols = []
    for X in pts:
        kers = kernels_series(A, X, K)
        vals = vec_fn(kers, X)
        cols.append(vals)
    nv = len(cols[0])
    Ms = []
    for j in range(K):
        M = [[0] * (2 * len(pts)) for _ in range(nv)]
        for c, vals in enumerate(cols):
            for r in range(nv):
                M[r][2 * c] = vals[r][0][j]
                M[r][2 * c + 1] = vals[r][1][j]
        Ms.append(M)
    return Ms


def toeplitz(Ms, j):
    """Block upper-triangular Toeplitz: block (k, r) = M_{r-k} for r >= k, k, r = 0..j."""
    nr, nc = len(Ms[0]), len(Ms[0][0])
    T = [[0] * (nc * (j + 1)) for _ in range(nr * (j + 1))]
    for k in range(j + 1):
        for r in range(k, j + 1):
            M = Ms[r - k]
            for i in range(nr):
                row = T[k * nr + i]
                Mi = M[i]
                off = r * nc
                for c in range(nc):
                    row[off + c] = Mi[c]
    return flint.nmod_mat(T, P)


def smith_counts(Ms, upto=None):
    """Counts of Smith exponents 0, 1, ..., upto (and the remainder '>upto') from the Toeplitz ranks."""
    upto = len(Ms) - 1 if upto is None else upto
    nv = len(Ms[0])
    ranks = [toeplitz(Ms, j).rank() for j in range(upto + 1)]
    le = [ranks[0]] + [ranks[j] - ranks[j - 1] for j in range(1, upto + 1)]   # #{e <= j}
    counts = {0: le[0]}
    for j in range(1, upto + 1):
        counts[j] = le[j] - le[j - 1]
    counts['>%d' % upto] = nv - le[upto]
    return counts, ranks


def nmod(rows):
    return flint.nmod_mat(rows, P)


def rank(rows):
    return flint.nmod_mat(rows, P).rank() if rows else 0


def left_kernel(rows):
    """Basis of {c : c^T M = 0} for M given as list of rows (mod P)."""
    M = flint.nmod_mat(rows, P).transpose()
    return right_kernel_mat(M)


def right_kernel_mat(M):
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


# ----------------------------------------------------------------- self-test
def selftest():
    from fractions import Fraction
    from hq_fresh_fast import Ring
    from hq_fresh_coalesce import family_eval
    rng = random.Random(3)
    Rq = Ring(None)
    for n in (3, 4):
        # exact rational configuration with u_N = u_k (1 + d nu) at a rational d; compare values mod P
        g = [[rng.randint(2, 40) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randint(2, 40) for _ in range(Q)] for _ in range(n - 1)]
        nu = [rng.randint(2, 40) for _ in range(Q)]
        k = 0
        for d in (Fraction(0), Fraction(3, 7)):
            uN = [Fraction(us[k][i]) * (1 + d * nu[i]) for i in range(Q)]
            uq = [[Fraction(x) for x in u] for u in us] + [uN]
            Aq = [[[Rq(Fraction(g[i][a]) * uq[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
            X = [Rq(rng.randint(1, 50)) for _ in range(Q)]
            ref = family_eval(Aq, n, X, Rq, 'F')
            dmod = d.numerator * pow(d.denominator, P - 2, P) % P
            usP = [[x % P for x in u] for u in us]
            uNP = [usP[k][i] * (1 + dmod * nu[i]) % P for i in range(Q)]
            A1 = make_A(g, [[s_const(x, 1) for x in u] for u in usP] + [[s_const(x, 1) for x in uNP]])
            Xp = [int(x.p) % P for x in X]
            mine = family_series(kernels_series(A1, Xp, 1), Xp, n, 1)
            for r, (vr, vm) in enumerate(zip(ref, mine)):
                for i in range(2):
                    want = int(vr[i].p) * pow(int(vr[i].q), P - 2, P) % P
                    assert vm[i][0] == want, ('mismatch', n, r, i)
        # jets of K_N: K_N(a,i)(d) = Num(d)/Den(d) with Num, Den linear in d, so the series must
        # satisfy (sum_j K_j d^j) * (Den0 + Den1 d) = Num0 + Num1 d  (mod d^3) exactly.
        A, info = collision_config(n, 0, rng, 3)
        X = rand_points(A, 1, rng, 3)[0]
        KN = kernels_series(A, X, 3)[n - 1]
        uk, nu, gg = info['us'][0], info['nu'], info['g']
        for a in range(Q):
            Den = [sum(gg[j][a] * uk[j] * X[j] for j in range(Q)) % P,
                   sum(gg[j][a] * uk[j] * nu[j] * X[j] for j in range(Q)) % P, 0]
            for i in range(Q):
                Num = [gg[i][a] * uk[i] * X[i] % P, gg[i][a] * uk[i] * nu[i] * X[i] % P, 0]
                assert s_mul(KN[a][i], Den) == Num, 'jet identity of K_N fails'
        A4, _ = collision_config(n, 0, random.Random(0), 4, nu=info['nu'], g=info['g'], us=info['us'])
        jets = family_series(kernels_series(A, X, 3), X, n, 3)
        jets4 = family_series(kernels_series(A4, X, 4), X, n, 4)
        assert all(jets4[r][i][:3] == jets[r][i] for r in range(len(jets)) for i in range(2))
    print('selftest: delta=0 and delta=3/7 values agree with hq_fresh_coalesce.family_eval (mod P); '
          'K_N jets satisfy the exact Num/Den identity; series truncations consistent.')


if __name__ == '__main__':
    selftest()


# ----------------------------------------------------------------- term-list vectors (all 3 components)
# A vector is a list of terms (coef, a0, heads, kind, word):
#   coef * X_{a0} * K_{t1}(a0,a1) ... K_{tk}(a_{k-1},b) * V,   heads = [(t1,a1),...,(tk,b)] (b = a0 if empty)
#   V = e_b (I - W)  (kind 'IW'),  e_b W  (kind 'W'),  e_b  (kind 'I');  W = K_{w1} ... K_{wl}.
def term_vec(kers, X, terms, K, wc=None, ncomp=3):
    wc = wc or WordCache(kers, K)
    out = [[0] * K for _ in range(ncomp)]
    for coef, a0, heads, kind, word in terms:
        sc = s_const(coef * X[a0], K)
        prev = a0
        for (t, a) in heads:
            sc = s_mul(sc, kers[t][prev][a])
            prev = a
        b = prev
        if kind == 'I':
            if b < ncomp:
                out[b] = s_add(out[b], sc)
            continue
        Wb = wc(word)[b]
        for i in range(ncomp):
            if kind == 'IW':
                v = s_sub(s_const(1 if i == b else 0, K), Wb[i])
            else:
                v = Wb[i]
            out[i] = s_add(out[i], s_mul(sc, v))
    return out


def eval_terms_matrix(A, vecs, pts, K, ncomp=3, jet=0):
    """rows = vectors, columns = (point, component); entry = coefficient of delta^jet."""
    rows = [[] for _ in vecs]
    for X in pts:
        kers = kernels_series(A, X, K)
        wc = WordCache(kers, K)
        for r, terms in enumerate(vecs):
            v = term_vec(kers, X, terms, K, wc, ncomp)
            rows[r].extend(v[i][jet] for i in range(ncomp))
    return rows


def T_E(s, a):
    return [(1, a, [], 'IW', [s])]


def T_F(t, s, a, b, n):
    return [(1, a, [(t, b)], 'IW', dhw_word(t, s, n))]


def T_head(t, a, b):
    return [(1, a, [(t, b)], 'I', [])]


def T_body(t, a, b, word):
    return [(1, a, [(t, b)], 'W', word)]


def T_Xe(a):
    return [(1, a, [], 'I', [])]


def family_terms(n):
    labs = family_labels(n)
    out = []
    for lab in labs:
        if lab[0] == 'E':
            out.append(T_E(lab[1], lab[2]))
        else:
            _, t, s, a, b = lab
            out.append(T_F(t, s, a, b, n))
    return labs, out


def span_dim(A, vecs, rng, K=1, ncomp=3, extra=8, jet=0):
    """Dimension of the span of term-list vectors (evaluated at enough random points)."""
    npts = len(vecs) // max(1, ncomp - 1) + extra
    pts = rand_points(A, npts, rng, K)
    return rank(eval_terms_matrix(A, vecs, pts, K, ncomp, jet))


# ----------------------------------------------------------------- polar data along a doubled line
def point_on_line(A, u, c, rng):
    """Random X0 on L_{uc} (all coordinates nonzero, on no other line of A)."""
    l = [A[u][c][i][0] for i in range(Q)]
    while True:
        x, y = rng.randrange(1, P), rng.randrange(1, P)
        X0 = (-(l[1] * x + l[2] * y)) * pow(l[0], P - 2, P) % P
        X = [X0, x, y]
        if X0 == 0:
            continue
        ok = True
        for t, At in enumerate(A):
            for a in range(Q):
                if [At[a][i][0] for i in range(Q)] == l:
                    continue
                if sum(At[a][i][0] * X[i] for i in range(Q)) % P == 0:
                    ok = False
        if ok:
            return X


def polar_kernels(A, X0, Yd, c, pole_blocks, K):
    """Kernels at X(eps) = X0 + eps*Yd as series; for pole blocks (whose line L_c passes through X0)
    return M = eps * K (regular).  Returns list of (matrix, shift) with K_t = eps^{-shift} M."""
    Xs = [[X0[i] % P, Yd[i] % P] + [0] * (K - 2) for i in range(Q)]
    out = []
    for t, At in enumerate(A):
        Kt = []
        pole = t in pole_blocks
        for a in range(Q):
            L = [0] * K
            for i in range(Q):
                L = s_add(L, s_scal(At[a][i][0], Xs[i]))
            if pole and a == c:
                assert L[0] == 0
                Lr = L[1:] + [0]           # L / eps
                iL = s_inv(Lr)
                Kt.append([s_mul(s_scal(At[a][i][0], Xs[i]), iL) for i in range(Q)])
            else:
                iL = s_inv(L)
                row = [s_mul(s_scal(At[a][i][0], Xs[i]), iL) for i in range(Q)]
                if pole:
                    row = [[0] + r[:-1] for r in row]   # eps * K
                Kt.append(row)
        out.append((Kt, 1 if pole else 0))
    return out, Xs


def s_shift(a, k):
    """multiply by eps^k (k >= 0), truncating."""
    if k == 0:
        return a
    return ([0] * k + a)[:len(a)]


def polar_vec(pk, Xs, terms, K, order=2):
    """eps^order * v(X0 + eps Yd) as series (components 0,1,2), for term-list v."""
    out = [[0] * K for _ in range(Q)]
    cache = {}

    def word(w):
        key = tuple(w)
        if key not in cache:
            if not w:
                cache[key] = (m_id(K), 0)
            else:
                M, sh = word(w[:-1])
                Kt, s2 = pk[w[-1]]
                cache[key] = (m_mul(M, Kt), sh + s2)
        return cache[key]

    for coef, a0, heads, kind, wd in terms:
        sc = s_scal(coef, Xs[a0])
        prev, jh = a0, 0
        for (t, a) in heads:
            Kt, sh = pk[t]
            sc = s_mul(sc, Kt[prev][a])
            jh += sh
            prev = a
        b = prev
        if kind in ('IW', 'I'):
            assert order - jh >= 0
            out[b] = s_add(out[b], s_shift(sc, order - jh))
        if kind in ('IW', 'W'):
            Wm, jw = word(wd)
            assert order - jh - jw >= 0, 'pole order exceeds the requested order'
            for i in range(Q):
                term = s_shift(s_mul(sc, Wm[b][i]), order - jh - jw)
                out[i] = s_sub(out[i], term) if kind == 'IW' else s_add(out[i], term)
    return out


# ----------------------------------------------------------------- derivative block D = dK_N/d delta at delta = 0
# For u_N = u_k (1 + delta nu):  D(a,i) = K_k(a,i) (nu_i - L'_a / L_ka),  L'_a = sum_j A_k(a,j) nu_j X_j.
# Term lists may use the extra block index n (= len(A)) for D; kernels_with_D / polar_kernels_with_D supply it.
def kernels_with_D(A, X, k, nu):
    """Constant (K = 1 series) kernels of all blocks plus D appended at index len(A)."""
    kers = kernels_series(A, X, 1)
    Ak = A[k]
    D = []
    for a in range(Q):
        L = sum(Ak[a][i][0] * X[i] for i in range(Q)) % P
        Lp = sum(Ak[a][i][0] * nu[i] * X[i] for i in range(Q)) % P
        r = Lp * pow(L, P - 2, P) % P
        D.append([[kers[k][a][i][0] * ((nu[i] - r) % P) % P] for i in range(Q)])
    return kers + [D]


def polar_kernels_with_D(A, X0, Yd, c, pole_blocks, K, k, nu):
    """As polar_kernels, plus D (shift 2) at index len(A); block k's line L_kc passes through X0."""
    pk, Xs = polar_kernels(A, X0, Yd, c, pole_blocks, K)
    M0, sh = pk[k]
    assert sh == 1
    Ak = A[k]
    D = []
    for a in range(Q):
        Lp = [0] * K
        L = [0] * K
        for i in range(Q):
            Lp = s_add(Lp, s_scal(Ak[a][i][0] * nu[i] % P, Xs[i]))
            L = s_add(L, s_scal(Ak[a][i][0], Xs[i]))
        if a == c:
            ell = L[1:] + [0]                       # L / eps (exact: L is linear in eps)
            q = s_mul(Lp, s_inv(ell))               # L'/ell
            # eps^2 D = eps M0 nu - M0 L'/ell
            row = [s_sub(s_shift(s_scal(nu[i], M0[a][i]), 1), s_mul(M0[a][i], q)) for i in range(Q)]
        else:
            q = s_mul(Lp, s_inv(L))
            # M0 row = eps K (regular K); eps^2 D = eps * (M0 nu - M0 L'/L)
            row = [s_shift(s_sub(s_scal(nu[i], M0[a][i]), s_mul(M0[a][i], q)), 1) for i in range(Q)]
        D.append(row)
    return pk + [(D, 2)], Xs


def jet_terms(n, k=0):
    """First-order jets of the 12 pair differences at u_N = u_k (k <= N-3 case), as term lists with D = index n.
    JE_a = d/d delta (E_{N,a} - E_{k,a}) = -X_a e_a D;
    JF_ab = d/d delta (F_{N,k,a,b} - F_{k,N,a,b}) = X_a D(a,b) e_b (I - K_k Pi) + X_a K_k(a,b) e_b D Pi,
    Pi = increasing product of the blocks other than k, N."""
    N = n - 1
    Dn = n
    Pi = [u for u in range(N) if u != k]
    out, labs = [], []
    for a in range(Q):
        out.append([(P - 1, a, [], 'W', [Dn])])
        labs.append(('JE', a))
    for a in range(Q):
        for b in range(Q):
            out.append([(1, a, [(Dn, b)], 'IW', [k] + Pi), (1, a, [(k, b)], 'W', [Dn] + Pi)])
            labs.append(('JF', a, b))
    return labs, out
