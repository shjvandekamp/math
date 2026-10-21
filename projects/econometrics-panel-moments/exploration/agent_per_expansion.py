#!/usr/bin/env python3
"""Task 1: closed-form eps-expansion of E, B, F (DHW) and G in the persistence limit.

Setting: A_t(a,i) = (delta_ai + eps H(a,i)) u_t(i), H(a,a) = 0 (g = I + eps H^T),
c_{t,a,i} = H(a,i) u_t(i)/u_t(a), lam_ta = sum_{i!=a} c_{t,a,i} X_i, mu_ta = lam_ta/X_a,
f_ta = X_a/(X_a + eps lam_ta), nu_ta = sum_{i!=a} c_{t,a,i} X_i (e_i - e_a).

Claims checked (all EXACT over Q at random rational points, as power series in eps
truncated at order K; the series are computed from the DEFINITION of A_t by series
division, an independent code path from the closed forms):

 (X1) K_t(a,a) = f_ta,  K_t(a,d) = eps c_{t,a,d} (X_d/X_a) f_ta (d != a).
 (X2) E_{s,a} = -eps f_sa nu_sa;  B_{t,s,a,b} = -eps (delta_ab + eps c_tab) f_ta f_sb nu_sb.
 (X3) word vectors h_tab (I - W), W = K_{w1}...K_{wm} (distinct letters, t not in w):
      a = b:  order 1: -sum_{u in w} nu_ua
              order 2:  mu_ta sum_u nu_ua + sum_u mu_ua nu_ua - sum_{i<j} nu_{w_i a} N_{w_j}
      a != b: order 1: 0;  order 2: -c_tab sum_u nu_ub
              order 3:  c_tab [mu_ta sum_u nu_ub + sum_u mu_ub nu_ub - sum_{i<j} nu_{w_i b} N_{w_j}]
      with  nu_ua N_v = sum_{c != a} c_{u,a,c} nu_vc - mu_ua nu_va   (exact identity).
 (X4) DHW differences (s_min = smallest block != t):
      [F_{t,s,a,a} - F_{t,s_min,a,a}]_2 = -sum_{v<s, v!=t} X_a e_a [N_s, N_v]
      X_a e_a [N_s, N_v] = sum_{c!=a} (c_{s,a,c} nu_vc - c_{v,a,c} nu_sc) + mu_va nu_sa - mu_sa nu_va.
 (X5) cross-check of the definition series against the project's own evaluator
      hq_fresh_coalesce.family_eval at eps = l = 10007: v_l(exact - truncated series) > K.

What this does not show: anything about ranks; the identities are exact algebra and
the script checks them at a few random rational points only.
"""
import itertools as it
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_coalesce import family_eval  # noqa: E402
from hq_fresh_fast import Ring  # noqa: E402

Q = 3
fq = flint.fmpq


# ------------------------------------------------------------- exact series over Q
class Ser:
    __slots__ = ('c',)

    def __init__(self, coeffs):
        self.c = list(coeffs)

    @staticmethod
    def const(x, K):
        return Ser([fq(x)] + [fq(0)] * K)

    def __add__(self, o):
        return Ser([x + y for x, y in zip(self.c, o.c)])

    def __sub__(self, o):
        return Ser([x - y for x, y in zip(self.c, o.c)])

    def __neg__(self):
        return Ser([-x for x in self.c])

    def __mul__(self, o):
        if not isinstance(o, Ser):
            return Ser([x * o for x in self.c])
        K = len(self.c) - 1
        out = [fq(0)] * (K + 1)
        for i, x in enumerate(self.c):
            if x == 0:
                continue
            for j in range(K + 1 - i):
                if o.c[j] != 0:
                    out[i + j] += x * o.c[j]
        return Ser(out)

    __rmul__ = __mul__

    def inv(self):
        K = len(self.c) - 1
        a0 = self.c[0]
        out = [fq(0)] * (K + 1)
        out[0] = 1 / a0
        for k in range(1, K + 1):
            s = sum((self.c[j] * out[k - j] for j in range(1, k + 1)), fq(0))
            out[k] = -s / a0
        return Ser(out)


def kernel_def(H, ut, X, K):
    """K_t from the definition A_t = (I + eps H) diag(u_t) by series division."""
    M = [[None] * Q for _ in range(Q)]
    for a in range(Q):
        L = Ser([fq(ut[a]) * X[a], sum((fq(H[a][i]) * ut[i] * X[i] for i in range(Q) if i != a), fq(0))]
                + [fq(0)] * (K - 1))
        Li = L.inv()
        for i in range(Q):
            num = Ser([fq(ut[i]) * X[i] if i == a else fq(0), fq(H[a][i]) * ut[i] * X[i] if i != a else fq(0)]
                      + [fq(0)] * (K - 1))
            M[a][i] = num * Li
    return M


def matmul(A, B):
    return [[A[i][0] * B[0][j] + A[i][1] * B[1][j] + A[i][2] * B[2][j] for j in range(Q)] for i in range(Q)]


def ident(K):
    return [[Ser.const(1 if i == j else 0, K) for j in range(Q)] for i in range(Q)]


def word(Ks, letters, K):
    W = ident(K)
    for u in letters:
        W = matmul(W, Ks[u])
    return W


def head(Ks, X, t, a, b, K):
    return [Ks[t][a][b] * fq(X[a]) if i == b else Ser.const(0, K) for i in range(Q)]


def vecmat(v, M):
    return [v[0] * M[0][j] + v[1] * M[1][j] + v[2] * M[2][j] for j in range(Q)]


def wordvec(Ks, X, t, a, b, w, K):
    h = head(Ks, X, t, a, b, K)
    hw = vecmat(h, word(Ks, w, K))
    return [h[i] - hw[i] for i in range(Q)]


def coeff(vec, k):
    return [x.c[k] for x in vec]


# ------------------------------------------------------------- closed forms (exact)
class Closed:
    def __init__(self, H, us, X):
        self.X = [fq(x) for x in X]
        n = len(us)
        self.c = [[[fq(H[a][i]) * us[t][i] / us[t][a] if i != a else fq(0) for i in range(Q)]
                   for a in range(Q)] for t in range(n)]
        self.lam = [[sum((self.c[t][a][i] * self.X[i] for i in range(Q) if i != a), fq(0)) for a in range(Q)]
                    for t in range(n)]
        self.mu = [[self.lam[t][a] / self.X[a] for a in range(Q)] for t in range(n)]

    def nu(self, t, a):
        v = [self.c[t][a][i] * self.X[i] if i != a else fq(0) for i in range(Q)]
        v[a] = -self.lam[t][a]
        return v

    def N(self, t):
        """N_t(a,i) = c X_i/X_a (i != a), N_t(a,a) = -mu_ta."""
        return [[(self.c[t][a][i] * self.X[i] / self.X[a]) if i != a else -self.mu[t][a] for i in range(Q)]
                for a in range(Q)]

    def nuN(self, u, a, v):
        """nu_ua N_v via the identity sum_{c != a} c_{u,a,c} nu_vc - mu_ua nu_va."""
        out = [-self.mu[u][a] * x for x in self.nu(v, a)]
        for cc in range(Q):
            if cc != a:
                out = [o + self.c[u][a][cc] * x for o, x in zip(out, self.nu(v, cc))]
        return out

    def f(self, t, a, k):
        """order-k coefficient of f_ta = sum (-eps mu)^k."""
        return (-self.mu[t][a]) ** k

    def word_closed(self, t, a, b, w):
        """orders 1, 2, 3 of h_tab (I - W) (order 3 only for a != b)."""
        add = lambda p, q: [x + y for x, y in zip(p, q)]  # noqa: E731
        sc = lambda s, p: [s * x for x in p]  # noqa: E731
        zero = [fq(0)] * Q
        e = a if a == b else b
        S1 = zero
        T2 = zero
        for u in w:
            S1 = add(S1, self.nu(u, e))
            T2 = add(T2, sc(self.mu[u][e], self.nu(u, e)))
        S2 = zero
        for i, j in it.combinations(range(len(w)), 2):
            S2 = add(S2, self.nuN(w[i], e, w[j]))
        second = add(add(sc(self.mu[t][a], S1), T2), sc(fq(-1), S2))
        if a == b:
            return {1: sc(fq(-1), S1), 2: second}
        ctab = self.c[t][a][b]
        return {1: zero, 2: sc(-ctab, S1), 3: sc(ctab, second)}


def check_point(seed, n, K=5, verbose=False):
    rng = random.Random(seed)
    H = [[0 if a == i else rng.randint(1, 30) for i in range(Q)] for a in range(Q)]
    us = [[rng.randint(1, 30) for _ in range(Q)] for _ in range(n)]
    X = [rng.randint(1, 30) for _ in range(Q)]
    Ks = [kernel_def(H, us[t], X, K) for t in range(n)]
    C = Closed(H, us, X)
    ok = {k: True for k in ('X1', 'X2', 'X3', 'X4', 'nuN')}
    # X1
    for t in range(n):
        for a in range(Q):
            for d in range(Q):
                for k in range(K + 1):
                    if d == a:
                        want = C.f(t, a, k)
                    else:
                        want = C.c[t][a][d] * C.X[d] / C.X[a] * C.f(t, a, k - 1) if k >= 1 else fq(0)
                    ok['X1'] &= Ks[t][a][d].c[k] == want
    # X2
    for s in range(n):
        for a in range(Q):
            Ev = [fq(X[a]) * (1 if i == a else 0) - fq(X[a]) * 0 for i in range(Q)]
            Ev = [Ser.const(X[a] if i == a else 0, K) - Ks[s][a][i] * fq(X[a]) for i in range(Q)]
            for k in range(K + 1):
                want = [fq(0)] * Q if k == 0 else [-C.f(s, a, k - 1) * x for x in C.nu(s, a)]
                ok['X2'] &= coeff(Ev, k) == want
    for t, s in it.permutations(range(n), 2):
        for a, b in it.product(range(Q), repeat=2):
            Bv = wordvec(Ks, X, t, a, b, [s], K)
            for k in range(K + 1):
                # -eps (delta + eps c) f_ta f_sb nu_sb
                tot = fq(0)
                for k1 in range(k):           # eps^1 * f f product of order k-1 (delta part)
                    pass
                fprod = lambda m: sum((C.f(t, a, i) * C.f(s, b, m - i) for i in range(m + 1)), fq(0))  # noqa: E731
                coefk = fq(0)
                if a == b and k >= 1:
                    coefk = -fprod(k - 1)
                if a != b and k >= 2:
                    coefk = -C.c[t][a][b] * fprod(k - 2)
                ok['X2'] &= coeff(Bv, k) == [coefk * x for x in C.nu(s, b)]
    # nuN identity
    for u, v in it.permutations(range(n), 2):
        for a in range(Q):
            Nv = C.N(v)
            direct = [sum((C.nu(u, a)[cc] * Nv[cc][j] for cc in range(Q)), fq(0)) for j in range(Q)]
            ok['nuN'] &= direct == C.nuN(u, a, v)
    # X3: DHW words, G words (two-term), random words
    words = []
    for t in range(n):
        others = [u for u in range(n) if u != t]
        for s in others:
            words.append((t, [s] + [u for u in others if u != s]))
        for k in range(1, len(others) + 1):
            for w in it.permutations(others, k):
                if rng.random() < 0.3:
                    words.append((t, list(w)))
    for t, w in words:
        for a, b in it.product(range(Q), repeat=2):
            vec = wordvec(Ks, X, t, a, b, w, K)
            cl = C.word_closed(t, a, b, w)
            ok['X3'] &= coeff(vec, 0) == [fq(0)] * Q
            for k, want in cl.items():
                ok['X3'] &= coeff(vec, k) == want
    # X4: DHW differences
    for t in range(n):
        others = [u for u in range(n) if u != t]
        s0 = others[0]
        w0 = [s0] + [u for u in others if u != s0]
        for s in others[1:]:
            ws = [s] + [u for u in others if u != s]
            for a in range(Q):
                d2 = [x - y for x, y in zip(coeff(wordvec(Ks, X, t, a, a, ws, K), 2),
                                            coeff(wordvec(Ks, X, t, a, a, w0, K), 2))]
                want = [fq(0)] * Q
                for v in others:
                    if v < s:
                        com = [x - y for x, y in zip(C.nuN(s, a, v), C.nuN(v, a, s))]
                        alt = [fq(0)] * Q
                        for cc in range(Q):
                            if cc != a:
                                alt = [z + C.c[s][a][cc] * x - C.c[v][a][cc] * y
                                       for z, x, y in zip(alt, C.nu(v, cc), C.nu(s, cc))]
                        alt = [z + C.mu[v][a] * x - C.mu[s][a] * y for z, x, y in zip(alt, C.nu(s, a), C.nu(v, a))]
                        ok['X4'] &= com == alt
                        want = [z - x for z, x in zip(want, com)]
                ok['X4'] &= d2 == want
    return ok, (H, us, X)


def ladic_check(n, K=4, l=10007, seed=3):
    """X5: exact family_eval at eps = l versus the definition series truncated at K."""
    rng = random.Random(seed)
    H = [[0 if a == i else rng.randint(1, 30) for i in range(Q)] for a in range(Q)]
    us = [[rng.randint(1, 30) for _ in range(Q)] for _ in range(n)]
    X = [rng.randint(1, 30) for _ in range(Q)]
    R = Ring(None)
    A = [[[(fq(1 if a == i else 0) + fq(l) * H[a][i]) * us[t][i] for i in range(Q)] for a in range(Q)]
         for t in range(n)]
    vals = family_eval(A, n, [fq(x) for x in X], R, 'F')
    Ks = [kernel_def(H, us[t], X, K) for t in range(n)]
    ser = []
    for s in range(n):
        for a in range(Q):
            ser.append([Ser.const(X[a] if i == a else 0, K) - Ks[s][a][i] * fq(X[a]) for i in range(Q)])
    for t in range(n):
        for s in range(n):
            if s == t:
                continue
            w = [s] + [u for u in range(n) if u not in (s, t)]
            for a in range(Q):
                for b in range(Q):
                    ser.append(wordvec(Ks, X, t, a, b, w, K))
    worst = None
    for v, sv in zip(vals, ser):
        for i in range(Q):
            approx = sum((sv[i].c[k] * fq(l) ** k for k in range(K + 1)), fq(0))
            diff = v[i] - approx
            if diff == 0:
                continue
            num, den = int(diff.p), int(diff.q)
            vv = 0
            while num % l == 0:
                num //= l
                vv += 1
            while den % l == 0:
                den //= l
                vv -= 1
            worst = vv if worst is None else min(worst, vv)
    return worst


def main():
    for n in (2, 3, 4):
        for seed in (1, 2):
            ok, _ = check_point(seed + 10 * n, n, K=5)
            print(f'n={n} seed={seed}: ' + ', '.join(f'{k} {v}' for k, v in ok.items()), flush=True)
    for n in (3, 4):
        w = ladic_check(n, K=4)
        print(f'(X5) n={n}: min l-adic valuation of (family_eval at eps=l) - (series to order 4) = {w} '
              f'(> 4 required): {w is None or w > 4}', flush=True)


if __name__ == '__main__':
    main()
