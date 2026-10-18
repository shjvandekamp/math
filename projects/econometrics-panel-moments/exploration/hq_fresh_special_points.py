#!/usr/bin/env python3
"""Exact rank of the raw equation-(24) source matrix at special parameter points.

Standard library only.  The source rows are K = M diag(A_y) exactly as in
general_source24.py (zero-based times, Q = 3, footnote-8 restriction), but the
transition table pi[t][q][r] is now an arbitrary rational table.  Rank is
computed modulo a large prime; a full modular rank proves full real rank at
that rational point, hence generic independence (rank cannot drop on a dense
open set once one minor is nonzero).  A modular rank deficiency proves nothing
by itself and is only reported.

What this checks: whether the family stays independent at degenerate points
 (a) no state dependence   pi_t(q,r) = u_t(q)
 (b) time-homogeneous      pi_t(q,r) = pi(q,r)
 (c) product form          pi_t(q,r) = u_t(q) * g(q,r)
 (d) random generic point.
What it does not show: anything about T beyond the periods run here.
"""
import itertools as it
import random
import sys
from fractions import Fraction

Q = 3
P = 1000003


def dimension(T):
    from math import comb
    return Q**T - comb(3 * T, 2) + 6 * (T - 1)


def source_indices(T):
    if T < 3:
        return []
    ans = []
    for j in range(T - 2):
        fixed = max(0, j - (Q - 2))
        for shared in it.combinations(range(T - 1), j):
            if shared[:fixed] != tuple(range(fixed)):
                continue
            remaining = sorted(set(range(T - 1)) - set(shared))
            s1 = remaining[0]
            for s2 in remaining[1:]:
                tail = sorted(set(remaining) - {s1, s2})
                tau1 = list(shared) + [s1] + tail + [s2, T - 1]
                tau2 = list(shared) + [s2] + tail + [s1, T - 1]
                for values in it.product(range(Q), repeat=j + 1):
                    ans.append(dict(j=j, shared=shared, s1=s1, s2=s2,
                                    values=values, tau1=tau1, tau2=tau2))
    return ans


def transformed_weight(y, tau, initial, pi):
    """prod over periods t of pi[t][generated outcome][true previous outcome]."""
    T = len(y)
    sigma = dict(zip([T - 1] + tau[:-1], tau))
    w = pi[0][y[sigma[T - 1]]][initial]
    for t in range(1, T):
        w *= pi[t][y[sigma[t - 1]]][y[t - 1]]
    return w


def source_row(paths, idx, pi, initial=0):
    row = []
    q = idx['values'][0]
    for y in paths:
        if any(y[t] != v for t, v in zip(idx['shared'], idx['values'][1:])):
            row.append(0)
            continue
        first = transformed_weight(y, idx['tau1'], initial, pi) if y[idx['s1']] == q else 0
        second = transformed_weight(y, idx['tau2'], initial, pi) if y[idx['s2']] == q else 0
        row.append(first - second)
    return row


def modp(x):
    x = Fraction(x)
    return x.numerator % P * pow(x.denominator % P, -1, P) % P


def rank_mod_p(rows):
    rows = [[modp(x) for x in r] for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], -1, P)
        rows[r] = [x * inv % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % P for x, y in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
        if r == len(rows):
            break
    return r


def family_rank(T, pi):
    idx = source_indices(T)
    paths = list(it.product(range(Q), repeat=T))
    rows = [source_row(paths, i, pi) for i in idx]
    return len(idx), rank_mod_p(rows)


def rnd():
    return Fraction(random.randint(1, 40), random.randint(1, 40))


def main():
    random.seed(12345)
    Ts = [int(a) for a in sys.argv[1:]] or [4, 5]
    for T in Ts:
        print(f"T={T}: family size {dimension(T)}")
        # (a) no state dependence
        u = [[rnd() for q in range(Q)] for t in range(T)]
        pi = [[[u[t][q] for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (a) no state dependence       :", family_rank(T, pi))
        # (b) time homogeneous
        g = [[rnd() for r in range(Q)] for q in range(Q)]
        pi = [[[g[q][r] for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (b) time homogeneous          :", family_rank(T, pi))
        # (c) product form u_t(q) g(q,r)
        pi = [[[u[t][q] * g[q][r] for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (c) product form u_t(q)g(q,r) :", family_rank(T, pi))
        # (c') economic-like: pi_t(q,r) = g(q,r) * w_q^t
        w = [Fraction(1), Fraction(2), Fraction(5)]
        pi = [[[g[q][r] * w[q] ** (t + 1) for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (c') g(q,r) w_q^(t+1)         :", family_rank(T, pi))
        # (d) random generic
        pi = [[[rnd() for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (d) random generic            :", family_rank(T, pi))
        # (e) binary-valued tropical-like: pi_t(q,r) = eps^{w} with eps=1/64 and random small weights
        eps = Fraction(1, 64)
        pi = [[[eps ** random.randint(0, 6) for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (e) powers of 1/64, random exp:", family_rank(T, pi))
        # (f) no state dependence AND time-homogeneous except period-specific scalar? pi_t(q,r)=u(q)^t
        pi = [[[u[0][q] ** (t + 1) for r in range(Q)] for q in range(Q)] for t in range(T)]
        print("  (f) u(q)^(t+1), no state dep. :", family_rank(T, pi))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
