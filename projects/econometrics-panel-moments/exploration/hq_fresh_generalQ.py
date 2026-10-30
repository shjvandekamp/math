#!/usr/bin/env python3
"""Raw equation-(24) family for general Q: count and modular rank at economic points.

Source tuples follow DHW (24)-(25): j shared positions t_1<...<t_j in {0..T-2}
(zero-based), restriction t_r = r for r < max(0, j-(Q-2)), s1 = min of the rest,
s2 any other, values q in [Q]^{j+1}; generation orders
tau1 = (t, s1, rest increasing, s2, T-1), tau2 = (t, s2, rest, s1, T-1).
Rows = moments (likelihood-weighted transformed-chain differences), columns =
paths.  Table pi_t(q,r) = g(q,r) u_t(q) with u_t(q) = w_q^{x_t} (economic point).
Full modular rank proves independence at that point (hence generic independence).
Prints the count, ell(Q,T) from formula (25), and the rank.
"""
import itertools as it
import random
import sys
from math import comb

import flint

P = (1 << 61) - 1


def ell(Q, T):
    tot = 0
    for j in range(T - 2):
        fixed = max(j - (Q - 2), 0)
        tot += comb(T - 1 - fixed, min(Q - 2, j)) * (T - 2 - j) * Q ** (j + 1)
    return tot


def source_indices(Q, T):
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
                    ans.append((shared, s1, s2, values, tau1, tau2))
    return ans


def weight(y, tau, init, pi):
    T = len(y)
    sigma = dict(zip([T - 1] + tau[:-1], tau))
    w = pi[0][y[sigma[T - 1]]][init]
    for t in range(1, T):
        w = w * pi[t][y[sigma[t - 1]]][y[t - 1]]
    return w


def family_rank(Q, T, pi, init=0):
    idx = source_indices(Q, T)
    paths = list(it.product(range(Q), repeat=T))
    rows = []
    for shared, s1, s2, values, tau1, tau2 in idx:
        q = values[0]
        row = []
        for y in paths:
            if any(y[t] != v for t, v in zip(shared, values[1:])):
                row.append(0)
                continue
            a = weight(y, tau1, init, pi) if y[s1] == q else 0
            b = weight(y, tau2, init, pi) if y[s2] == q else 0
            row.append(int(a - b))
        rows.append(row)
    M = flint.nmod_mat(rows, P)
    return len(idx), M.rank()


def main():
    args = [tuple(map(int, a.split(','))) for a in sys.argv[1:]] or [(3, 4), (4, 4), (5, 4), (3, 5), (4, 5)]
    rng = random.Random(3)
    for Q, T in args:
        g = [[flint.nmod(rng.randint(2, 10 ** 6), P) for _ in range(Q)] for _ in range(Q)]
        w = [flint.nmod(rng.randint(2, 10 ** 6), P) for _ in range(Q)]
        xs = [rng.randint(1, 50) for _ in range(T)]
        pi = [[[g[q][r] * w[q] ** xs[t] for r in range(Q)] for q in range(Q)] for t in range(T)]
        cnt, rk = family_rank(Q, T, pi)
        print(f'Q={Q} T={T}: family size {cnt} (formula (25): {ell(Q, T)}), rank {rk}'
              f'{"  FULL (independent)" if rk == cnt else ""}', flush=True)


if __name__ == '__main__':
    main()
