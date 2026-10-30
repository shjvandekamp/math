#!/usr/bin/env python3
"""agent_col task 3(c): cyclic structure of the configuration (0, 1, ..., m-1, 0').

For the same m generic blocks, the cyclic configuration can be cut at any block k:
   C_k = (k, k+1, ..., m-1, 0, ..., k-1, k')   (block k doubled; n = m+1 time slots).
S^(k) := span of the distinct delta = 0 family members of C_k (a space of rational vector functions with
double poles along block k's lines).  Prints dim S^(k), dim(S^(0) cap S^(k)) for k = 1..m-1, and compares
with dim W_m and with dim(Y_0 cap Y_k), Y_k = W_m + W_m K_k (the explicit part found in agent_col_stepY).
Also tests whether S^(0) is invariant under reversal of the cycle (C'_0 = (0, m-1, ..., 1, 0')), and
(usage `agent_col_cyclic.py order m ...`) whether S^(0) is independent of the order of the middle blocks.
Exact mod p = 2^61-1 at one random product-form point (blocks shared by all cuts).
What this does not show: any symmetry beyond these intersections.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, make_A, s_const, eval_terms_matrix, rand_points, rank, T_E, T_F)  # noqa
from agent_col_stepY import canon_W  # noqa: E402


def cyc_family(order, n):
    """order: list of block ids (length n) with order[0] == order[-1] (the doubled block).
    Returns delta=0 distinct family members as term lists in terms of block ids (time positions mapped)."""
    N = n - 1
    vecs, seen = [], set()
    # positions 0..N; F_{t,s} with t, s positions; word = s then increasing positions other than s,t
    for a_ in range(Q):
        pass
    for pos_s in range(n):
        for a in range(Q):
            key = ('E', order[pos_s], a)
            if key not in seen:
                seen.add(key)
                vecs.append([(1, a, [], 'IW', [order[pos_s]])])
    for pt in range(n):
        for ps in range(n):
            if ps == pt:
                continue
            word = [order[ps]] + [order[u] for u in range(n) if u not in (ps, pt)]
            for a in range(Q):
                for b in range(Q):
                    key = ('F', order[pt], tuple(word), a, b)
                    if key in seen:
                        continue
                    seen.add(key)
                    vecs.append([(1, a, [(order[pt], b)], 'IW', word)])
    return vecs


def main(ms):
    for m in ms:
        n = m + 1
        rng = random.Random(9000 + m)
        g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
        A = make_A(g, [[s_const(x, 1) for x in u] for u in us])      # m distinct blocks, ids 0..m-1
        fams = {}
        for k in range(m):
            order = [(k + j) % m for j in range(m)] + [k]
            fams[k] = cyc_family(order, n)
        rev = [0] + [m - j for j in range(1, m)] + [0]
        famrev = cyc_family(rev, n)
        Wm = canon_W(m)
        npts = (2 * len(fams[0]) + len(Wm)) // 2 + 20
        pts = rand_points(A, npts, rng, 1)

        def ev(vs):
            return eval_terms_matrix(A, vs, pts, 1, ncomp=2)

        E0 = ev(fams[0])
        d0 = rank(E0)
        dW = rank(ev(Wm))
        print(f'm={m}: dim S^(0)={d0} (#members {len(fams[0])}), dim W_m={dW}, W_m in S^(0): '
              f'{rank(E0 + ev(Wm)) == d0}', flush=True)
        for k in range(1, m):
            Ek = ev(fams[k])
            dk = rank(Ek)
            inter = d0 + dk - rank(E0 + Ek)
            print(f'   cut k={k}: dim S^(k)={dk}, dim(S^(0) cap S^(k))={inter}', flush=True)
        Er = ev(famrev)
        dr = rank(Er)
        print(f'   reversed cycle: dim={dr}, dim(S^(0) cap S^rev)={d0 + dr - rank(E0 + Er)}, equal spans: '
              f'{rank(E0 + Er) == d0 == dr}', flush=True)




def order_independence(m, trials=4):
    """Is S^(0) independent of the order of the middle blocks?  (0, sigma(1..m-1), 0') for random sigma."""
    import itertools
    n = m + 1
    rng = random.Random(9500 + m)
    g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
    us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
    A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
    base = cyc_family([0] + list(range(1, m)) + [0], n)
    pts = rand_points(A, len(base) + 20, rng, 1)
    E0 = eval_terms_matrix(A, base, pts, 1, ncomp=2)
    d0 = rank(E0)
    perms = list(itertools.permutations(range(1, m)))
    rng.shuffle(perms)
    for sig in perms[:trials]:
        fam = cyc_family([0] + list(sig) + [0], n)
        Es = eval_terms_matrix(A, fam, pts, 1, ncomp=2)
        ds = rank(Es)
        print(f'm={m} middle order {sig}: dim={ds}, same span as (1..m-1): {rank(E0 + Es) == d0 == ds}', flush=True)
    # a non-cyclic control: the n-system with u_N = u_0 but the doubled block in the MIDDLE (0,..,j,..,0) is
    # the same thing; control = cut at a different block (already shown: intersection = W_m).


if __name__ == '__main__':
    # usage: agent_col_cyclic.py [m ...]          (cut points and reversed cycle)
    #        agent_col_cyclic.py order [m ...]    (independence of the middle order)
    if len(sys.argv) > 1 and sys.argv[1] == 'order':
        for mm in [int(x) for x in sys.argv[2:]] or [4, 5]:
            order_independence(mm, trials=2 if mm >= 6 else 4)
    else:
        main([int(x) for x in sys.argv[1:]] or [4, 5])
