#!/usr/bin/env python3
"""agent_col2 task (3): how does the head map change under one adjacent transposition of middle blocks?

Two time orders tau, tau' differing by swapping two adjacent middle blocks u, v.  Families:
  (m-system)  DHW family of the m blocks in order tau (= (0, sigma)), a basis of W_m (P(m));
  (cyclic)    distinct delta = 0 members of (0, sigma, 0'), a basis of S_0 = S_loc (Q_cyc(m)).
Head map Lambda^tau(w)_{slot,a,b} = sum of the tau-family coefficients of w over the columns with head slot `slot`
and states (a,b), minus the E-spread (E_{s,a} contributes -1 to (s,a,b) for every b).  For the cyclic family the
head slots are 0, the middle blocks, and 0'; the merged column F_{0,N} = F_{N,0} is put in slot 0.
Delta := Lambda^tau - Lambda^tau'.  PROVED (word inspection): the columns with t or s in {u,v} and the E's are common
to both families, so Delta vanishes on them; for the other columns F^tau - F^tau' = +- h_t W1 [K_u, K_v] W2.
Prints rank Delta, the number of nonzero entries, which head rows are hit, and the rank of Delta restricted to
column groups.  Also dim(Head cap (Bod^tau + Bod^tau')) (an upper bound for rank Delta, m-system).
Exact mod p = 2^61-1, one random product-form point.  Kill criterion: dense, full rank, no visible structure.
What this does not show: proofs; other transpositions than those printed.
"""
import random
import sys
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, make_A, s_const, eval_terms_matrix, rand_points, rank)  # noqa: E402


def dhw_family(order):
    """order: list of block ids in time order (distinct).  Returns labels and term lists."""
    labs, vecs = [], []
    for s in order:
        for a in range(Q):
            labs.append(('E', s, a))
            vecs.append([(1, a, [], 'IW', [s])])
    for t in order:
        for s in order:
            if s == t:
                continue
            word = [s] + [u for u in order if u not in (s, t)]
            for a in range(Q):
                for b in range(Q):
                    labs.append(('F', t, s, a, b, tuple(word)))
                    vecs.append([(1, a, [(t, b)], 'IW', word)])
    return labs, vecs


def cyclic_family(order):
    """order = slots (0, middle..., 0') given as block ids with the last equal to the first.
    Slots are labelled by position; returns labels with head slot positions and term lists (duplicates removed)."""
    n = len(order)

    def name(pos):                      # slot label: block id, with the two copies of block 0 distinguished
        if pos == 0:
            return 'f0'
        if pos == n - 1:
            return 'l0'
        return order[pos]
    labs, vecs, seen = [], [], set()
    for pos in range(n - 1):            # E for each distinct block
        s = order[pos]
        for a in range(Q):
            labs.append(('E', name(pos), a))
            vecs.append([(1, a, [], 'IW', [s])])
    for pt in range(n):
        for ps in range(n):
            if ps == pt:
                continue
            word = [order[ps]] + [order[u] for u in range(n) if u not in (ps, pt)]
            for a in range(Q):
                for b in range(Q):
                    key = (order[pt], tuple(word), a, b)
                    if key in seen:
                        continue
                    seen.add(key)
                    labs.append(('F', name(pt), name(ps), a, b, tuple(word)))
                    vecs.append([(1, a, [(order[pt], b)], 'IW', word)])
    return labs, vecs


def coords_in(A, basis_vecs, target_vecs, rng, ncomp=2):
    """Coordinates of target vectors in the given basis (exact; checked at extra columns)."""
    pts = rand_points(A, len(basis_vecs) // 2 + 8, rng, 1)
    EB = eval_terms_matrix(A, basis_vecs, pts, 1, ncomp=ncomp)
    ET = eval_terms_matrix(A, target_vecs, pts, 1, ncomp=ncomp)
    M = flint.nmod_mat(EB, P)
    Rr, rk = M.rref()
    assert rk == len(basis_vecs), f'basis rank {rk} < {len(basis_vecs)}'
    piv, r = [], 0
    for c in range(M.ncols()):
        if r < rk and int(Rr[r, c]) != 0:
            piv.append(c)
            r += 1
    Sq = flint.nmod_mat([[EB[i][c] for i in range(len(basis_vecs))] for c in piv], P)
    Sqinv = Sq.inv()
    Y = flint.nmod_mat([[ET[j][c] for j in range(len(target_vecs))] for c in piv], P)
    C = Sqinv * Y                     # columns = targets
    # check at all columns
    full = flint.nmod_mat([[EB[i][c] for i in range(len(basis_vecs))] for c in range(M.ncols())], P) * C
    Tfull = flint.nmod_mat([[ET[j][c] for j in range(len(target_vecs))] for c in range(M.ncols())], P)
    assert full == Tfull, 'target not in the span of the basis'
    return C


def head_rows(labs, slot_of):
    heads = sorted(set(slot_of(l) for l in labs if l[0] == 'F'), key=str)
    keys = [(h, a, b) for h in heads for a in range(Q) for b in range(Q)]
    return keys


def lambda_matrix(labs, C, slot_of, keys):
    """Lambda(target_j)_{key} from coordinate matrix C (rows = basis labels, columns = targets)."""
    kpos = {k: i for i, k in enumerate(keys)}
    rows = [[0] * C.ncols() for _ in keys]
    for i, lab in enumerate(labs):
        if lab[0] == 'F':
            k = (slot_of(lab), lab[3], lab[4])
            r = rows[kpos[k]]
            for j in range(C.ncols()):
                x = int(C[i, j])
                if x:
                    r[j] = (r[j] + x) % P
        else:
            _, s, a = lab
            for b in range(Q):
                k = (s, a, b)
                if k in kpos:
                    r = rows[kpos[k]]
                    for j in range(C.ncols()):
                        x = int(C[i, j])
                        if x:
                            r[j] = (r[j] - x) % P
    return rows


def analyse(kind, A, order1, order2, rng, label):
    if kind == 'msys':
        l1, v1 = dhw_family(order1)
        l2, v2 = dhw_family(order2)

        def slot1(l):
            return l[1]
        slot2 = slot1
    else:
        l1, v1 = cyclic_family(order1)
        l2, v2 = cyclic_family(order2)

        def slot1(l):
            return l[1]
        slot2 = slot1
    C = coords_in(A, v2, v1, rng)                 # tau-family in the tau'-basis
    keys = head_rows(l1, slot1)
    L2 = lambda_matrix(l2, C, slot2, keys)        # Lambda^tau'(F^tau_j)
    # Lambda^tau(F^tau_j) = unit vector / -spread
    Id = flint.nmod_mat([[1 if i == j else 0 for j in range(len(v1))] for i in range(len(v1))], P)
    L1 = lambda_matrix(l1, Id, slot1, keys)
    D = [[(a - b) % P for a, b in zip(r1, r2)] for r1, r2 in zip(L1, L2)]
    common = [j for j, l in enumerate(l1) if l[0] == 'E' or l[5] in set(x[5] for x in l2 if x[0] == 'F' and
                                                                           x[1] == l[1] and x[2] == l[2])]
    nzcols = [j for j in range(len(v1)) if any(D[i][j] for i in range(len(keys)))]
    nz = sum(1 for r in D for x in r if x)
    rowhit = sorted(set(keys[i][0] for i in range(len(keys)) if any(D[i])), key=str)
    diffcols = [j for j in range(len(v1)) if j not in set(common)]
    print(f'{label}: |family| = {len(v1)}, columns differing between the orders: {len(diffcols)}; '
          f'rank Delta = {rank(D)} (of max {len(keys)}); nonzero columns of Delta: {len(nzcols)} '
          f'(all inside the differing ones: {set(nzcols) <= set(diffcols)}); density on differing columns: '
          f'{nz}/{len(keys) * max(1, len(diffcols))}; head slots hit: {rowhit}', flush=True)
    return D, keys, l1


def head_body_bound(A, order1, order2, rng):
    """m-system: dim(Head cap (Bod^tau + Bod^tau')) with Head = span h_tab, Bod = bodies + X_a e_a."""
    m = len(order1)
    heads = [[(1, a, [(t, b)], 'I', [])] for t in order1 for a in range(Q) for b in range(Q)]
    Xe = [[(1, a, [], 'I', [])] for a in range(Q)]

    def bodies(order):
        out = []
        for t in order:
            for s in order:
                if s != t:
                    word = [s] + [u for u in order if u not in (s, t)]
                    out += [[(1, a, [(t, b)], 'W', word)] for a in range(Q) for b in range(Q)]
        return out
    B1, B2 = bodies(order1), bodies(order2)
    vecs = heads + Xe + B1 + B2
    pts = rand_points(A, len(vecs) // 2 + 10, rng, 1)
    E = lambda vs: eval_terms_matrix(A, vs, pts, 1, ncomp=3)  # noqa: E731
    dH = rank(E(heads))
    dB = rank(E(Xe + B1 + B2))
    dHB = rank(E(heads + Xe + B1 + B2))
    return dH, dB, dH + dB - dHB


def main():
    for m in (4, 5):
        rng = random.Random(17000 + m)
        g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
        A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
        base = list(range(m))
        for k in range(1, m - 1):          # swap middle blocks at positions k, k+1
            o2 = base[:]
            o2[k], o2[k + 1] = o2[k + 1], o2[k]
            analyse('msys', A, base, o2, rng, f'm={m} m-system swap ({base[k]},{base[k + 1]})')
            analyse('cyc', A, base + [0], o2 + [0], rng, f'm={m} cyclic   swap ({base[k]},{base[k + 1]})')
        o2 = base[:]
        o2[1], o2[2] = o2[2], o2[1]
        dH, dB, inter = head_body_bound(A, base, o2, rng)
        print(f'm={m}: m-system head/body: dim Head = {dH}, dim(Bod^tau + Bod^tau\') = {dB}, '
              f'dim(Head cap (Bod^tau + Bod^tau\')) = {inter}', flush=True)


if __name__ == '__main__':
    main()
