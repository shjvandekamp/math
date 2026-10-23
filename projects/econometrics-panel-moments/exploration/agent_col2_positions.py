#!/usr/bin/env python3
"""agent_col2 task (2): exploit the freedom of where a new middle block b sits (induction m-1 -> m).

Blocks 0, 1, ..., m-2 (old) and b := m-1 (new); block 0 doubled.  Time-slot orders:
   pos j (j = 0..m-2): (0, 1..j, b, j+1..m-2, 0')          [cyclic; j = m-2 is the standard order]
   'last':  (0, 1, ..., m-2, 0', b)        'first': (b, 0, 1, ..., m-2, 0')   [non-cyclic, not covered by Conj. I]
Family = distinct delta = 0 members.  Split: New = {E_b} u {columns with head b or first letter b}; Old_j = the rest
(old columns with b inserted into their words at position j).  PROVED (word inspection): New is the same for every
position (b is removed from the word when it is the head or the first letter, and the other letters keep their
time order).  Checks (exact mod p = 2^61-1, one random point):
 (A) span(family) = S_loc(m) (= span of the standard order) for every position;
 (B) dims of O_j = span Old_j, of O_j cap O_j', of sum_j O_j, and whether New lies in sum_j O_j;
 (C) commutator differences Ins_j(F) - Ins_{j+1}(F): rank, and rank modulo O_j;
 (D) explicit hull for 'last': Y_last = S_old K_b + span{h_t (I - K_b)} + span{E_b} contains O_last? dim Y_last - dim O_last,
     and rank of New modulo Y_last (a Lambda-free step would need Y_last = O_last);
 (E) commutator form of the step at the first middle position: coordinates of the commutator differences in the
     basis Old u New; density/rank of the New-block and of the head sums of the Old-block.
What this does not show: proofs; anything beyond the printed m.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, make_A, s_const, eval_terms_matrix, rand_points, rank)  # noqa: E402


def family_split(order, b):
    """Distinct delta = 0 members for a slot order (block ids, block 0 twice); split into Old/New by b."""
    n = len(order)
    old, new, seen = [], [], set()
    for blk in sorted(set(order)):
        for a in range(Q):
            v = [(1, a, [], 'IW', [blk])]
            (new if blk == b else old).append((('E', blk, a), v))
    for pt in range(n):
        for ps in range(n):
            if ps == pt:
                continue
            word = [order[ps]] + [order[u] for u in range(n) if u not in (ps, pt)]
            for a in range(Q):
                for b2 in range(Q):
                    key = (order[pt], tuple(word), a, b2)
                    if key in seen:
                        continue
                    seen.add(key)
                    v = [(1, a, [(order[pt], b2)], 'IW', word)]
                    is_new = (order[pt] == b) or (order[ps] == b)
                    # label for matching old columns across positions: (head slot, first slot) by block with copies
                    lab = ('F', slotname(order, pt), slotname(order, ps), a, b2)
                    (new if is_new else old).append((lab, v))
    return old, new


def slotname(order, pos):
    blk = order[pos]
    if blk != 0:
        return blk
    first0 = order.index(0)
    return 'f0' if pos == first0 else 'l0'


def main(ms):
    for m in ms:
        rng = random.Random(23000 + m)
        g = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(Q)]
        us = [[rng.randrange(1, P) for _ in range(Q)] for _ in range(m)]
        A = make_A(g, [[s_const(x, 1) for x in u] for u in us])
        b = m - 1
        mid = list(range(1, m - 1))
        orders = {f'pos{j}': [0] + mid[:j] + [b] + mid[j:] + [0] for j in range(m - 1)}
        orders['last'] = [0] + mid + [0, b]
        orders['first'] = [b, 0] + mid + [0]
        splits = {k: family_split(o, b) for k, o in orders.items()}
        # New position-independent?
        newsets = {k: sorted(str(v) for _, v in sp[1]) for k, sp in splits.items()}
        same_new = all(newsets[k] == newsets['pos0'] for k in newsets)
        nfam = 3 * (m + 1) * (3 * (m + 1) - 2) - 12
        allvecs = [v for sp in splits.values() for _, v in sp[0] + sp[1]]
        pts = rand_points(A, len(splits['pos0'][0]) * 3 // 2 + len(splits['pos0'][1]) + 40, rng, 1)

        def ev(vs):
            return eval_terms_matrix(A, vs, pts, 1, ncomp=2)

        std = f'pos{m - 2}'
        Estd = ev([v for _, v in splits[std][0] + splits[std][1]])
        dstd = rank(Estd)
        print(f'm={m}: |fam|-12 = {nfam}; New is identical for all positions: {same_new}; |New| = '
              f'{len(splits[std][1])} (18m+3 = {18 * m + 3}); |Old| = {len(splits[std][0])}', flush=True)
        EO, EN = {}, ev([v for _, v in splits[std][1]])
        for k, (old, new) in splits.items():
            Ef = ev([v for _, v in old + new])
            d = rank(Ef)
            same = rank(Estd + Ef) == dstd == d
            EO[k] = ev([v for _, v in old])
            dO = rank(EO[k])
            dON = rank(EO[k] + EN)
            print(f'   (A) {k:6s} order {orders[k]}: rank family = {d}, same span as standard: {same}; '
                  f'dim O = {dO} (|Old| {len(old)}), rank New mod O = {dON - dO}', flush=True)
        keys = [k for k in orders if k.startswith('pos')]
        sumO = rank([r for k in keys for r in EO[k]])
        print(f'   (B) dim sum_j O_j (cyclic positions) = {sumO}; New in sum_j O_j: '
              f'{rank([r for k in keys for r in EO[k]] + EN) == sumO}', flush=True)
        for i in range(len(keys) - 1):
            k1, k2 = keys[i], keys[i + 1]
            d1, d2 = rank(EO[k1]), rank(EO[k2])
            print(f'   (B) dim(O_{k1} cap O_{k2}) = {d1 + d2 - rank(EO[k1] + EO[k2])}', flush=True)
            # (C) commutator differences: match old columns by label
            lab1 = {l: v for l, v in splits[k1][0]}
            lab2 = {l: v for l, v in splits[k2][0]}
            diffs = []
            for l, v in lab1.items():
                if l in lab2 and str(v) != str(lab2[l]):
                    diffs.append([(c, a, h, kd, w) for (c, a, h, kd, w) in v] +
                                 [(P - c, a, h, kd, w) for (c, a, h, kd, w) in lab2[l]])
            if diffs:
                ED = ev(diffs)
                rD = rank(ED)
                print(f'   (C) {k1}->{k2}: {len(diffs)} commutator differences, rank {rD}, rank mod O_{k1} = '
                      f'{rank(EO[k1] + ED) - rank(EO[k1])}', flush=True)
        # (E) commutator form of the step: coordinates of the differences Ins_j(F) - Ins_{j+1}(F) in the basis
        #     Old_j u New; density of the New-block and of the head sums (old cyclic head map) of the Old-block
        import flint
        k1, k2 = keys[0], keys[1]
        lab1 = {l: v for l, v in splits[k1][0]}
        lab2 = {l: v for l, v in splits[k2][0]}
        diffs, dlabs = [], []
        for l, v in lab1.items():
            if l in lab2 and str(v) != str(lab2[l]):
                diffs.append([(c, a, h, kd, w) for (c, a, h, kd, w) in v] +
                             [(P - c, a, h, kd, w) for (c, a, h, kd, w) in lab2[l]])
                dlabs.append(l)
        basis = [v for _, v in splits[k1][0]] + [v for _, v in splits[k1][1]]
        blabs = [l for l, _ in splits[k1][0]] + [l for l, _ in splits[k1][1]]
        EB, ED = ev(basis), ev(diffs)
        MB = flint.nmod_mat(EB, P)
        Rr, rk = MB.rref()
        piv, r = [], 0
        for c in range(MB.ncols()):
            if r < rk and int(Rr[r, c]) != 0:
                piv.append(c)
                r += 1
        Sq = flint.nmod_mat([[EB[i][c] for i in range(len(basis))] for c in piv], P).inv()
        Cm = Sq * flint.nmod_mat([[ED[j][c] for j in range(len(diffs))] for c in piv], P)
        nold = len(splits[k1][0])
        newblock = [[int(Cm[i, j]) for j in range(len(diffs))] for i in range(nold, len(basis))]
        nzN = sum(1 for row in newblock for x in row if x)
        # head sums of the Old-block coefficients (old columns are labelled by (head slot, first slot, a, b))
        hs = {}
        for i in range(nold):
            l = blabs[i]
            if l[0] != 'F':
                continue
            key = (l[1], l[3], l[4])
            row = hs.setdefault(key, [0] * len(diffs))
            for j in range(len(diffs)):
                x = int(Cm[i, j])
                if x:
                    row[j] = (row[j] + x) % P
        HS = list(hs.values())
        nzH = sum(1 for row in HS for x in row if x)
        print(f'   (E) {k1}: {len(diffs)} commutator differences in the basis Old u New: New-block density '
              f'{nzN}/{len(newblock) * len(diffs)}, rank {rank(newblock)}; head sums of the Old-block: density '
              f'{nzH}/{len(HS) * len(diffs)}, rank {rank(HS)}', flush=True)
        # (D) explicit hull for 'last'
        olds = [0] + mid + [0]
        oldfam = family_split(olds, b)[0]           # b absent: everything is 'old'
        Sold = [v for _, v in oldfam]

        def times_b(vec):
            out = []
            for c, a, h, kd, w in vec:
                out.append((c, a, h, 'W', [b]))
                out.append((P - c, a, h, 'W', list(w) + [b]))
            return out
        Ylast = [times_b(v) for v in Sold]
        Ylast += [[(1, a, [(t, b2)], 'IW', [b])] for t in range(m - 1) for a in range(Q) for b2 in range(Q)]
        Ylast += [[(1, a, [], 'IW', [b])] for a in range(Q)]          # E_b (Phi_b(E_s) = E_s - E_b)
        EY = ev(Ylast)
        dY, dOl = rank(EY), rank(EO['last'])
        incl = rank(EY + EO['last']) == dY
        print(f'   (D) Y_last = S_old K_b + span h_t(I-K_b) + E_b: dim {dY}; O_last inside Y_last: {incl}; '
              f'dim Y_last - dim O_last = {dY - dOl} (9(m-1) = {9 * (m - 1)}); Y_last inside S_loc(m): '
              f'{rank(Estd + EY) == dstd}; rank New mod Y_last = {rank(EY + EN) - dY}', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [4, 5])
