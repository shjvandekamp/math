#!/usr/bin/env python3
"""agent_col (follow-up to task 3): are the latest-pair collision jets independent modulo an EXPLICIT space?

Latest pair u_N = u_{N-1}(1 + delta nu) (AG_NOTES sec. 5).  At delta = 0 block N = block K := N-1.
AG 5.3: S_0 = Phi0(W_{n-1}) + span{E_{K,a}} + span{h_{K,ab}(I - K Pi_{0..K-1})}, Phi0(w) = w K_K + L(Lambda(w)).
Every term of Phi0 lies in the explicit (Lambda-free) space
    Y_lp := W_{n-1} + W_{n-1} K_K + span{h_{K,ab}(I - K_K)} + span{h_{K,ab}(I - K_K Pi)}.
If the 18n-24 jets are independent modulo Y_lp, the jet step of the latest-pair collision is Lambda-free.
Prints dim S_0, dim Y_lp, rank(jets mod S_0), rank(jets mod Y_lp).  Jets (D = dK_N/d delta at 0):
   E:  -X_a e_a D;   (N,K)-pair: X_a D(a,b) e_b (I - K_K Pi) + X_a K_K(a,b) e_b D Pi;
   (t,N)/(t,K):  h_tab (K_K Pi_t D - D Pi_t K_K);   (N,s)/(K,s): X_a D(a,b) e_b (I - K_s Pi'_s K_K) + h_{K,ab} K_s Pi'_s D.
Exact mod p = 2^61-1, one random point per n.  What this does not show: proofs; anything beyond printed n.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, family_series, kernels_series, rand_points, rank,  # noqa
                           family_labels, term_vec, T_E, T_F, kernels_with_D, WordCache)
from agent_col_stepY import canon_W  # noqa: E402


def eval_D(A, vecs, pts, k, nu):
    rows = [[] for _ in vecs]
    for X in pts:
        kers = kernels_with_D(A, X, k, nu)
        wc = WordCache(kers, 1)
        for r, terms in enumerate(vecs):
            v = term_vec(kers, X, terms, 1, wc, 2)
            rows[r].extend([v[0][0], v[1][0]])
    return rows


def times_block(vec, k):
    out = []
    for coef, a0, heads, kind, word in vec:
        assert kind == 'IW'
        out.append((coef, a0, heads, 'W', [k]))
        out.append((-coef, a0, heads, 'W', list(word) + [k]))
    return out


def latest_jets(n):
    N = n - 1
    K = N - 1
    Dn = n
    Pi = list(range(K))                       # blocks 0..K-1
    out = []
    for a in range(Q):
        out.append([(P - 1, a, [], 'W', [Dn])])
    for a in range(Q):
        for b in range(Q):
            out.append([(1, a, [(Dn, b)], 'IW', [K] + Pi), (1, a, [(K, b)], 'W', [Dn] + Pi)])
    for t in range(K):
        Pit = [u for u in range(K) if u != t]
        for a in range(Q):
            for b in range(Q):
                out.append([(1, a, [(t, b)], 'W', [K] + Pit + [Dn]), (P - 1, a, [(t, b)], 'W', [Dn] + Pit + [K])])
    for s in range(K):
        Pis = [u for u in range(K) if u != s]
        for a in range(Q):
            for b in range(Q):
                out.append([(1, a, [(Dn, b)], 'IW', [s] + Pis + [K]), (1, a, [(K, b)], 'W', [s] + Pis + [Dn])])
    return out


def main(ns):
    for n in ns:
        N = n - 1
        K = N - 1
        rng = random.Random(6100 + n)
        A2, info = collision_config(n, K, rng, 2)
        nu = info['nu']
        A0 = [[[[x[0]] for x in row] for row in blk] for blk in A2]
        labs = family_labels(n)
        # distinct delta = 0 members: drop N-side of each coinciding pair
        drop = set([('E', N, a) for a in range(Q)] + [('F', N, K, a, b) for a in range(Q) for b in range(Q)])
        drop |= set(('F', t, N, a, b) for t in range(K) for a in range(Q) for b in range(Q))
        drop |= set(('F', N, s, a, b) for s in range(K) for a in range(Q) for b in range(Q))
        fam = []
        for lab in labs:
            if lab in drop:
                continue
            fam.append(T_E(lab[1], lab[2]) if lab[0] == 'E' else T_F(lab[1], lab[2], lab[3], lab[4], n))
        jets = latest_jets(n)
        # verify jets against series (spot check)
        X = rand_points(A0, 1, rng, 1)[0]
        ser = family_series(kernels_series(A2, X, 2), X, n, 2)
        pos = {l: i for i, l in enumerate(labs)}
        pairs = [(('E', N, a), ('E', K, a)) for a in range(Q)]
        pairs += [(('F', N, K, a, b), ('F', K, N, a, b)) for a in range(Q) for b in range(Q)]
        pairs += [(('F', t, N, a, b), ('F', t, K, a, b)) for t in range(K) for a in range(Q) for b in range(Q)]
        pairs += [(('F', N, s, a, b), ('F', K, s, a, b)) for s in range(K) for a in range(Q) for b in range(Q)]
        kers = kernels_with_D(A0, X, K, nu)
        ok = True
        for (l1, l0), jt in zip(pairs, jets):
            v = term_vec(kers, X, jt, 1, None, 2)
            for comp in range(2):
                ok &= v[comp][0] == (ser[pos[l1]][comp][1] - ser[pos[l0]][comp][1]) % P
        Wo = canon_W(N)                                        # W_{n-1}: blocks 0..N-1
        Ylp = Wo + [times_block(v, K) for v in Wo]
        Ylp += [[(1, a, [(K, b)], 'IW', [K])] for a in range(Q) for b in range(Q)]
        Ylp += [[(1, a, [(K, b)], 'IW', [K] + list(range(K)))] for a in range(Q) for b in range(Q)]
        pts = rand_points(A0, (len(Ylp) + len(jets) + len(fam)) // 2 + 12, rng, 1)
        EF, EJ, EY = eval_D(A0, fam, pts, K, nu), eval_D(A0, jets, pts, K, nu), eval_D(A0, Ylp, pts, K, nu)
        dS, dSJ = rank(EF), rank(EF + EJ)
        dY, dYJ, dYS = rank(EY), rank(EY + EJ), rank(EY + EF)
        print(f'n={n}: jets verified: {ok}; dim S_0={dS} (|fam|-(18n-24)={3 * n * (3 * n - 2) - 18 * n + 24}); '
              f'rank jets mod S_0 = {dSJ - dS} (18n-24={18 * n - 24}); dim Y_lp={dY}, S_0 in Y_lp: {dYS == dY}; '
              f'rank jets mod Y_lp = {dYJ - dY}', flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [4, 5, 6])
