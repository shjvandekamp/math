#!/usr/bin/env python3
"""agent_col task 2/3: structure of the delta = 0 span S_0 at the collision u_N = u_0 (blocks 0..N, N = n-1).

At delta = 0 block N equals block 0 (the configuration is (0, 1, ..., m-1, 0'), m = n-1 distinct blocks).
Exact mod p = 2^61-1, random product-form points, evaluation at random X.

(A) Kernel of the delta = 0 family: its dimension and whether it is spanned by the 12 pair differences
    E_{N,a} - E_{0,a}, F_{N,0,a,b} - F_{0,N,a,b}; for n = 4 the extra relations are located (labels).
(B) Head/body form: S_0 has dim |fam| - 12  <=>  Q_cyc(m): the 9m^2 + 18m - 6 functions
    {h_tab : t < m} u {X_a e_a} u {bodies h_tab W_{t,s} at delta = 0, the (0,N)/(N,0) duplicate removed}
    are independent (the same bookkeeping as AG 1.3).  Prints the rank.
(C) Append/prepend (Mayer-Vietoris) decomposition: A = span(E, F_{t,s} : t,s in {0..m-1}) = E + Phi_0(W_m)
    (old columns of the append view), B = span(E, F_{t,s} : t,s in {1..m-1, N}) (old columns of the
    prepend view of the rotated system (1..m-1, 0)), C = span(E, F_{t,s} : t,s in {1..m-1}) (common).
    Prints dims of A, B, C, A+B, A+B+F_{0,N}, and dim(A cap B) = dim A + dim B - dim(A+B).
What this does not show: anything beyond the printed n; a proof of any of the dimension statements.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_col_lib import (P, Q, collision_config, family_terms, eval_terms_matrix, rand_points, rank,  # noqa
                           left_kernel, T_head, T_body, T_Xe, T_F, T_E, dhw_word, span_dim)


def part_A(n, seed):
    rng = random.Random(seed)
    A, info = collision_config(n, 0, rng, 1)
    N = n - 1
    labs, vecs = family_terms(n)
    pts = rand_points(A, len(vecs) // 2 + 8, rng, 1)
    M = eval_terms_matrix(A, vecs, pts, 1, ncomp=2)
    ker = left_kernel(M)
    pos = {l: i for i, l in enumerate(labs)}
    pairs = []
    for a in range(Q):
        v = [0] * len(labs)
        v[pos[('E', N, a)]] = 1
        v[pos[('E', 0, a)]] = P - 1
        pairs.append(v)
    for a in range(Q):
        for b in range(Q):
            v = [0] * len(labs)
            v[pos[('F', N, 0, a, b)]] = 1
            v[pos[('F', 0, N, a, b)]] = P - 1
            pairs.append(v)
    rk_ker = rank(ker) if ker else 0
    rk_both = rank(ker + pairs)
    print(f'(A) n={n}: dim ker(delta=0 family) = {len(ker)}; pair differences inside kernel: '
          f'{rk_both == rk_ker}; rank of pair differences = {rank(pairs)}', flush=True)
    if len(ker) > 12:
        # extra kernel vectors modulo pair differences: zero the N-columns via pair differences
        import flint
        # reduce: project kernel onto coordinates not in the pair labels' N-side
        killcols = [pos[('E', N, a)] for a in range(Q)] + [pos[('F', N, 0, a, b)] for a in range(Q) for b in range(Q)]
        red = []
        for v in ker:
            w = v[:]
            for c in killcols:
                if w[c]:
                    lab = labs[c]
                    if lab[0] == 'E':
                        partner = pos[('E', 0, lab[2])]
                    else:
                        partner = pos[('F', 0, N, lab[3], lab[4])]
                    w[partner] = (w[partner] + w[c]) % P
                    w[c] = 0
            red.append(w)
        Mred = flint.nmod_mat(red, P)
        Rr, rk = Mred.rref()
        print(f'    extra relations modulo the pairs: {rk}')
        for i in range(rk):
            sup = [labs[j] for j in range(len(labs)) if int(Rr[i, j]) != 0]
            print('     support:', sup)


def qcyc_vectors(n):
    """Heads (t < N), X_a e_a, bodies at delta = 0 with the (N,0) duplicate of (0,N) removed."""
    N = n - 1
    vecs, labs = [], []
    for t in range(N):
        for a in range(Q):
            for b in range(Q):
                vecs.append(T_head(t, a, b))
                labs.append(('h', t, a, b))
    for a in range(Q):
        vecs.append(T_Xe(a))
        labs.append(('X', a))
    for t in range(n):
        for s in range(n):
            if s == t or (t == N and s == 0):
                continue
            for a in range(Q):
                for b in range(Q):
                    vecs.append(T_body(t, a, b, dhw_word(t, s, n)))
                    labs.append(('body', t, s, a, b))
    return labs, vecs


def part_B(n, seed):
    rng = random.Random(seed)
    m = n - 1
    A0, _ = collision_config(n, 0, rng, 1)
    labs, vecs = qcyc_vectors(n)
    d = span_dim(A0, vecs, rng, 1, 3, extra=10)
    print(f'(B) n={n}, m={m}: Q_cyc(m): rank {d} of {len(vecs)} functions (9m^2+18m-6 = {9 * m * m + 18 * m - 6})',
          flush=True)


def part_C(n, seed):
    rng = random.Random(seed)
    N = n - 1
    m = n - 1
    A0, _ = collision_config(n, 0, rng, 1)
    Es = [T_E(s, a) for s in range(m) for a in range(Q)]

    def Fs(blockset):
        return [T_F(t, s, a, b, n) for t in blockset for s in blockset if s != t for a in range(Q) for b in range(Q)]

    old = list(range(m))
    rot = list(range(1, m)) + [N]
    mid = list(range(1, m))
    VA = Es + Fs(old)
    VB = Es + Fs(rot)
    VC = Es + Fs(mid)
    F0N = [T_F(0, N, a, b, n) for a in range(Q) for b in range(Q)]
    pts = rand_points(A0, (len(VA) + len(VB) + 9) // 2 + 10, rng, 1)

    def dim(vs):
        return rank(eval_terms_matrix(A0, vs, pts, 1, ncomp=2))

    dA, dB, dC = dim(VA), dim(VB), dim(VC)
    dAB = dim(VA + VB)
    dABF = dim(VA + VB + F0N)
    print(f'(C) n={n}, m={m}: dim A={dA} (|A|={len(VA)}, 9m^2-6m={9 * m * m - 6 * m}), dim B={dB}, '
          f'dim C={dC} (|C|={len(VC)}), dim(A+B)={dAB}, dim(A+B+F0N)={dABF} (target {3 * n * (3 * n - 2) - 12}), '
          f'dim(A cap B)={dA + dB - dAB}', flush=True)


if __name__ == '__main__':
    ns = [int(x) for x in sys.argv[1:]] or [4, 5, 6]
    for n in ns:
        part_A(n, 11 + n)
    for n in ns:
        part_B(n, 21 + n)
    for n in ns:
        part_C(n, 31 + n)
