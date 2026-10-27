#!/usr/bin/env python3
"""All-T dimension theorem dim M_T = ell(Q,T) and the canonical basis (research/GENERALQ_ALLT_PROOF.md).
Exact checks mod p = 2^61 - 1 (and exact rationals where stated).

(0) The canonical family (DHW's index set (24)-(25), generation orders (t, s1, s2, rest, T) and (t, s2, s1, rest, T)):
    exact rational check of its quotient images c(q) e_q0 (I - K_(s2+1)) (every non-lift member, (Q,T) = (3,5), (4,5));
    raw rank = ell(Q,T) and every row a valid moment at (Q,T) = (3,5), (3,6), (4,6) (T > Q+1); DHW's own family at
    (3,5), (3,6) for comparison.
(1) (Gen) at the witness point of Lemma 2.1 (every set of <= Q distinct forms from {eta_i} u {L_tr} is
    independent), for the block numbers used below.
(2) Lemma 4.1 (capped fat-ideal lemma), k blocks: the products P(S, r_S) = prod_{t in S} h_{t r_t} prod_{u not in S} D_u
    with |S| <= min(k, Q-1) lie in the fat ideal J^(k) (all partial derivatives of order < m_Z vanish at random
    points of every stratum Z, m_Z = number of blocks), are independent, and span J_{kQ}; and
    dim S_1 J_{kQ} = dim J_{kQ+1} = dim S_1 H_1 ... H_k.
(3) Lemma 5.2: the canonical multi-heads with |H| <= Q-2 have numerators g_i in J_{kQ} with sum_i eta_i g_i = 0,
    are independent (rank N_Q(k) as rational vectors), and dim K = Q dim J_{kQ} - dim J_{kQ+1} = N_Q(k).
(4) raw dim M_T = ell(Q,T) from the path likelihoods at random economic points with distinct covariates.
(5) the recursion ell(Q,T+1) = Q ell(Q,T) + N_Q(T-1) of eq. (25), and DHW's Table 1.
Points: (2), (3) at the witness point and at a random product-form point. What this does not show: anything
beyond the listed (Q, k) and (Q, T); the proof is in the note. Run: ../../../.venv/bin/python hq_fresh_generalQ_allT.py
"""
import itertools as it
import random
import sys
import time
from math import comb
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hq_fresh_generalQ_T4 import monos, point_on, P  # noqa: E402
from hq_fresh_generalQ_dim import deriv_rows, ell, raw_dim, witness_blocks  # noqa: E402


def N_Q(Q, k):
    return sum(comb(k, j) * (k - j) * Q ** (j + 1) for j in range(min(Q - 2, k - 1) + 1))


def sigma(Q, k):
    return sum(comb(k, j) * Q ** j for j in range(min(k, Q - 1) + 1))


def random_blocks(Q, k, rng):
    g = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
    u = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(k)]
    return [[[g[j][r] * u[t][j] % P for j in range(Q)] for r in range(Q)] for t in range(k)]   # A[t][r] = coeffs of L_tr


def gen_holds(Q, A):
    eta = [[1 if j == i else 0 for j in range(Q)] for i in range(Q)]
    forms = eta + [A[t][r] for t in range(len(A)) for r in range(Q)]
    for size in range(2, Q + 1):
        for F in it.combinations(forms, size):
            if flint.nmod_mat([list(f) for f in F], P).rank() < size:
                return False
    return True


def strata(Q, A):
    """all nonempty intersections of base-locus components of distinct blocks: (blocks, defining forms)"""
    k = len(A)
    eta = [[1 if j == i else 0 for j in range(Q)] for i in range(Q)]
    comps = [[(tuple(A[t][s]), tuple(A[t][s2])) for s, s2 in it.combinations(range(Q), 2)] +
             [(tuple(eta[r]), tuple(A[t][r])) for r in range(Q)] for t in range(k)]
    out, frontier = [], [((), ())]
    while frontier:
        new = []
        for blocks, fs in frontier:
            for t in range((blocks[-1] + 1) if blocks else 0, k):
                for c in comps[t]:
                    f2 = tuple(dict.fromkeys(fs + c))
                    if flint.nmod_mat([list(f) for f in f2], P).rank() < Q:
                        new.append((blocks + (t,), f2))
        out += new
        frontier = new
    return out


def fat_conditions(Q, d, st, rng):
    ms = monos(Q, d)
    rows = []
    for blocks, fs in st:
        basis = []
        for f in fs:
            if flint.nmod_mat(basis + [list(f)], P).rank() > len(basis):
                basis.append(list(f))
        dimZ = Q - 1 - len(basis)
        npts = (comb(d + dimZ, dimZ) + 2) if dimZ > 0 else 1
        for _ in range(npts):
            rows += deriv_rows(ms, point_on(basis, Q, rng), Q, len(blocks))
    return ms, flint.nmod_mat(rows, P)


def coef_vec(poly, index, nm):
    v = [0] * nm
    for mono, c in poly.to_dict().items():
        v[index[mono]] = int(c)
    return v


def check_lemmas(Q, k, A, rng, label, sample=400):
    t0 = time.time()
    ctx = flint.fmpz_mod_mpoly_ctx.get(('x', Q), modulus=P)
    x = ctx.gens()
    L = [[sum((A[t][r][i] * x[i] for i in range(Q)), ctx.from_dict({})) for r in range(Q)] for t in range(k)]
    D = [L[t][0] for t in range(k)]
    for t in range(k):
        for r in range(1, Q):
            D[t] = D[t] * L[t][r]
    def h(t, r):
        f = x[r]
        for s in range(Q):
            if s != r:
                f = f * L[t][s]
        return f
    hh = [[h(t, r) for r in range(Q)] for t in range(k)]
    st = strata(Q, A)
    d0 = k * Q
    ms0, C0 = fat_conditions(Q, d0, st, rng)
    ms1, C1 = fat_conditions(Q, d0 + 1, st, rng)
    idx0 = {m: i for i, m in enumerate(ms0)}
    idx1 = {m: i for i, m in enumerate(ms1)}
    dimJ0 = len(ms0) - C0.rank()
    dimJ1 = len(ms1) - C1.rank()
    # products P(S, r_S)
    prods = []
    for j in range(min(k, Q - 1) + 1):
        for S in it.combinations(range(k), j):
            for rS in it.product(range(Q), repeat=j):
                f = ctx.from_dict({tuple([0] * Q): 1})
                for t, r in zip(S, rS):
                    f = f * hh[t][r]
                for u in range(k):
                    if u not in S:
                        f = f * D[u]
                prods.append(f)
    Pm = flint.nmod_mat([coef_vec(f, idx0, len(ms0)) for f in prods], P)
    in_J = (C0 * Pm.transpose()).rank() == 0
    rk_prods = Pm.rank()
    S1P = flint.nmod_mat([coef_vec(x[i] * f, idx1, len(ms1)) for f in prods for i in range(Q)], P)
    rk_S1J = S1P.rank()
    # product span S_1 H_1...H_k by evaluation
    N = len(ms1) + 30
    pts = [[rng.randint(1, P - 1) for _ in range(Q)] for _ in range(N)]
    def ev_lin(c, p):
        return sum(ci * pi for ci, pi in zip(c, p)) % P
    cur = [[p[i] for p in pts] for i in range(Q)]
    for t in range(k):
        Hv = []
        for r in range(Q):
            vals = []
            for p in pts:
                v = p[r]
                for s in range(Q):
                    if s != r:
                        v = v * ev_lin(A[t][s], p) % P
                vals.append(v)
            Hv.append(vals)
        M = flint.nmod_mat([[a * b % P for a, b in zip(v, hv)] for v in cur for hv in Hv], P)
        R, rk = M.rref()
        cur = [[int(R[i, j]) for j in range(N)] for i in range(rk)]
    dimV = len(cur)
    ok41 = (in_J and rk_prods == len(prods) == dimJ0 == sigma(Q, k) and rk_S1J == dimJ1 == dimV)
    # canonical multi-heads, |H| <= Q-2
    heads = []
    for j in range(min(Q - 2, k - 1) + 1):
        for H in it.combinations(range(k), j):
            for s in range(k):
                if s in H:
                    continue
                for qH in it.product(range(Q), repeat=j):
                    for q0 in range(Q):
                        heads.append((H, qH, s, q0))
    # rank as rational vectors (evaluation; zero-sum, drop last component)
    npts = len(heads) // (Q - 1) + 6
    rows = [[] for _ in heads]
    for _ in range(npts):
        p = [rng.randint(1, P - 1) for _ in range(Q)]
        Lp = [[ev_lin(A[t][a], p) for a in range(Q)] for t in range(k)]
        for n_, (H, qH, s, q0) in enumerate(heads):
            sc = p[q0]
            for uu, qu in zip(H, qH):
                sc = sc * p[qu] % P * pow(Lp[uu][qu], P - 2, P) % P
            inv = pow(Lp[s][q0], P - 2, P)
            vec = [((1 if i == q0 else 0) - A[s][q0][i] * p[i] % P * inv) % P for i in range(Q)]
            rows[n_].extend([sc * vec[i] % P for i in range(Q - 1)])
    rk_heads = flint.nmod_mat(rows, P).rank()
    # numerators in J_{kQ} and zero eta-sum, on a sample
    sub = heads if len(heads) <= sample else rng.sample(heads, sample)
    num_rows, eta_ok = [], True
    for (H, qH, s, q0) in sub:
        base = ctx.from_dict({tuple([0] * Q): 1})
        for uu, qu in zip(H, qH):
            base = base * hh[uu][qu]
        for t in range(k):
            if t not in H and t != s:
                base = base * D[t]
        g = []
        for i in range(Q):
            if i != q0:
                g.append(base * hh[s][q0] * (-A[s][q0][i] % P))
            else:
                g.append(base * (D[s] - hh[s][q0] * A[s][q0][q0]))
        tot = ctx.from_dict({})
        for i in range(Q):
            tot = tot + x[i] * g[i]
        eta_ok &= tot.is_zero()
        num_rows += [coef_vec(gi, idx0, len(ms0)) for gi in g]
    num_in_J = (C0 * flint.nmod_mat(num_rows, P).transpose()).rank() == 0
    dimK = Q * dimJ0 - dimJ1
    ok52 = (rk_heads == len(heads) == N_Q(Q, k) == dimK and num_in_J and eta_ok)
    mult = {}
    for b, _ in st:
        mult[len(b)] = mult.get(len(b), 0) + 1
    print(f'  Q={Q} k={k} [{label}] strata by multiplicity {mult}: dim J_kQ = {dimJ0} (sigma = {sigma(Q, k)}), '
          f'products in J: {in_J}, independent: {rk_prods == len(prods)}; dim S_1 J_kQ = {rk_S1J}, '
          f'dim J_(kQ+1) = {dimJ1}, dim S_1 H..H = {dimV}  -> Lemma 4.1: {ok41}', flush=True)
    print(f'  Q={Q} k={k} [{label}] multi-heads |H| <= Q-2: {len(heads)} (N_Q = {N_Q(Q, k)}), rank {rk_heads}; '
          f'numerators in J and zero eta-sum ({len(sub)} checked): {num_in_J and eta_ok}; '
          f'dim K = Q dim J_kQ - dim J_(kQ+1) = {dimK}  -> Lemma 5.2: {ok52}   [{time.time() - t0:.0f}s]', flush=True)
    return ok41 and ok52


def canon_indices(Q, T):
    """DHW's index set (24)-(25) (zero-based periods 0..T-1), with the canonical generation orders
    tau1 = (t, s1, s2, rest, T-1), tau2 = (t, s2, s1, rest, T-1)."""
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
                for values in it.product(range(Q), repeat=j + 1):
                    ans.append((shared, s1, s2, values, list(shared) + [s1, s2] + tail + [T - 1],
                                list(shared) + [s2, s1] + tail + [T - 1]))
    return ans


def canon_images_exact(Q, T, rng):
    """exact rational check of the quotient image of every non-lift canonical moment:
    sum_{y: y_1 = i} m(y) p_y = c(q) (delta_{i q0} - K_{s2+1}(q0, i))."""
    from fractions import Fraction
    import hq_fresh_generalQ as GQ
    pi = [[[Fraction(rng.randint(1, 9)) for _ in range(Q)] for _ in range(Q)] for _ in range(T)]   # pi[t][i][a]
    X = [Fraction(rng.randint(1, 9)) for _ in range(Q)]
    y0 = 0
    Ks = []
    for t in range(T):
        Kt = []
        for a in range(Q):
            Lta = sum(pi[t][j][a] * X[j] for j in range(Q))
            Kt.append([pi[t][i][a] * X[i] / Lta for i in range(Q)])
        Ks.append(Kt)
    paths = list(it.product(range(Q), repeat=T))
    py = {}
    for y in paths:
        w, prev = Fraction(1), y0
        for t in range(T):
            w *= Ks[t][prev][y[t]]
            prev = y[t]
        py[y] = w
    n_new = 0
    for shared, s1, s2, values, tau1, tau2 in canon_indices(Q, T):
        if 0 in shared:
            continue
        q0 = values[0]
        C = [Fraction(0)] * Q
        for y in paths:
            if any(y[t] != v for t, v in zip(shared, values[1:])):
                continue
            a_ = GQ.weight(y, tau1, y0, pi) if y[s1] == q0 else 0
            b_ = GQ.weight(y, tau2, y0, pi) if y[s2] == q0 else 0
            C[y[0]] += (a_ - b_) / GQ.weight(y, list(range(T)), y0, pi) * py[y]
        chain = [y0] + list(values[1:]) + [q0]
        heads = [0] + [t + 1 for t in shared]
        pref = Fraction(1)
        for k_, (st_, en) in enumerate(zip(chain[:-1], chain[1:])):
            pref *= Ks[heads[k_]][st_][en]
        pred = [pref * ((1 if i == q0 else 0) - Ks[s2 + 1][q0][i]) for i in range(Q)]
        if C != pred:
            return False, n_new
        n_new += 1
    return True, n_new


def canon_raw_rank(Q, T, rng, which='canon'):
    import hq_fresh_generalQ as GQ
    g = [[rng.randint(2, 10 ** 6) for _ in range(Q)] for _ in range(Q)]
    w = [rng.randint(2, 10 ** 6) for _ in range(Q)]
    xs = rng.sample(range(1, 40), T)
    pi = [[[g[q][r] * pow(w[q], xs[t], P) % P for r in range(Q)] for q in range(Q)] for t in range(T)]
    idx = canon_indices(Q, T) if which == 'canon' else GQ.source_indices(Q, T)
    paths = list(it.product(range(Q), repeat=T))
    rows = []
    for shared, s1, s2, values, tau1, tau2 in idx:
        q = values[0]
        row = []
        for y in paths:
            if any(y[t] != v for t, v in zip(shared, values[1:])):
                row.append(0)
                continue
            a = GQ.weight(y, tau1, 0, pi) if y[s1] == q else 0
            b = GQ.weight(y, tau2, 0, pi) if y[s2] == q else 0
            row.append(int(a - b) % P)
        rows.append(row)
    valid = True
    for _ in range(2):
        eta = [rng.randint(1, P - 1) for _ in range(Q)]
        col = []
        for y in paths:
            v, prev = 1, 0
            for t in range(T):
                L = sum(pi[t][i][prev] * eta[i] for i in range(Q)) % P
                v = v * eta[y[t]] % P * pow(L, P - 2, P) % P
                prev = y[t]
            col.append(v)
        valid &= all(sum(a * b for a, b in zip(r, col)) % P == 0 for r in rows)
    return len(idx), flint.nmod_mat(rows, P).rank(), valid


def main():
    rng = random.Random(2610)
    allok = True
    print('(0) canonical family (generation orders (t,s1,s2,rest,T), (t,s2,s1,rest,T)):')
    for Q, T in [(3, 5), (4, 5)]:
        t0 = time.time()
        ok, nn = canon_images_exact(Q, T, rng)
        allok &= ok
        print(f'  Q={Q} T={T}: quotient image c(q) e_q0 (I - K_(s2+1)) exact for all {nn} non-lift members: {ok}  '
              f'[{time.time() - t0:.0f}s]', flush=True)
    for Q, T, which in [(3, 5, 'canon'), (3, 6, 'canon'), (4, 6, 'canon'), (3, 5, 'dhw'), (3, 6, 'dhw')]:
        t0 = time.time()
        size, rk, valid = canon_raw_rank(Q, T, rng, which)
        allok &= (valid and rk == size == ell(Q, T))
        print(f'  Q={Q} T={T} [{which}]: |family| = {size}, ell = {ell(Q, T)}, raw rank = {rk}, all rows valid moments: '
              f'{valid}  [{time.time() - t0:.0f}s]', flush=True)
    print('(1) (Gen) at the witness point of Lemma 2.1:')
    for Q, k in [(3, 6), (4, 5)]:
        g = gen_holds(Q, witness_blocks(Q, k))
        allok &= g
        print(f'  Q={Q}, {k} blocks: {g}', flush=True)
    print('(2)-(3) Lemmas 4.1 and 5.2 (k >= Q is the new range):')
    for Q, k in [(3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5)]:
        allok &= check_lemmas(Q, k, witness_blocks(Q, k), rng, 'witness')
        allok &= check_lemmas(Q, k, random_blocks(Q, k, rng), rng, 'random')
    print('(4) raw dim M_T from path likelihoods (distinct covariates):')
    for Q, T in [(3, 5), (3, 6), (4, 6)]:
        t0 = time.time()
        r = raw_dim(Q, T, rng)
        allok &= (r == ell(Q, T))
        print(f'  Q={Q} T={T}: raw dim M_T = {r}, ell = {ell(Q, T)}  [{time.time() - t0:.0f}s]', flush=True)
    print('(5) recursion ell(Q,T+1) = Q ell(Q,T) + N_Q(T-1), and DHW Table 1:')
    rec = all(ell(Q, T + 1) == Q * ell(Q, T) + N_Q(Q, T - 1) for Q in range(2, 11) for T in range(2, 25))
    table = {2: [2, 8, 22, 52, 114, 240], 3: [3, 33, 162, 606, 2013, 6327], 4: [4, 56, 524, 3072, 14548, 62536],
             5: [5, 85, 965, 9145, 62500, 358280], 6: [6, 120, 1602, 17844, 179094, 1399680],
             7: [7, 161, 2471, 31633, 364791, 3929793], 8: [8, 208, 3608, 52192, 679976, 8274160]}
    tab = all(ell(Q, T) == table[Q][T - 3] for Q in table for T in range(3, 9))
    allok &= rec and tab
    print(f'  recursion (Q <= 10, T <= 24): {rec}; Table 1 (Q = 2..8, T = 3..8): {tab}', flush=True)
    print('ALL CHECKS PASSED' if allok else 'SOME CHECK FAILED')


if __name__ == '__main__':
    main()
