#!/usr/bin/env python3
"""Exact det R_n and its factorisation against natural geometric quantities.

R_n is the matrix expressing the j=1 source columns F_{t,s,a,b} in the
canonical basis {E, B} of the quotient space W_n (B-coefficients only; the
E-coefficients form a unipotent block, so det(change of basis) = det R_n).

Checks performed (all exact, Fraction arithmetic):
 1. Expansion validity: for every F, the E- and B-coefficients extracted by
    single- and double-pole residues reconstruct F exactly at random points.
 2. n = 2: R_2 is the identity (F = B when there is no suffix).
 3. n = 3 (and n = 4 if requested): det R_n as an exact rational, its prime
    factorisation, and the prime factorisations of the natural quantities
    (cross-point coordinates X_i(P), third-line values L_{wc}(P), entries and
    determinants of the A_t).  Primes of det R_n that do not divide any
    natural quantity signal an irreducible factor without a product formula.

What this does not show: anything for general n.  It is a structural probe.
"""
import argparse
import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hq_fresh_lib as lib  # noqa: E402

Q = 3


def random_blocks(n, rng, product_form=True):
    while True:
        if product_form:
            g = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(Q)]
            us = [[rng.randint(1, 9) for _ in range(Q)] for _ in range(n)]
            A = [[[Fraction(g[i][a] * us[t][i]) for i in range(Q)] for a in range(Q)] for t in range(n)]
        else:
            A = [[[Fraction(rng.randint(1, 9)) for _ in range(Q)] for _ in range(Q)] for _ in range(n)]
        ok, msg = lib.check_geometry(A, n)
        if ok and all(lib.det_fraction(A[t]) != 0 for t in range(n)):
            return A


def eval_F(A, n, t, s, a, b, X):
    mats = {w: lib.kernel_at(A[w], X) for w in range(n)}
    W = lib.word(lib.increasing_word(s, {t}, n), mats)
    pref = X[a] * mats[t][a][b]
    return [pref * (int(i == b) - W[b][i]) for i in range(Q)]


def eval_E(A, s, a, X):
    K = lib.kernel_at(A[s], X)
    return [X[a] * (int(i == a) - K[a][i]) for i in range(Q)]


def eval_B(A, t, s, a, b, X):
    Kt = lib.kernel_at(A[t], X)
    Ks = lib.kernel_at(A[s], X)
    pref = X[a] * Kt[a][b]
    return [pref * (int(i == b) - Ks[b][i]) for i in range(Q)]


def point_on_line(A, n, t, c, rng):
    """A rational point on L_{tc}, off every other line and coordinate line."""
    A_t = A[t]
    while True:
        y = Fraction(rng.randint(-40, 40)), Fraction(rng.randint(-40, 40))
        # solve A[c][0] X0 + A[c][1] X1 + A[c][2] X2 = 0 with X1, X2 = y
        if A_t[c][0] == 0:
            continue
        X0 = -(A_t[c][1] * y[0] + A_t[c][2] * y[1]) / A_t[c][0]
        X = [X0, y[0], y[1]]
        if any(x == 0 for x in X):
            continue
        if any(lib.dot(A[u][e], X) == 0 for u in range(n) for e in range(Q) if (u, e) != (t, c)):
            continue
        return X


def single_residue_of_F(A, n, t, s, a, b, w, c, X0):
    """(L_{wc} F_{t,s,a,b})|_{X0}, X0 on L_{wc} and on no other line."""
    if t == w and a != c:
        return [Fraction(0)] * Q
    mats = {}
    for u in range(n):
        mats[u] = lib.residue_kernel(A[w], c, X0) if u == w else lib.kernel_at(A[u], X0)
    pref = A[t][a][b] * X0[b]
    if t != w:
        pref = pref / lib.dot(A[t][a], X0)
    W = lib.word(lib.increasing_word(s, {t}, n), mats)
    if t == w:
        # prefactor carries the pole; the word is regular (w not in word? it is, as K_w in suffix or s)
        # K_w also appears inside the word; but with t == w the block w is not in the word.
        mats_reg = {u: lib.kernel_at(A[u], X0) for u in range(n) if u != w}
        W = lib.word(lib.increasing_word(s, {t}, n), mats_reg)
        return [X0[a] * pref * (int(i == b) - W[b][i]) for i in range(Q)]
    return [-X0[a] * pref * x for x in W[b]]


def e_coefficients(A, n, t, s, a, b, bcoef, rng):
    """E-coefficients of F_{t,s,a,b} from single-line residues, checked at two points."""
    coeffs = {}
    for w in range(n):
        for c in range(Q):
            vals = []
            for _ in range(2):
                X0 = point_on_line(A, n, w, c, rng)
                res = single_residue_of_F(A, n, t, s, a, b, w, c, X0)
                # subtract B residues along L_{wc}
                for (u, v, cc, d), coef in bcoef.items():
                    if coef == 0:
                        continue
                    if u == w and cc == c:
                        Kv = lib.kernel_at(A[v], X0)
                        r = [A[w][c][d] * X0[c] * X0[d] * (int(i == d) - Kv[d][i]) for i in range(Q)]
                    elif v == w and d == c:
                        Ku = lib.kernel_at(A[u], X0)
                        vw = [A[w][c][i] * X0[i] for i in range(Q)]
                        r = [-X0[cc] * Ku[cc][c] * x for x in vw]
                    else:
                        continue
                    res = [x - coef * y for x, y in zip(res, r)]
                base = [-X0[c] * A[w][c][i] * X0[i] for i in range(Q)]
                # res must be a multiple of base
                k = next(i for i in range(Q) if base[i] != 0)
                lam = res[k] / base[k]
                assert all(res[i] == lam * base[i] for i in range(Q)), 'residue not proportional to E residue'
                vals.append(lam)
            assert vals[0] == vals[1], 'E coefficient not constant along the line'
            coeffs[(w, c)] = vals[0]
    return coeffs


def validate_expansion(A, n, rng, samples=3):
    cols, rows = lib.b_coefficient_matrix(A, n)
    for ci, (t, s, a, b) in enumerate(cols):
        bcoef = {key: rows[key][ci] for key in rows}
        ecoef = e_coefficients(A, n, t, s, a, b, bcoef, rng)
        for _ in range(samples):
            X = [Fraction(rng.randint(1, 30)) for _ in range(Q)]
            lhs = eval_F(A, n, t, s, a, b, X)
            rhs = [Fraction(0)] * Q
            for (u, v, c, d), coef in bcoef.items():
                if coef:
                    rhs = [x + coef * y for x, y in zip(rhs, eval_B(A, u, v, c, d, X))]
            for (w, c), coef in ecoef.items():
                if coef:
                    rhs = [x + coef * y for x, y in zip(rhs, eval_E(A, w, c, X))]
            assert lhs == rhs, f'expansion fails for F{(t, s, a, b)}'
    return cols, rows


def natural_quantities(A, n):
    vals = {}
    for t in range(n):
        vals[f'detA[{t}]'] = lib.det_fraction(A[t])
        for a in range(Q):
            for i in range(Q):
                vals[f'A[{t}][{a}][{i}]'] = A[t][a][i]
    pairs = [(t, a) for t in range(n) for a in range(Q)]
    for i1 in range(len(pairs)):
        for i2 in range(i1 + 1, len(pairs)):
            (u, c), (v, d) = pairs[i1], pairs[i2]
            if u == v:
                continue
            P = lib.cross(A[u][c], A[v][d])
            for i in range(Q):
                vals[f'X{i}(P{u}{c},{v}{d})'] = P[i]
            for w in range(n):
                for e in range(Q):
                    if (w, e) not in ((u, c), (v, d)):
                        vals[f'L{w}{e}(P{u}{c},{v}{d})'] = lib.dot(A[w][e], P)
    return vals


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--n', type=int, nargs='+', default=[2, 3])
    ap.add_argument('--seed', type=int, default=7)
    ap.add_argument('--general', action='store_true', help='random A_t instead of product form')
    ap.add_argument('--trials', type=int, default=2)
    args = ap.parse_args()
    for n in args.n:
        for trial in range(args.trials):
            rng = random.Random(args.seed + 1000 * n + trial)
            A = random_blocks(n, rng, product_form=not args.general)
            cols, rows = validate_expansion(A, n, rng)
            M = [rows[key] for key in cols]   # square: rows keyed by same ordered 4-tuples
            print(f'n={n} trial={trial}: expansion of all {len(cols)} F columns reconstructed exactly '
                  f'(E and B coefficients from residues).')
            if n == 2:
                ident = all(M[i][j] == (1 if i == j else 0) for i in range(len(M)) for j in range(len(M)))
                print(f'   R_2 == identity: {ident}')
                continue
            d = lib.det_fraction(M)
            print(f'   det R_{n}: numerator has {len(str(abs(d.numerator)))} digits, '
                  f'denominator has {len(str(d.denominator))} digits, sign {"+" if d > 0 else "-"}')
            nat = natural_quantities(A, n)
            nat_primes = set()
            for v in nat.values():
                nat_primes |= set(lib.factorize(v.numerator)) | set(lib.factorize(v.denominator))
            # smooth part over natural primes and small primes
            small = [p for p in range(2, 20000) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
            trial = sorted(nat_primes | set(small))
            num, den = abs(d.numerator), d.denominator
            num_f, den_f = {}, {}
            for p in trial:
                while num % p == 0:
                    num //= p
                    num_f[p] = num_f.get(p, 0) + 1
                while den % p == 0:
                    den //= p
                    den_f[p] = den_f.get(p, 0) + 1
            print(f'   numerator smooth part:   {num_f}')
            print(f'   denominator smooth part: {den_f}')
            print(f'   numerator cofactor after removing natural/small primes: {num if num < 10**40 else str(num)[:20] + "...(" + str(len(str(num))) + " digits)"}')
            print(f'   denominator cofactor: {den if den < 10**40 else str(den)[:20] + "...(" + str(len(str(den))) + " digits)"}')
            foreign = [p for p in set(num_f) | set(den_f) if p not in nat_primes]
            print(f'   small primes in det not dividing any natural quantity: {sorted(foreign)}')
            for p in sorted(set(num_f) | set(den_f)):
                if p > 50:
                    carriers = [k for k, v in nat.items() if (v.numerator % p == 0) or (v.denominator % p == 0)]
                    print(f'   prime {p}^({num_f.get(p, 0)}-{den_f.get(p, 0)}): natural carriers {carriers[:6]}{"..." if len(carriers) > 6 else ""}')
            sys.stdout.flush()


if __name__ == '__main__':
    main()
