#!/usr/bin/env python3
"""Exact binary-axis checks for selected actual first-slot differences.

At X0=0 and x=X1/X2, block t has the actual two-state kernel
  K_t=[[x/(x+sigma*z_t), sigma*z_t/(x+sigma*z_t)],
       [x/(x+tau*z_t), tau*z_t/(x+tau*z_t)]].
Here sigma=G[1][2]/G[1][1], tau=G[2][2]/G[2][1], z_t=v_t/u_t.
Let Delta=prod det(K_t), and p(P)=P[0][1]. For the ascending prefix Ppre
before s with t omitted, the scalar formula to check is
  (F_t,s,a,b-F_t,r(t),a,b)_2 / (X2*Delta) = -H_t,a,b*kappa,
  kappa=((1-d_s)*p(Ppre)-(1-det(Ppre))*p(K_s))/(det(Ppre)*d_s).

The pole matrix is constructed independently from actual ordered products:
at x=-sigma*z_u or -tau*z_u, replace the relevant row of K_u by its
residue numerator and the other row by zero. No old source matrix O or
full three-state source/residue system is built.

Only the finite m=3,...,8 fixtures below are certified. The Laurent endpoint
induction and uniform T2(N) surjectivity are separate paper obligations.

Reproduce:
  nice -n 19 python3 exploration/source24_binary_axis_spanning.py --output exploration/source24-binary-axis-spanning-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming


P, G = incoming.P, incoming.G
residue, sparse = incoming.residue, incoming.sparse


def inverse(x):
    assert x % P, 'A stated denominator vanishes at this fixture.'
    return pow(x % P, -1, P)


def product(kernels, word):
    result = [[1, 0], [0, 1]]
    for t in word:
        result = residue.matmul(result, kernels[t], P)
    return result


def determinant(matrix):
    return (matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]) % P


def binary_kernel(sigma, tau, z, x, pole_state=None):
    result = []
    for a, rate in enumerate((sigma, tau), start=1):
        numerator = [x % P, rate * z % P]
        denominator = sum(numerator) % P
        if pole_state is None:
            result.append([value * inverse(denominator) % P for value in numerator])
        else:
            assert (denominator == 0) == (a == pole_state)
            result.append(numerator if a == pole_state else [0, 0])
    if pole_state is None:
        assert all(sum(row) % P == 1 for row in result)
    else:
        assert all(sum(row) % P == 0 for row in result)
    return result


def words(m, t, s):
    ascending = [u for u in range(1, m + 1) if u != t]
    moved = [s] + [u for u in ascending if u != s]
    return ascending, moved


def source_difference(kernels, m, t, s, a, b, x):
    """Component 2 divided by X2, with the actual K_t(a,b) factor."""
    ascending, moved = words(m, t, s)
    base, first = product(kernels, ascending), product(kernels, moved)
    Xa = x if a == 1 else 1
    return Xa * kernels[t][a - 1][b - 1] * (base[b - 1][1] - first[b - 1][1]) % P


def selected_columns(m):
    pairs = [(3, 2), (2, 3)] + [(m, j) for j in range(3, m)]
    assert len(pairs) == m - 1 and len(set(pairs)) == m - 1
    columns = [(t, s, a, b) for t, s in pairs for a in (1, 2) for b in (1, 2)]
    assert all(s != min(u for u in range(1, m + 1) if u != t) for t, s in pairs)
    return pairs, columns


def quadratic_coprime(sigma, tau, z):
    """Verify a constant Bezout combination, not just numerical root samples."""
    z1, z2, z3 = z[1], z[2], z[3]
    Q12 = [sigma * tau * z1 * z2 % P, tau * (z1 + z2) % P, 1]
    Q13 = [sigma * tau * z1 * z3 % P, tau * (z1 + z3) % P, 1]
    scale = tau * (z2 - z3) % P
    remainder = sigma * (sigma - tau) * z1 * z1 % P
    assert scale and remainder
    assert [(a - b) % P for a, b in zip(Q12, Q13)] == [scale * sigma * z1 % P, scale, 0]
    root = -sigma * z1 % P
    assert sum(c * pow(root, i, P) for i, c in enumerate(Q12)) % P == remainder
    quotient = [tau * (z1 + z2) - sigma * z1, 1]
    V = [c * inverse(scale * remainder) % P for c in quotient]
    U = [(inverse(remainder) - V[0]) % P, -V[1] % P]
    combination = [0] * 4
    for left, right in ((U, Q12), (V, Q13)):
        for i, x in enumerate(left):
            for j, y in enumerate(right):
                combination[i + j] = (combination[i + j] + x * y) % P
    assert combination == [1, 0, 0, 0]
    return dict(Q12=Q12, Q13=Q13, coefficient_order='Increasing powers of x.',
                difference_scale=scale, Q12_at_minus_sigma_z1=remainder,
                Bezout_U=U, Bezout_V=V, U_times_Q12_plus_V_times_Q13_equals_one=True)


def calculate(m):
    started = time.monotonic()
    times = sparse.factors(m, 'economic')
    sigma = G[1][2] * inverse(G[1][1]) % P
    tau = G[2][2] * inverse(G[2][1]) % P
    c = (tau - sigma) % P
    assert sigma and tau and c
    z = {t: v * inverse(u) % P for t, (u, v) in enumerate(times, start=1)}
    pairs, columns = selected_columns(m)
    poles = [(u, state, -rate * z[u] % P) for u in range(1, m + 1)
             for state, rate in ((1, sigma), (2, tau))]
    assert all(pole for _, _, pole in poles)
    assert len({pole for _, _, pole in poles}) == 2 * m
    pole_matrix = []
    for u, state, x in poles:
        kernels = {t: binary_kernel(sigma, tau, z[t], x, state if t == u else None)
                   for t in range(1, m + 1)}
        pole_matrix.append([source_difference(kernels, m, t, s, a, b, x)
                            for t, s, a, b in columns])

    ordinary = []
    formula_checks = reconstruction_checks = 0
    for x in (1, 2, 7):
        kernels = {t: binary_kernel(sigma, tau, z[t], x) for t in range(1, m + 1)}
        d = {t: determinant(kernels[t]) for t in kernels}
        Delta = 1
        for t in kernels:
            explicit = c * z[t] * x * inverse((x + sigma * z[t]) * (x + tau * z[t])) % P
            assert d[t] == explicit and explicit
            Delta = Delta * d[t] % P
        kappas = {}
        for t, s in pairs:
            prefix = [u for u in range(1, s) if u != t]
            Ppre = product(kernels, prefix)
            determinant_prefix = determinant(Ppre)
            kappa = ((1 - d[s]) * Ppre[0][1] - (1 - determinant_prefix) * kernels[s][0][1])
            kappas[t, s] = kappa * inverse(determinant_prefix * d[s]) % P
        direct = []
        for t, s, a, b in columns:
            H = {(1, 1): x * (x + tau * z[t]) * inverse(c * z[t]),
                 (1, 2): sigma * (x + tau * z[t]) * inverse(c),
                 (2, 1): (x + sigma * z[t]) * inverse(c * z[t]),
                 (2, 2): tau * (x + sigma * z[t]) * inverse(c * x)}
            value = source_difference(kernels, m, t, s, a, b, x)
            assert value * inverse(Delta) % P == -H[a, b] * kappas[t, s] % P, (
                'Actual first-slot difference/scalar formula mismatch.', m, x, t, s, a, b)
            direct.append(value)
            formula_checks += 1
        # Each difference is bounded at infinity and zero at x=0. Its simple
        # pole residues therefore reconstruct it with this fixed constant term.
        weights = [(inverse(x - pole) + inverse(pole)) % P for _, _, pole in poles]
        reconstructed = incoming.schur.matrix_product([weights], pole_matrix)[0]
        assert reconstructed == direct, ('Direct pole reconstruction mismatch.', m, x)
        reconstruction_checks += len(columns)
        ordinary.append(dict(x=x, Delta=Delta, direct_values_sha256=residue.matrix_hash([direct])))
    certificate = incoming.matrix_certificate(pole_matrix)
    assert certificate['rank_certificate']['rank'] == 2 * m
    result = dict(m=m, prime=P, G=G, time_fixture='economic', time_factors=times,
                  sigma=sigma, tau=tau, c=c, z=[z[t] for t in range(1, m + 1)],
                  selected_pairs=pairs, columns=columns,
                  column_convention='(t,s,a,b) means actual F_t,s,a,b−F_t,r(t),a,b; blocks t,s are one-based and states a,b are 1 or 2.',
                  pole_labels=poles,
                  pole_convention='Row (u,state,pole) is the coefficient of 1/(x−pole) in component 2 divided by X2; no additional source normalization.',
                  direct_pole_matrix=certificate, full_binary_pole_span_over_Fp=True,
                  quadratic_coprimality=quadratic_coprime(sigma, tau, z),
                  ordinary_points=ordinary, normalized_difference_formula_checks=formula_checks,
                  direct_residue_reconstruction_checks=reconstruction_checks,
                  all_poles_nonzero_and_distinct=True, every_ordinary_denominator_nonzero=True,
                  elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(m=m, columns=len(columns), pole_rank=certificate['rank_certificate']['rank'],
                          target=2*m, minor_determinant=certificate['rank_certificate']['nonzero_minor']['determinant_mod_prime'],
                          formula_checks=formula_checks, seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second binary-axis cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024**2:
            raise TimeoutError('95 MiB binary-axis RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation, current = None, None
    try:
        for current in range(3, 9):
            cases.append(calculate(current))
    except TimeoutError as error:
        limitation = dict(m=current, reason=str(error))
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Exact finite binary-axis minor and actual first-slot-difference checks; no uniform source-rank claim.',
                  independent_check='The scalar H*kappa formula is compared with actual ordered binary kernels. Pole matrices are built directly from residue kernels and independently reconstruct those same actual differences at three ordinary points.',
                  scope='Only m=3,...,8 at the recorded economic fixture; no old source matrix O or full three-state system was constructed.',
                  limitations='These nonzero minors do not constitute the all-m Laurent induction or the full T2(N) surjectivity proof. Row-zero long-empty directions belong to that separate bridge.',
                  limits=dict(seconds=28, maximum_rss_bytes=95*1024**2),
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
