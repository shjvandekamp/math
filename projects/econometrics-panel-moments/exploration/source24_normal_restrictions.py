#!/usr/bin/env python3
"""Reconstruct four finite normal-restriction bases from actual source words.

All arithmetic is over F_1009.  The scalar binary recurrence is p -> a_t+d_t*p.
Y_t starts at c_t, H_ts starts at c_s and omits t, then divides by r_t;
Z_ts=r_t*H_ts/(x+tau*z_t).  Delta is the difference of the two binary affine
intercepts for the actual move-s-first and ascending words omitting t.

The augmented H column has prefix coefficient e_t in the independent basis
pi_t=1/(x+rho*z_t).  These are coefficient rows, not evaluation rows.

Independent controls use three-state transition products over F_1009[e]/(e^3)
at X=(e,x,1), G=[[1,1,1],[1,3,6],[1,5,15]], u_t=2^t, v_t=u_t*z_t.
J_j denotes the coefficient of e^j, not the j-th derivative.  Actual moments
are F_tsab=X_a*K_t(a,b)*e_b*(I-P_s^omit_t) and long-empty X_a*e_a*(I-P_t).
Only the four requested finite matrices are tested; no growing-m scan or
uniform rank conclusion is made.  No external code is downloaded or executed.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_residue as residue
from source24_odd_incoming import maximum_rss_bytes


P = 1009
RHO, SIGMA, TAU = 1, 2, 3
Z = (1, 5, 7, 11, 13)
G = ((1, 1, 1), (1, 3, 6), (1, 5, 15))
ZERO, ONE = (0, 0, 0), (1, 0, 0)
DENOMINATORS = {}


def inverse(value, kind):
    value %= P
    assert value, ('Nonunit denominator', kind)
    DENOMINATORS.setdefault(kind, set()).add(value)
    return pow(value, -1, P)


def add(a, b):
    return tuple((x+y) % P for x, y in zip(a, b))


def subtract(a, b):
    return tuple((x-y) % P for x, y in zip(a, b))


def scale(c, a):
    return tuple(c*x % P for x in a)


def multiply(a, b):
    return tuple(sum(a[j]*b[k-j] for j in range(k+1)) % P for k in range(3))


def reciprocal(a):
    first = inverse(a[0], 'actual_Taylor_denominator')
    values = [first]
    for k in range(1, 3):
        values.append(-first*sum(a[j]*values[k-j] for j in range(1, k+1)) % P)
    result = tuple(values)
    assert multiply(a, result) == ONE
    return result


def series_product(a, b):
    result = []
    for row in a:
        out = []
        for col in zip(*b):
            value = ZERO
            for x, y in zip(row, col):
                value = add(value, multiply(x, y))
            out.append(value)
        result.append(out)
    return result


def word(m, s, omit=None):
    return [s]+[t for t in range(1, m+1) if t not in (s, omit)]


def scalar_data(m, x):
    a, d, c, r = {}, {}, {}, {}
    for t, z in enumerate(Z[:m], start=1):
        r[t] = (x+RHO*z) % P
        a[t] = SIGMA*z*inverse(x+SIGMA*z, 'x_plus_sigma_z') % P
        d[t] = x*(TAU-SIGMA)*z*inverse((x+SIGMA*z)*(x+TAU*z), 'binary_determinant_denominator') % P
        c[t] = RHO*z*inverse(r[t], 'x_plus_rho_z') % P

    def follow(initial, order):
        for t in order:
            initial = (a[t]+d[t]*initial) % P
        return initial

    Y = {t: follow(c[t], [s for s in range(1, m+1) if s != t]) for t in range(1, m+1)}
    H, Zvalue, delta = {}, {}, {}
    for t in range(1, m+1):
        baseline = min(u for u in range(1, m+1) if u != t)
        for s in range(1, m+1):
            if t == s:
                continue
            H[t, s] = follow(c[s], [u for u in range(1, m+1) if u not in (t, s)])*inverse(r[t], 'x_plus_rho_z') % P
            Zvalue[t, s] = r[t]*H[t, s]*inverse(x+TAU*Z[t-1], 'x_plus_tau_z') % P
            delta[t, s] = (follow(0, word(m, s, t))-follow(0, word(m, baseline, t))) % P
    return dict(Y=Y, H=H, Z=Zvalue, delta=delta, a=a, d=d, c=c)


def actual_controls(m, x, scalar):
    X = ((0, 1, 0), (x % P, 0, 0), ONE)
    tables, kernels = {}, {}
    for t in range(1, m+1):
        u, v = 2**t, 2**t*Z[t-1]
        tables[t] = [[row[0], row[1]*u, row[2]*v] for row in G]
        K = []
        for row in tables[t]:
            numerator = [scale(row[c], X[c]) for c in range(3)]
            denominator = ZERO
            for value in numerator:
                denominator = add(denominator, value)
            inv = reciprocal(denominator)
            K.append([multiply(value, inv) for value in numerator])
        assert all(add(add(row[0], row[1]), row[2]) == ONE for row in K)
        assert K[0][2][0] == scalar['c'][t]
        assert K[1][2][0] == scalar['a'][t]
        assert (K[2][2][0]-K[1][2][0]) % P == scalar['d'][t]
        kernels[t] = K
    cache = {(): [[ONE if i == j else ZERO for j in range(3)] for i in range(3)]}

    def product(order):
        key = tuple(order)
        if key not in cache:
            value = cache[()]
            for t in order:
                value = series_product(value, kernels[t])
            cache[key] = value
        return cache[key]

    def F(t, s, a, b):
        tail = subtract(ONE if b == 2 else ZERO, product(word(m, s, t))[b][2])
        return multiply(multiply(X[a], kernels[t][a][b]), tail)

    checks = dict(binary_row_entries=3*m, Y_first_coefficients=0,
                  F00_second_coefficients=0, F20_first_coefficients=0,
                  summed_difference_first_coefficients=0,
                  actual_omit_word_probabilities=0)
    for t in range(1, m+1):
        full = product(word(m, t))
        longempty = scale(-1, multiply(X[0], full[0][2]))
        assert longempty[0] == 0 and longempty[1] == -scalar['Y'][t] % P
        checks['Y_first_coefficients'] += 1
        baseline = min(u for u in range(1, m+1) if u != t)
        for s in range(1, m+1):
            if s == t:
                continue
            u = 2**t
            f00, f20 = F(t, s, 0, 0), F(t, s, 2, 0)
            assert f00[:2] == (0, 0)
            assert f00[2] == -scalar['H'][t, s]*inverse(u*G[0][1], 'source_scaling_u_G01') % P
            assert f20[0] == 0
            assert f20[1] == -scalar['Z'][t, s]*inverse(u*G[2][1], 'source_scaling_u_G21') % P
            difference = ZERO
            for b in range(3):
                difference = add(difference, subtract(F(t, s, 0, b), F(t, baseline, 0, b)))
            assert difference[0] == 0 and difference[1] == -scalar['delta'][t, s] % P
            assert product(word(m, s, t))[0][2][0] == (x+RHO*Z[t-1])*scalar['H'][t, s] % P
            checks['F00_second_coefficients'] += 1
            checks['F20_first_coefficients'] += 1
            checks['summed_difference_first_coefficients'] += 1
            checks['actual_omit_word_probabilities'] += 1
    return checks


def certificate(name, m, row_labels, column_labels, matrix, expected):
    assert len(matrix) == len(matrix[0]) == len(row_labels) == len(column_labels)
    result = residue.modular_rank(matrix, P)
    determinant = result['determinant_mod_prime']
    return dict(name=name, m=m, row_labels=row_labels, column_labels=column_labels,
                matrix=matrix, matrix_sha256=residue.matrix_hash(matrix),
                rank_certificate=result, claimed_determinant=expected,
                determinant_mod_prime=determinant, claimed_determinant_matches=determinant == expected)


def calculate():
    assert residue.modular_rank(G, P)['determinant_mod_prime'] == 8
    assert len({rate*z % P for rate in (RHO, SIGMA, TAU) for z in Z}) == 15
    values, checks = {}, {}
    for m, last_x in ((4, 12), (5, 13)):
        totals = {}
        for x in range(1, last_x+1):
            values[m, x] = scalar_data(m, x)
            current = actual_controls(m, x, values[m, x])
            for key, count in current.items():
                totals[key] = totals.get(key, 0)+count
        checks[m] = totals
    pairs4 = [(t, s) for t in range(1, 5) for s in range(1, 5) if t != s][:11]
    H4 = [[values[4, x]['H'][pair] for pair in pairs4] for x in range(1, 12)]
    first = certificate('H_m4', 4, [dict(kind='evaluation', x=x) for x in range(1, 12)],
                        [dict(kind='H', t=t, s=s) for t, s in pairs4], H4, 290)

    pairs5 = [(t, s) for t in range(1, 6) for s in range(1, 6) if t != s][:18]
    augmented = [[int(t == i) for t, s in pairs5] for i in range(1, 6)]
    augmented += [[values[5, x]['H'][pair] for pair in pairs5] for x in range(1, 14)]
    second = certificate('augmented_H_m5', 5,
                         [dict(kind='pi_coefficient', t=t) for t in range(1, 6)]
                         +[dict(kind='evaluation', x=x) for x in range(1, 14)],
                         [dict(kind='H_with_pi_t', t=t, s=s) for t, s in pairs5], augmented, 487)

    delta_pairs = [(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 2), (3, 4), (4, 5)]
    delta_matrix = [[values[5, x]['delta'][pair] for pair in delta_pairs] for x in range(1, 10)]
    third = certificate('delta_m5', 5, [dict(kind='evaluation', x=x) for x in range(1, 10)],
                        [dict(kind='delta', t=t, s=s) for t, s in delta_pairs], delta_matrix, 730)

    first_normal_columns = [('Y', t, None) for t in range(1, 5)]
    first_normal_columns += [('delta', t, s) for t, s in ((1, 3), (1, 4), (2, 3), (2, 4), (3, 2), (3, 4))]
    first_normal_columns += [('Z', 1, 2), ('Z', 1, 3)]
    first_normal = [[values[4, x][kind][t if kind == 'Y' else (t, s)]
                     for kind, t, s in first_normal_columns] for x in range(1, 13)]
    fourth = certificate('first_normal_m4', 4, [dict(kind='evaluation', x=x) for x in range(1, 13)],
                         [dict(kind=kind, t=t, s=s) for kind, t, s in first_normal_columns], first_normal, 379)
    return dict(prime=P, rho=RHO, sigma=SIGMA, tau=TAU, z=Z, compatible_G=G,
                compatible_G_determinant=8,
                actual_times='u_t=2^t, v_t=u_t*z_t, with one-based t.',
                normal_chart='X=(epsilon,x,1); J_j is the ordinary Taylor coefficient [epsilon^j].',
                prefix_basis='pi_t=1/(x+rho*z_t); an augmented H_(t,s) column has coefficient e_t, with no extra sign or normalization.',
                actual_source_control_counts=checks,
                source_scalings=dict(F00_J2='-H_ts/(u_t*G[0][1])',
                                     longempty0_J1='-Y_t', F20_J1='-Z_ts/(u_t*G[2][1])',
                                     summed_F0b_difference_J1='-delta_ts'),
                all_denominators_units=True,
                checked_denominator_values={kind: sorted(values) for kind, values in sorted(DENOMINATORS.items())},
                bases=[first, second, third, fourth])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, result, limitation = time.monotonic(), None, None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        result = calculate()
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    output = dict(status='Independent local reconstruction of four finite normal-restriction bases.',
                  scope='Only the four recorded matrices and actual-source Taylor identities at their evaluation points are checked. Formal rank implications and any uniform theorem are separate.',
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=maximum_rss_bytes(),
                  bounded_limitation=limitation, result=result)
    if args.output:
        args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(determinants=None if result is None else
                         {item['name']: item['determinant_mod_prime'] for item in result['bases']},
                         all_claims_match=None if result is None else
                         all(item['claimed_determinant_matches'] for item in result['bases']),
                         elapsed_seconds=output['elapsed_seconds'],
                         maximum_rss_bytes=output['maximum_rss_bytes'], bounded_limitation=limitation)), flush=True)


if __name__ == '__main__':
    main()
