#!/usr/bin/env python3
"""Bounded exact probe of the Fourier cyclic transverse scalar blocks.

On L_(q,c)=0, with d=c+1 and e=c+2 modulo 3, the columns are
    f_(t,a) = Xa K_t(a,c) (v_c T_omit_t)_e,
where v_c=A_q(c,:)diag(X) and T uses every earlier block except t in
ascending order. These are the e-components of the actual completed-word
residues; the corresponding F-source residue has the opposite sign.

The Fourier table satisfies G diag(0,omega-1,omega^2-1)=(C-I)G for
C_(c,c+1)=1. Thus the cyclic orientation is checked against the actual
relative-time perturbation rather than assumed.

For m=2 there is an exact relation with coefficients
 +g_a A_1(a,e)/A_1(a,c), -g_a A_2(a,e)/A_2(a,c), g_a=A_q(c,a).
Both sums equal Xc/Xe times (v_c K_1)_e (v_c K_2)_e. The code also
cancels the nine denominator-labelled numerator pairs exactly, without
inferring this relation from sampled rank. Larger deficient sampled
ranks are reported only as lower bounds, not as function-rank ceilings.

Only one prescribed fixture is used, m=2,3,4,5 and all three c.
Standard library and existing local exact finite-field utilities only.
"""

import argparse
import json
from pathlib import Path
import resource
import signal
import sys
import time

import source24_residue as residue


P = 1000003
TERMINAL_FACTORS = (97, 193)


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def inverse(value):
    assert value % P, 'A required denominator is zero.'
    return pow(value % P, -1, P)


def fourier_fixture():
    assert (P - 1) % 3 == 0
    omega = next(pow(base, (P - 1) // 3, P) for base in range(2, 20)
                 if pow(base, (P - 1) // 3, P) != 1)
    assert pow(omega, 3, P) == 1 and (1 + omega + omega * omega) % P == 0
    G = [[pow(omega, a * b, P) for b in range(3)] for a in range(3)]
    C = [[int(b == (a + 1) % 3) for b in range(3)] for a in range(3)]
    H = [[(C[a][b] - int(a == b)) % P for b in range(3)] for a in range(3)]
    direction = [0, (omega - 1) % P, (omega * omega - 1) % P]
    left = [[G[a][b] * direction[b] % P for b in range(3)] for a in range(3)]
    assert left == residue.matmul(H, G, P)
    G_certificate = residue.modular_rank(G, P)
    assert G_certificate['rank'] == 3
    return omega, G, C, H, direction, G_certificate


def tables_for(m, G):
    times = [(2 ** t, 5 ** t) for t in range(1, m + 1)] + [TERMINAL_FACTORS]
    tables = [[[G[a][b] * (1, u, v)[b] % P for b in range(3)]
               for a in range(3)] for u, v in times]
    return times, tables


def line_points(tables, c, count):
    g = tables[-1][c]
    points, rejected, parameter = [], 0, 0
    while len(points) < count:
        parameter += 1
        assert parameter < 10000
        X = [-(g[1] + g[2] * parameter) * inverse(g[0]) % P, 1, parameter]
        assert residue.dot(g, X, P) == 0
        if not all(X) or any(residue.dot(row, X, P) == 0 for table in tables[:-1] for row in table):
            rejected += 1
            continue
        if any(residue.dot(tables[-1][a], X, P) == 0 for a in range(3) if a != c):
            rejected += 1
            continue
        points.append(X)
    return points, rejected


def evaluate(tables, c, X, direction):
    m, d, e = len(tables) - 1, (c + 1) % 3, (c + 2) % 3
    kernels = [residue.ordinary_kernel(tables, t, X, P) for t in range(m)]
    vc = [tables[-1][c][a] * X[a] % P for a in range(3)]
    vd = [tables[-1][d][a] * X[a] % P for a in range(3)]
    assert sum(vc) % P == 0
    assert [vc[a] * direction[a] % P for a in range(3)] == [
        (vd[a] - vc[a]) % P for a in range(3)]
    q_residue = [vc[:] if a == c else [0, 0, 0] for a in range(3)]
    values = []
    for t in range(m):
        word = [j for j in range(m) if j != t]
        tail = residue.word_product(kernels, word, P)
        row = residue.matmul([vc], tail, P)[0]
        assert sum(row) % P == 0
        # Independent actual full word with the singular kernel replaced by
        # L_(q,c) K_q: its only nonzero row is the actual v_c.
        completed = residue.word_product(kernels + [q_residue], [m] + word, P)
        for a in range(3):
            prefactor = X[a] * kernels[t][a][c] % P
            scalar = prefactor * row[e] % P
            assert scalar == prefactor * completed[c][e] % P
            values.append(scalar)
    return values, kernels


def two_block_relation(tables, c):
    """Termwise exact rational cancellation, not a sampled nullvector."""
    assert len(tables) == 3
    e, g = (c + 2) % 3, tables[-1][c]
    coefficients = [sign * g[a] * tables[t][a][e] * inverse(tables[t][a][c]) % P
                    for t, sign in ((0, 1), (1, -1)) for a in range(3)]
    assert all(coefficients)
    pairs = []
    for a in range(3):
        for h in range(3):
            # Both expanded terms have denominator L_(1,a) L_(2,h)
            # and numerator monomial Xa Xc Xh Xe.
            first = coefficients[a] * tables[0][a][c] * g[h] * tables[1][h][e] % P
            second = coefficients[3 + h] * tables[1][h][c] * g[a] * tables[0][a][e] % P
            assert (first + second) % P == 0
            powers = [sum(int(j == state) for j in (a, c, h, e)) for state in range(3)]
            pairs.append(dict(denominators=[[1, a], [2, h]], numerator_powers=powers,
                              first_coefficient=first, second_coefficient=second))
    return dict(coefficients=coefficients, cancelled_numerator_pairs=pairs,
                interpretation='Exact relation for these field tables; the displayed symbolic factor cancellation holds for arbitrary unit A_t(a,c).')


def calculate(m, c, G, direction):
    times, tables = tables_for(m, G)
    points, rejected = line_points(tables, c, 3 * m + 8)
    columns = [dict(t=t + 1, a=a, word=[j + 1 for j in range(m) if j != t])
               for t in range(m) for a in range(3)]
    matrix, relation = [], two_block_relation(tables, c) if m == 2 else None
    for X in points:
        row, kernels = evaluate(tables, c, X, direction)
        if relation is not None:
            coefficients, e = relation['coefficients'], (c + 2) % 3
            assert sum(a * b for a, b in zip(coefficients, row)) % P == 0
            vc = [tables[-1][c][a] * X[a] % P for a in range(3)]
            left = sum(coefficients[a] * row[a] for a in range(3)) % P
            right = (-sum(coefficients[3 + a] * row[3 + a] for a in range(3))) % P
            common = X[c] * inverse(X[e])
            for kernel in kernels:
                common = common * residue.matmul([vc], kernel, P)[0][e] % P
            assert left == right == common
        matrix.append(row)
    certificate = residue.modular_rank(matrix, P)
    if relation is not None:
        assert certificate['rank'] <= 5
    return dict(m=m, q=m + 1, c=c, d=(c + 1) % 3, e=(c + 2) % 3,
                time_factors=times, column_labels=columns, points=points,
                rejected_parameters=rejected, all_required_denominators_units=True,
                matrix=matrix, matrix_sha256=residue.matrix_hash(matrix),
                rank_certificate=certificate, target_columns=3 * m,
                actual_completed_word_residue_checks=len(points) * 3 * m,
                cyclic_relative_derivative_checks=len(points), two_block_relation=relation)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.05, 0.05)
    omega, G, C, H, direction, G_certificate = fourier_fixture()
    cases = [calculate(m, c, G, direction) for m in range(2, 6) for c in range(3)]
    result = dict(status='Finite Fourier cyclic transverse probe; no all-length rank claim.',
                  prime=P, omega=omega, G=G, G_certificate=G_certificate, C=C, H=H,
                  relative_direction=direction, terminal_factors=TERMINAL_FACTORS,
                  indexing='Times and words are one based; states are 0,1,2; q=m+1.',
                  scalar_formula='Xa K_t(a,c) [A_q(c,:)diag(X) prod_(j ascending, j!=t) K_j]_e on L_(q,c)=0.',
                  source_sign='Positive completed-word residue; actual F_t,q,a,c residue is its negative.',
                  rank_interpretation='Each nonzero minor is an exact lower bound for this finite-field specialization. Larger sampled deficiencies are not function-rank upper bounds. The m=2 upper bound follows separately from the exact displayed relation.',
                  fixture_scope='One prescribed Fourier G and one sequence of old factors (2^t,5^t); terminal factors (97,193); no parameter scan.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2),
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=maximum_rss_bytes(),
                  resource_measurement_scope='Calculation before JSON serialization; external time command records complete-process use.',
                  cases=cases)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(dict(ranks=[(c['m'], c['c'], c['rank_certificate']['rank'], c['target_columns'])
                                 for c in cases], elapsed_seconds=result['elapsed_seconds'],
                          maximum_rss_bytes=maximum_rss_bytes())))


if __name__ == '__main__':
    main()
