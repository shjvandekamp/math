#!/usr/bin/env python3
"""Actual E/F columns and first u-jets when the last two times coincide.

Old factors are (8**t, 8**(2*t)), t=1,...,q; the new factors are
(u_q+du*epsilon,v_q+dv*epsilon). The default checks q=4 with (du,dv)=(1,0).
The explicit --generic-followup preserves that result and checks q=4 with
(du,dv)=(u_q,2*v_q), then q=5 only if q=4 is full and the budget permits.
Copied old F columns still contain
the full terminal K_new and are differentiated as such. The specified
vanishing differences are differentiated before taking the evaluation rank.

This is a finite-field lower-bound certificate, not an all-length theorem.
A deficient sampled first jet is not a function-rank upper bound.
"""

import argparse
import json
from pathlib import Path
import resource
import signal
import sys
import time

import absorbing_firstjet as dual
import normalized_sparse_source24 as sparse
import source24_residue as residue


P = residue.PRIME
G = ((1, 1, 1), (1, 30, 10), (1, 3, 2))
POINT_SEED = 240015


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def labels(m):
    return [('E', t, a) for t in range(m) for a in range(3)] + [
        ('F', t, s, a, b) for t in range(m) for s in range(m) if t != s
        for a in range(3) for b in range(3)]


def order(m, t, s):
    return [s] + [j for j in range(m) if j not in (t, s)]


def actual_values(tables, X):
    """Independent existing ordinary evaluator, undoing its F normalization."""
    values = sparse.evaluated_columns(tables, X)
    assert values is not None
    for label, row in zip(labels(len(tables)), values):
        if label[0] == 'F':
            _, t, _, a, b = label
            row[:] = [tables[t][a][b] * value % P for value in row]
    return values


def values_and_derivatives(tables, X, du=1, dv=0):
    """Dual-number evaluation of every actual full-length E/F column."""
    m, last = len(tables), len(tables) - 1
    kernels = []
    for t, table in enumerate(tables):
        kernel = []
        for a in range(3):
            numerators = [(table[a][i] * X[i] % P,
                           G[a][i] * X[i] * (0, du, dv)[i] % P if t == last else 0)
                          for i in range(3)]
            denominator = tuple(sum(z[k] for z in numerators) % P for k in (0, 1))
            inverse = dual.inverse(denominator)
            row = [dual.mul(z, inverse) for z in numerators]
            assert tuple(sum(z[k] for z in row) % P for k in (0, 1)) == dual.ONE
            kernel.append(row)
        kernels.append(kernel)
    products = {}
    for t in range(m):
        for s in range(m):
            if t != s:
                product = dual.identity()
                for j in order(m, t, s):
                    product = dual.mmul(product, kernels[j])
                products[t, s] = product
    values = []
    for label in labels(m):
        if label[0] == 'E':
            _, t, a = label
            row = [dual.scale(X[a], dual.sub(dual.ONE if c == a else dual.ZERO,
                                            kernels[t][a][c])) for c in range(3)]
        else:
            _, t, s, a, b = label
            prefactor = dual.scale(X[a], kernels[t][a][b])
            row = [dual.mul(prefactor, dual.sub(dual.ONE if c == b else dual.ZERO,
                                               products[t, s][b][c])) for c in range(3)]
        assert all(sum(z[k] for z in row) % P == 0 for k in (0, 1))
        values.append(row)
    return values, kernels


def analytic_derivative_control(tables, X, values, kernels, du=1, dv=0):
    """Ordinary product rule with one explicit K' insertion; no dual products."""
    m, new = len(tables), len(tables) - 1
    K = [[[z[0] for z in row] for row in kernel] for kernel in kernels]
    derivative = []
    for a in range(3):
        den = residue.dot(tables[new][a], X, P)
        numerator_prime = [G[a][c] * X[c] * (0, du, dv)[c] % P for c in range(3)]
        den_prime, inverse = sum(numerator_prime) % P, pow(den, -1, P)
        derivative.append([(numerator_prime[c] - K[new][a][c] * den_prime) * inverse % P
                           for c in range(3)])
    assert derivative == [[z[1] for z in row] for row in kernels[new]]
    controls = 0
    for label, value in zip(labels(m), values):
        if label[0] == 'E':
            _, t, a = label
            expected = [-X[a] * derivative[a][c] % P if t == new else 0 for c in range(3)]
        else:
            _, t, s, a, b = label
            word = order(m, t, s)
            product = residue.word_product(K, word, P)
            if new in word:
                position = word.index(new)
                before = residue.word_product(K, word[:position], P)
                after = residue.word_product(K, word[position + 1:], P)
                product_prime = residue.matmul(residue.matmul(before, derivative, P), after, P)
            else:
                product_prime = [[0] * 3 for _ in range(3)]
            prefactor = X[a] * K[t][a][b] % P
            prefactor_prime = X[a] * derivative[a][b] % P if t == new else 0
            expected = [(prefactor_prime * (int(c == b) - product[b][c])
                         - prefactor * product_prime[b][c]) % P for c in range(3)]
        assert expected == [z[1] for z in value], ('Derivative control', label, X)
        controls += 3
    return controls


def copied_append_control(tables, X, values, kernels, lookup, q):
    """Check C=I+(R_old-I)K_new, including its complete derivative."""
    old_values = actual_values(tables[:q], X)
    Kold = [[[z[0] for z in row] for row in kernel] for kernel in kernels[:q]]
    Knew = [[z[0] for z in row] for row in kernels[q]]
    Kprime = [[z[1] for z in row] for row in kernels[q]]
    controls = 0
    for label, old in zip(labels(q), old_values):
        if label[0] == 'E':
            prefix = old
        else:
            _, t, _, a, b = label
            prefix = [X[a] * Kold[t][a][b] % P if c == b else 0 for c in range(3)]
        completed = [(old[c] - prefix[c]) % P for c in range(3)]
        leading = residue.matmul([completed], Knew, P)[0]
        expected = [(prefix[c] + leading[c]) % P for c in range(3)]
        expected_prime = residue.matmul([completed], Kprime, P)[0]
        actual = values[lookup[label]]
        assert expected == [z[0] for z in actual]
        assert expected_prime == [z[1] for z in actual]
        controls += 6
    return controls


def transformed_columns(q, source_labels):
    lookup = {label: i for i, label in enumerate(source_labels)}
    new, last = q, q - 1
    base_labels = labels(q) + [('F', last, new, a, b) for a in range(3) for b in range(3)]
    base = [dict(kind='base', label=label, terms=[[lookup[label], 1]]) for label in base_labels]
    differences = []

    def difference(kind, left, right):
        differences.append(dict(kind=kind, left=left, right=right,
                                terms=[[lookup[left], 1], [lookup[right], -1]]))

    for a in range(3):
        difference('new_E_minus_last_old_E', ('E', new, a), ('E', last, a))
    for s in range(last):
        for a in range(3):
            for b in range(3):
                difference('shared_new_minus_copied_last_shared',
                           ('F', new, s, a, b), ('F', last, s, a, b))
    for t in range(last):
        for a in range(3):
            for b in range(3):
                difference('first_new_minus_copied_last_first',
                           ('F', t, new, a, b), ('F', t, last, a, b))
    for a in range(3):
        for b in range(3):
            difference('shared_new_last_minus_first_new_last',
                       ('F', new, last, a, b), ('F', last, new, a, b))
    primary = [item['terms'][0][0] for item in base + differences]
    assert sorted(primary) == list(range(len(source_labels)))
    base_indices = set(primary[:len(base)])
    assert all(item['terms'][1][0] in base_indices for item in differences)
    assert len(base) == 9 * q * (q - 1) + 3 * q + 9
    assert len(differences) == 18 * q - 6
    return base, differences, lookup


def ordinary_points(tables, count):
    state, points, seen, skipped = POINT_SEED, [], set(), 0
    while len(points) < count:
        state = (1664525 * state + 1013904223) % (2 ** 32)
        x = 2 + state % 10007
        state = (1664525 * state + 1013904223) % (2 ** 32)
        y = 2 + state % 10007
        X = (1, x, y)
        if X in seen or any(residue.dot(row, X, P) == 0 for table in tables for row in table):
            skipped += 1
            continue
        seen.add(X)
        points.append(X)
    return points, skipped


def certificate(matrix):
    return dict(shape=[len(matrix), len(matrix[0])], sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def local_basepoint_motion(table, du, dv):
    """Projective velocities of the three matching and three same-block points."""
    prime = [[0, G[a][1] * du % P, G[a][2] * dv % P] for a in range(3)]
    points = []
    for a in range(3):
        axis = [int(i == a) for i in range(3)]
        X = residue.cross(table[a], axis, P)
        velocity = residue.cross(prime[a], axis, P)
        points.append(dict(kind='matching', state=a, point=X, derivative=velocity,
                           moves_projectively=any(residue.cross(X, velocity, P))))
    for a in range(3):
        for b in range(a + 1, 3):
            X = residue.cross(table[a], table[b], P)
            left, right = residue.cross(prime[a], table[b], P), residue.cross(table[a], prime[b], P)
            velocity = [(x + y) % P for x, y in zip(left, right)]
            points.append(dict(kind='same_block_pair', states=[a, b], point=X, derivative=velocity,
                               moves_projectively=any(residue.cross(X, velocity, P))))
    return points


def calculate(q=4, direction='u_only'):
    started = time.monotonic()
    times = sparse.factors(q, 'economic')
    times.append(times[-1])
    assert direction in ('u_only', 'relative_1_2')
    du, dv = (1, 0) if direction == 'u_only' else (times[-1][0], 2 * times[-1][1])
    tables = sparse.coefficient_tables(G, times)
    motion = local_basepoint_motion(tables[-1], du, dv)
    if direction == 'relative_1_2':
        assert all(item['moves_projectively'] for item in motion)
    source_labels = labels(q + 1)
    base, differences, lookup = transformed_columns(q, source_labels)
    count = len(source_labels)
    points, skipped = ordinary_points(tables, (count + 1) // 2 + 12)
    B0, B1, D1 = [], [], []
    ordinary_controls = derivative_controls = copied_controls = vanishing_controls = 0
    for point_id, X in enumerate(points):
        values, kernels = values_and_derivatives(tables, X, du, dv)
        if point_id < 3:
            ordinary = actual_values(tables, X)
            assert ordinary == [[z[0] for z in row] for row in values]
            ordinary_controls += 3 * count
            derivative_controls += analytic_derivative_control(tables, X, values, kernels, du, dv)
            copied_controls += copied_append_control(tables, X, values, kernels, lookup, q)
        base_values = [values[item['terms'][0][0]] for item in base]
        difference_values = []
        for item in differences:
            left, right = [values[index] for index, _ in item['terms']]
            row = [dual.sub(a, b) for a, b in zip(left, right)]
            assert all(value[0] == 0 for value in row), ('Collision identity', item, X, row)
            difference_values.append(row)
            vanishing_controls += 3
        for component in (0, 1):
            B0.append([row[component][0] for row in base_values])
            B1.append([row[component][1] for row in base_values])
            D1.append([row[component][1] for row in difference_values])
    copied_count = len(labels(q))
    copied_certificate = certificate([row[:copied_count] for row in B0])
    base_certificate = certificate(B0)
    # Independence of the sampled B0 proves functional independence of B.
    # The prescribed collision differences then span the true leading kernel.
    # A deficient sampled B0 would not justify differentiating its sampled kernel.
    assert base_certificate['rank_certificate']['rank'] == len(base), (
        'Unresolved: sampled base is deficient; no functional-kernel claim is made.')
    first_jet = [left + right for left, right in zip(B0, D1)]
    first_jet_certificate = certificate(first_jet)
    base_kernel = None
    full_kernel_certificate = first_jet_certificate
    r0 = base_certificate['rank_certificate']['rank']
    r1 = full_kernel_certificate['rank_certificate']['rank']
    result = dict(q=q, m=q + 1, prime=P, G=G, time_factors_at_collision=times,
                  case_label=f'q{q}_{direction}',
                  direction=dict(new_u_derivative=du, new_v_derivative=dv, old_time_derivatives=0,
                                 relative_u_derivative=du * pow(times[-1][0], -1, P) % P,
                                 relative_v_derivative=dv * pow(times[-1][1], -1, P) % P),
                  block_numbering='Zero based; old final block q-1, new block q.',
                  source_column_labels=source_labels, base_columns=base,
                  vanishing_difference_columns=differences,
                  transformed_coefficient_basis_unitriangular_after_permutation=True,
                  point_seed=POINT_SEED, effect_points=points, point_count=len(points),
                  skipped_points=skipped, all_evaluation_denominators_nonzero=True,
                  old_last_and_new_tables_identical=tables[-1] == tables[-2],
                  local_basepoint_motion=motion,
                  all_six_local_basepoints_move=all(item['moves_projectively'] for item in motion),
                  row_labels='Row 2j is component 0 at effect_points[j]; row 2j+1 is component 1.',
                  copied_old_leading_certificate=copied_certificate,
                  base_leading_certificate=base_certificate,
                  specified_first_jet_certificate=first_jet_certificate,
                  full_coefficient_kernel_first_jet_certificate=full_kernel_certificate,
                  base_additional_kernel=base_kernel,
                  leading_rank=r0, induced_first_jet_rank=r1-r0,
                  certified_generic_rank_lower_bound=r1, target_column_count=count,
                  base_value_matrix=B0, base_derivative_matrix=B1,
                  vanished_difference_derivative_matrix=D1,
                  vanished_difference_constant_matrix_is_zero=True,
                  controls=dict(collision_identity_component_checks=vanishing_controls,
                                ordinary_existing_evaluator_component_checks=ordinary_controls,
                                explicit_kernel_and_product_derivative_component_checks=derivative_controls,
                                full_copied_old_append_component_checks=copied_controls),
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q, direction=direction,
                          copied_old_rank=copied_certificate['rank_certificate']['rank'],
                          base_rank=r0, first_jet_rank=r1, target=count,
                          induced_gain=r1-r0)), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--generic-followup', action='store_true')
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    cases, limitation, previous_resources = [], None, []
    optional_q5 = 'Not requested by the default u-only run.'
    try:
        if args.generic_followup:
            previous = json.loads(args.output.read_text())
            cases = previous['cases']
            assert len(cases) == 1 and cases[0]['q'] == 4
            assert cases[0]['direction']['new_u_derivative'] == 1
            assert cases[0]['direction']['new_v_derivative'] == 0
            previous_resources = [dict(elapsed_seconds=previous['elapsed_seconds'],
                                       maximum_rss_bytes=previous['maximum_rss_bytes'],
                                       scope='Prior u-only run, measured before JSON serialization.')]
            cases.append(calculate(4, 'relative_1_2'))
            if cases[-1]['certified_generic_rank_lower_bound'] == cases[-1]['target_column_count']:
                if time.monotonic() - started < 18:
                    cases.append(calculate(5, 'relative_1_2'))
                    optional_q5 = 'Executed once after the q=4 relative-(1,2) case was full.'
                else:
                    optional_q5 = 'Not attempted because the remaining time budget was insufficient.'
            else:
                optional_q5 = 'Not attempted because the prescribed q=4 first jet was deficient.'
        else:
            cases.append(calculate(4))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite actual-source last-time collision and full coefficient-kernel first jet.',
                  scope='Prescribed q=4 u-only baseline, followed only on request by the relative-(1,2) flow; no parameter scan.',
                  source_formula='E_ta=Xa(ea-Kt(a,:)); F_tsab=Xa Kt(a,b) eb(I-P_s^omit_t).',
                  rank_interpretation='Rank of leading columns plus derivatives on their actual coefficient kernel, never stacked raw jets. A deficient sampled first jet is not a function-rank upper bound or a source dependence.',
                  optional_q5=optional_q5,
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2),
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=maximum_rss_bytes(),
                  resource_measurement_scope='This guarded calculation, before JSON serialization.',
                  previous_run_resources=previous_resources,
                  bounded_limitation=limitation, cases=cases)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    if limitation:
        raise SystemExit(2)


if __name__ == '__main__':
    main()
