#!/usr/bin/env python3
"""Differentiate the actual paired residue matrix at a binary terminal time.

Fixed data: G=I+11^T, sector a=0, old times (1,8^s,8^(2s)) for
s=1,...,q-1, terminal time (1,epsilon,7), and q=2,3,4 modulo 1000003.
All arithmetic takes place in F_p[epsilon]/(epsilon^2). At terminal nodes
the cross product and its sum normalization are both differentiated.

For a regular kernel, the derivative is
 K'_ij=(A'_ij X_j+A_ij X'_j)/L_i-A_ij X_j L'_i/L_i^2.
At the observed pole, replace that kernel by e_d*(A_u[d,:] diag(X));
the moving row form has been cleared before either coefficient is read.
H uses [s]+all other blocks increasingly; J omits its external block and
uses the remaining blocks increasingly. Polynomial clearing checks both
coefficients independently, including J's external A_t(c,0) factor.

Exact row and column operations put B0 into diag(I_r,0) and carry B1
through the same operations. The lower-right derivative is the map from
ker(B0) to coker(B0). No scalar response M is used to construct these jets.
This is a prescribed finite diagnostic, not an all-length rank theorem.
"""

import argparse
import itertools
import json
from pathlib import Path
import signal
import time
import traceback

import source24_residue as residue
import source24_schur as schur
import source24_equal_weight_boundary as paired


P = paired.P
ZERO, ONE = (0, 0), (1, 0)


def constant(value):
    return value % P, 0


def add(x, y):
    return (x[0] + y[0]) % P, (x[1] + y[1]) % P


def neg(x):
    return -x[0] % P, -x[1] % P


def mul(x, y):
    return x[0] * y[0] % P, (x[0] * y[1] + x[1] * y[0]) % P


def inverse(x):
    assert x[0], 'A required dual denominator has zero constant coefficient.'
    value = pow(x[0], -1, P)
    return value, -x[1] * value * value % P


def divide(x, y):
    return mul(x, inverse(y))


def total(values):
    answer = ZERO
    for value in values:
        answer = add(answer, value)
    return answer


def product(values):
    answer = ONE
    for value in values:
        answer = mul(answer, value)
    return answer


def dot(left, right):
    return total(mul(x, y) for x, y in zip(left, right))


def cross(left, right):
    return [add(mul(left[i], right[j]), neg(mul(left[j], right[i])))
            for i, j in ((1, 2), (2, 0), (0, 1))]


def identity():
    return [[ONE if i == j else ZERO for j in range(3)] for i in range(3)]


def matrix_product(left, right):
    columns = list(zip(*right))
    return [[dot(row, column) for column in columns] for row in left]


def word_product(matrices, word):
    answer = identity()
    for t in word:
        answer = matrix_product(answer, matrices[t])
    return answer


def row_product(row, matrix):
    return [dot(row, column) for column in zip(*matrix)]


def scale(value, vector):
    return [mul(value, x) for x in vector]


def numeric_identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def induced_jet(B0, B1):
    """Carry exact constant row/column transformations to the derivative."""
    n = len(B0)
    A, derivative = [row[:] for row in B0], [row[:] for row in B1]
    left, right, operations = numeric_identity(n), numeric_identity(n), []
    rank = 0
    for k in range(n):
        pivot = next(((i, j) for i in range(k, n) for j in range(k, n) if A[i][j]), None)
        if pivot is None:
            break
        i, j = pivot
        operations.append(dict(step=k, pivot_row=i, pivot_column=j, pivot_value=A[i][j]))
        for matrix in (A, derivative, left):
            matrix[k], matrix[i] = matrix[i], matrix[k]
        for matrix in (A, derivative, right):
            for row in matrix:
                row[k], row[j] = row[j], row[k]
        multiplier = pow(A[k][k], -1, P)
        for matrix in (A, derivative, left):
            matrix[k] = [multiplier * value % P for value in matrix[k]]
        for i in range(n):
            factor = A[i][k]
            if i != k and factor:
                for matrix in (A, derivative, left):
                    matrix[i] = [(x - factor * y) % P for x, y in zip(matrix[i], matrix[k])]
        for j in range(n):
            factor = A[k][j]
            if j != k and factor:
                for matrix in (A, derivative, right):
                    for row in matrix:
                        row[j] = (row[j] - factor * row[k]) % P
        rank += 1
    assert A == [[int(i == j and i < rank) for j in range(n)] for i in range(n)]
    assert schur.matrix_product(schur.matrix_product(left, B0), right) == A
    assert schur.matrix_product(schur.matrix_product(left, B1), right) == derivative
    B0_certificate = residue.modular_rank(B0, P)
    assert B0_certificate['rank'] == rank
    left_certificate, right_certificate = residue.modular_rank(left, P), residue.modular_rank(right, P)
    assert left_certificate['rank'] == right_certificate['rank'] == n
    nullity = n - rank
    kernel = [row[rank:] for row in right]
    cokernel = left[rank:]
    induced = [row[rank:] for row in derivative[rank:]]
    if nullity:
        assert schur.matrix_product(B0, kernel) == [[0] * nullity for _ in range(n)]
        assert schur.matrix_product(cokernel, B0) == [[0] * n for _ in range(nullity)]
        assert schur.matrix_product(schur.matrix_product(cokernel, B1), kernel) == induced
        induced_certificate = residue.modular_rank(induced, P)
    else:
        induced_certificate = dict(rank=0, full_rank=True, determinant_mod_prime=1,
                                   empty_determinant_convention=True)
    det_transform = (left_certificate['determinant_mod_prime'] *
                     right_certificate['determinant_mod_prime']) % P
    determinant_coefficient = induced_certificate['determinant_mod_prime'] * pow(det_transform, -1, P) % P
    return dict(constant_rank=rank, constant_certificate=B0_certificate, nullity=nullity,
                left_transformation=left, right_transformation=right,
                left_certificate=left_certificate, right_certificate=right_certificate,
                elimination_pivots=operations, transformed_constant=A, transformed_derivative=derivative,
                right_kernel_basis=kernel, left_cokernel_basis=cokernel,
                induced_derivative_matrix=induced, induced_derivative_certificate=induced_certificate,
                transformation_identities_verified=True,
                kernel_and_cokernel_identities_verified=True,
                determinant_leading_order=(nullity if determinant_coefficient else None),
                coefficient_at_order_nullity=determinant_coefficient,
                determinant_convention='If the induced derivative is invertible, det(B(epsilon)) has exact order nullity; coefficient=det(induced)/(det(left)*det(right)).')


def formal_geometry(tables):
    """Check nonvanishing through first order for the complete arrangement."""
    lines = [(t, a) for t in range(len(tables)) for a in range(3)]
    checks = dict(all_line_coefficients_nonzero_through_first_order=True,
                  all_pair_coordinates_nonzero_through_first_order=True,
                  every_third_line_determinant_nonzero_through_first_order=True,
                  coordinate_edge_incidence_separated_through_first_order=True)
    failures, pair_count, triple_count, edge_count = [], 0, 0, 0
    for t, a in lines:
        for j, value in enumerate(tables[t][a]):
            if value == ZERO:
                checks['all_line_coefficients_nonzero_through_first_order'] = False
                failures.append(dict(kind='coefficient', line=[t, a], coordinate=j))
    for first, second in itertools.combinations(lines, 2):
        X = cross(tables[first[0]][first[1]], tables[second[0]][second[1]])
        pair_count += 1
        if not all(value != ZERO for value in X):
            checks['all_pair_coordinates_nonzero_through_first_order'] = False
            failures.append(dict(kind='pair_coordinate', lines=[first, second], point=X))
    for first, second, third in itertools.combinations(lines, 3):
        determinant = dot(cross(tables[first[0]][first[1]], tables[second[0]][second[1]]),
                          tables[third[0]][third[1]])
        triple_count += 1
        if determinant == ZERO:
            checks['every_third_line_determinant_nonzero_through_first_order'] = False
            failures.append(dict(kind='third_line', lines=[first, second, third]))
    for line in lines:
        for coordinate in range(3):
            X = cross(tables[line[0]][line[1]], [ONE if j == coordinate else ZERO for j in range(3)])
            for other in lines:
                if other != line:
                    edge_count += 1
                    if dot(tables[other[0]][other[1]], X) == ZERO:
                        checks['coordinate_edge_incidence_separated_through_first_order'] = False
                        failures.append(dict(kind='edge_incidence', line=line, edge=coordinate, other=other))
    return dict(checks=checks, all_passed=all(checks.values()), failures=failures,
                pair_intersections_checked=pair_count, triple_determinants_checked=triple_count,
                other_line_edge_incidence_checks=edge_count,
                interpretation='A nonzero constant or first coefficient certifies nonidentical vanishing as a function of epsilon. This does not assert complete general position at epsilon=0.')


def calculate(q):
    ordinary_tables, fixture = paired.fixture(q - 1)
    tables = [[[constant(value) for value in row] for row in table] for table in ordinary_tables]
    terminal_time = [ONE, (0, 1), (7, 0)]
    tables.append([[mul(constant(paired.G[i][j]), terminal_time[j]) for j in range(3)] for i in range(3)])
    normal = tables[0][0]
    labels = [['H', s, b] for s in range(1, q + 1) for b in range(3)]
    labels += [['J', t, c] for t in range(1, q + 1) for c in range(3)]
    B0, B1, row_labels, nodes = [], [], [], []
    component_checks = 0
    for u in range(1, q + 1):
        for d in range(3):
            raw = cross(normal, tables[u][d])
            normalization = inverse(total(raw))
            X = scale(normalization, raw)
            assert total(X) == ONE and all(value[0] for value in X)
            assert (any(value[1] for value in X) if u == q else all(value[1] == 0 for value in X))
            forms = [[dot(row, X) for row in table] for table in tables]
            zero_constants = [(t, c) for t in range(q + 1) for c in range(3) if not forms[t][c][0]]
            assert zero_constants == [(0, 0), (u, d)], ('Paired-node geometry failed.', q, u, d, zero_constants)
            assert forms[0][0] == forms[u][d] == ZERO
            v = [mul(normal[j], X[j]) for j in range(3)]
            w = [mul(tables[u][d][j], X[j]) for j in range(3)]
            assert total(v) == total(w) == ZERO
            residue.coordinates([value[0] for value in v], [value[0] for value in v],
                                [value[0] for value in w], P)
            matrices = {}
            for t in range(1, q + 1):
                matrices[t] = ([[value if i == d else ZERO for value in w] for i in range(3)]
                               if t == u else
                               [[divide(mul(tables[t][i][j], X[j]), forms[t][i]) for j in range(3)]
                                for i in range(3)])
                if t != u:
                    assert all(total(row) == ONE for row in matrices[t])
            cleared = {t: [[mul(mul(tables[t][i][j], X[j]),
                                product(forms[t][h] for h in range(3) if h != i))
                            for j in range(3)] for i in range(3)] for t in range(1, q + 1)}
            remaining = product(forms[t][c] for t in range(1, q + 1) for c in range(3)
                                if (t, c) != (u, d))
            inverse_remaining = inverse(remaining)
            heads, incoming, cleared_heads, cleared_incoming = {}, {}, {}, {}
            for t in range(1, q + 1):
                head_word = [t] + [s for s in range(1, q + 1) if s != t]
                incoming_word = [s for s in range(1, q + 1) if s != t]
                heads[t], incoming[t] = word_product(matrices, head_word), word_product(matrices, incoming_word)
                cleared_heads[t] = word_product(cleared, head_word)
                cleared_incoming[t] = word_product(cleared, incoming_word)
            vectors = []
            for kind, t, c in labels:
                if kind == 'H':
                    actual = scale(neg(X[c]), heads[t][c])
                    control = scale(mul(neg(X[c]), inverse_remaining), cleared_heads[t][c])
                else:
                    if t == u and c != d:
                        actual = [ZERO] * 3
                    else:
                        denominator = ONE if t == u else forms[t][c]
                        factor = neg(divide(mul(tables[t][c][0], X[c]), denominator))
                        actual = scale(factor, row_product(v, incoming[t]))
                    cleared_factor = neg(product([tables[t][c][0], X[c], inverse_remaining] +
                                                 [forms[t][h] for h in range(3) if h != c]))
                    control = scale(cleared_factor, row_product(v, cleared_incoming[t]))
                assert actual == control, ('Dual polynomial-clearing mismatch.', q, u, d, kind, t, c)
                assert total(actual) == ZERO
                vectors.append(actual)
                component_checks += 6
            for coordinate in (0, 1):
                B0.append([vector[coordinate][0] for vector in vectors])
                B1.append([vector[coordinate][1] for vector in vectors])
                row_labels.append([u, d, coordinate])
            nodes.append(dict(block=u, state=d, point_constant=[value[0] for value in X],
                              point_derivative=[value[1] for value in X], raw_cross=raw,
                              normalization=normalization, row_forms=forms,
                              nonzero_remaining_denominator=remaining,
                              zero_constant_row_forms=zero_constants))
    assert len(B0) == len(B1) == 6 * q
    jet = induced_jet(B0, B1)
    expected_rank, expected_jet = 3 * q + 6, 3 * q - 6
    terminal_determinant = dot(tables[q][0], cross(tables[q][1], tables[q][2]))
    assert terminal_determinant == (0, 28)
    geometry = formal_geometry(tables)
    return dict(q=q, sector=0, prime=P, fixture=fixture,
                terminal_time_dual=terminal_time, terminal_table_dual=tables[q],
                terminal_table_determinant_dual=terminal_determinant,
                terminal_constant_rank=residue.modular_rank([[value[0] for value in row] for row in tables[q]], P)['rank'],
                complete_old_geometry=paired.geometry_controls(ordinary_tables), formal_deformation_geometry=geometry,
                degeneration='At epsilon=0 the terminal rows meet at (0,1,0), off the fixed new-state line. Every evaluated paired node retains nonzero coordinates and all other required row forms are units.',
                row_labels=row_labels, column_labels=labels, node_records=nodes,
                residue_convention='Res_L_ud(Y) at the moving point cross(g,A_u[d,:])/sum(cross); components0,1. B1 is the coefficient of epsilon, including both node and normalization derivatives.',
                B0=B0, B1=B1, B0_sha256=residue.matrix_hash(B0), B1_sha256=residue.matrix_hash(B1),
                polynomial_clearing_coefficient_checks=component_checks,
                exact_first_jet=jet, expected_constant_rank=expected_rank, expected_induced_rank=expected_jet,
                expected_ranks_verified=(jet['constant_rank'] == expected_rank and
                                         jet['induced_derivative_certificate']['rank'] == expected_jet),
                construction_independent_of_scalar_response_M=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or paired.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='Direct dual-number derivatives of actual paired residue matrices for one prescribed fixture, q=2,3,4; no scalar-response construction, search, or all-length claim.',
                  prime=P, resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for q in (2, 3, 4):
            case = calculate(q)
            result['cases'].append(case)
            jet = case['exact_first_jet']
            print(json.dumps(dict(q=q, constant_rank=jet['constant_rank'],
                                  induced_rank=jet['induced_derivative_certificate']['rank'],
                                  determinant_order=jet['determinant_leading_order'],
                                  leading_coefficient=jet['coefficient_at_order_nullity'],
                                  expected_ranks_verified=case['expected_ranks_verified'],
                                  formal_deformation_geometry_passed=case['formal_deformation_geometry']['all_passed'])), flush=True)
        result['status'] = ('PASS: expected constant and induced first-jet ranks hold in all three prescribed cases.'
                            if all(case['expected_ranks_verified'] for case in result['cases']) else
                            'Completed diagnostic: an expected rank fails at this fixture; no replacement fixture used.')
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete prescribed diagnostic; no replacement fixture used.',
                      error=str(error), traceback=traceback.format_exc())
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = paired.maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active during writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
