#!/usr/bin/env python3
"""Exact paired-boundary diagnostic in the fixed equal-weight family.

Use only r=(1,1,1), G=I+11^T, new time (1,1,1), and old times
b_t=(1,8^t,8^(2t)), t=1,...,q, for q=2,3,4 modulo 1000003.
This is the zero-based prescription b_t=(1,8^(t+1),8^(2t+2)).
No full source matrix is constructed and no parameter is searched.

On each new-state line v*1=0, the actual paired columns are
 H_sb=X_b e_b(I-K_s product_(u!=s, increasing) K_u),
 J_tc=-A_t(c,a) X_c/L_tc * v product_(u!=t, increasing) K_u.
At an old node L_ud=0, replace K_u by e_d (A_u(d,:) diag(X))
when it occurs in a product; handle J's external denominator separately.
An independent polynomial-clearing calculation checks all three vector
components before components 0 and 1 form the square residue matrix.

Nonzero determinants are finite certificates at this fixture. A singular
matrix at this fixture alone would not prove an identically singular family.
"""

import argparse
import itertools
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

import source24_residue as residue


P = 1000003
G = [[1 + int(i == j) for j in range(3)] for i in range(3)]


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def product(values):
    answer = 1
    for value in values:
        answer = answer * value % P
    return answer


def rowmul(row, matrix):
    return [sum(row[i] * matrix[i][j] for i in range(3)) % P
            for j in range(3)]


def scale(value, vector):
    return [value * x % P for x in vector]


def certificate(matrix):
    return dict(shape=[len(matrix), len(matrix[0])],
                sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def fixture(q):
    times = [[1, 8 ** t, 8 ** (2 * t)] for t in range(q + 1)]
    tables = [[[G[i][j] * time_factors[j] % P for j in range(3)]
               for i in range(3)] for time_factors in times]
    determinants = [residue.modular_rank(table, P)['determinant_mod_prime']
                    for table in tables]
    assert all(determinants)
    assert determinants == [4 * factors[1] * factors[2] % P for factors in times]
    minors = [((G[i][j] * G[k][l] - G[i][l] * G[k][j]) % P)
              for i, k in itertools.combinations(range(3), 2)
              for j, l in itertools.combinations(range(3), 2)]
    assert all(minors)
    return tables, dict(r=[1, 1, 1], common_matrix=G,
                        new_time=times[0], old_time_factors=times[1:],
                        actual_coefficient_tables_mod_prime=tables,
                        table_determinants_mod_prime=determinants,
                        common_matrix_two_by_two_minors_mod_prime=minors,
                        all_parameters_positive_rational=True)


def geometry_controls(tables):
    """Report the complete arrangement, beyond the paired matrix's needs."""
    lines = [(t, a) for t in range(len(tables)) for a in range(3)]
    normalized = [tuple(x * pow(tables[t][a][0], -1, P) % P
                        for x in tables[t][a]) for t, a in lines]
    checks = dict(all_line_coefficients_nonzero=all(all(row) for table in tables for row in table),
                  all_lines_distinct=len(set(normalized)) == len(lines),
                  all_pair_coordinates_nonzero=True,
                  no_unintended_three_line_points=True,
                  every_coordinate_edge_on_only_its_matching_line=True)
    failures = []
    for left, right in itertools.combinations(lines, 2):
        X = residue.cross(tables[left[0]][left[1]], tables[right[0]][right[1]], P)
        if not all(X):
            checks['all_pair_coordinates_nonzero'] = False
            failures.append(dict(kind='pair_coordinate', lines=[left, right], point=X))
        zeros = [line for line in lines
                 if not residue.dot(tables[line[0]][line[1]], X, P)]
        if zeros != [left, right]:
            checks['no_unintended_three_line_points'] = False
            failures.append(dict(kind='third_line', lines=[left, right], zero_lines=zeros))
    for line in lines:
        for edge in range(3):
            X = residue.cross(tables[line[0]][line[1]], [int(j == edge) for j in range(3)], P)
            assert X[edge] == 0 and all(X[j] for j in range(3) if j != edge)
            zeros = [other for other in lines
                     if not residue.dot(tables[other[0]][other[1]], X, P)]
            if zeros != [line]:
                checks['every_coordinate_edge_on_only_its_matching_line'] = False
                failures.append(dict(kind='edge_third_line', line=line, edge=edge, zero_lines=zeros))
    return dict(checks=checks, all_passed=all(checks.values()),
                denominator_lines=len(lines),
                pair_intersections_checked=len(lines) * (len(lines) - 1) // 2,
                coordinate_edge_intersections_checked=3 * len(lines),
                failures=failures)


def calculate_sector(tables, a):
    q, normal = len(tables) - 1, tables[0][a]
    labels = [['H', s, b] for s in range(1, q + 1) for b in range(3)]
    labels += [['J', t, c] for t in range(1, q + 1) for c in range(3)]
    matrix, row_labels, records = [], [], []
    checked = 0
    for u in range(1, q + 1):
        for d in range(3):
            raw = residue.cross(normal, tables[u][d], P)
            assert all(raw) and sum(raw) % P
            normalization = pow(sum(raw) % P, -1, P)
            X = scale(normalization, raw)
            assert sum(X) % P == 1
            forms = [[residue.dot(row, X, P) for row in table] for table in tables]
            zeros = [(t, c) for t in range(q + 1) for c in range(3) if not forms[t][c]]
            assert zeros == [(0, a), (u, d)], ('Paired node geometry failed.', a, u, d, zeros)
            v = [normal[j] * X[j] % P for j in range(3)]
            w = [tables[u][d][j] * X[j] % P for j in range(3)]
            assert sum(v) % P == sum(w) % P == 0
            residue.coordinates(v, v, w, P)
            matrices = {t: ([[value if i == d else 0 for value in w] for i in range(3)]
                             if t == u else residue.ordinary_kernel(tables, t, X, P))
                        for t in range(1, q + 1)}
            cleared = {t: [[tables[t][i][j] * X[j] *
                            product(forms[t][h] for h in range(3) if h != i) % P
                            for j in range(3)] for i in range(3)]
                       for t in range(1, q + 1)}
            remaining = product(forms[t][c] for t in range(1, q + 1) for c in range(3)
                                if (t, c) != (u, d))
            assert remaining
            inverse_remaining = pow(remaining, -1, P)
            ordinary_heads, cleared_heads, ordinary_incoming, cleared_incoming = {}, {}, {}, {}
            for t in range(1, q + 1):
                head_word = [t] + [s for s in range(1, q + 1) if s != t]
                incoming_word = [s for s in range(1, q + 1) if s != t]
                ordinary_heads[t] = residue.word_product(matrices, head_word, P)
                cleared_heads[t] = residue.word_product(cleared, head_word, P)
                ordinary_incoming[t] = residue.word_product(matrices, incoming_word, P)
                cleared_incoming[t] = residue.word_product(cleared, incoming_word, P)
            vectors = []
            for kind, t, c in labels:
                if kind == 'H':
                    actual = scale(-X[c], ordinary_heads[t][c])
                    control = scale(-X[c] * inverse_remaining, cleared_heads[t][c])
                else:
                    if t == u and c != d:
                        actual = [0, 0, 0]
                    else:
                        denominator = 1 if t == u else forms[t][c]
                        factor = -tables[t][c][a] * X[c] * pow(denominator, -1, P)
                        actual = scale(factor, rowmul(v, ordinary_incoming[t]))
                    cleared_factor = (-tables[t][c][a] * X[c] * inverse_remaining *
                                      product(forms[t][h] for h in range(3) if h != c))
                    control = scale(cleared_factor, rowmul(v, cleared_incoming[t]))
                assert actual == control, ('Polynomial clearing mismatch.', a, u, d, kind, t, c)
                assert sum(actual) % P == 0
                vectors.append(actual)
                checked += 3
            matrix.extend([[vector[j] for vector in vectors] for j in (0, 1)])
            row_labels.extend([[u, d, j] for j in (0, 1)])
            records.append(dict(old_block=u, state=d, point=X, original_cross=raw,
                                projective_scale=normalization, row_form_values=forms,
                                new_and_old_residue_basis=[v, w],
                                nonzero_remaining_denominator=remaining))
    assert len(matrix) == 6 * q and all(len(row) == 6 * q for row in matrix)
    full = certificate(matrix)
    heads = certificate([row[:3 * q] for row in matrix])
    return dict(sector=a, old_blocks=q, row_labels=row_labels, column_labels=labels,
                residue_convention='Res_L_ud(Y) at X=(normal cross A_u[d,:])/sum(cross); components 0,1, with component 2 their negative sum.',
                matrix=matrix, certificate=full, head_certificate=heads,
                full_rank=full['rank_certificate']['rank'] == 6 * q,
                paired_node_geometry_passed=True, node_records=records,
                polynomial_clearing_component_checks=checked,
                polynomial_clearing_identity='D=product_(t,c) L_tc, C_t=diag(product_(h!=c)L_th) A_t diag(X). Res_L Y=(D Y)(X)/(D/L)(X).',
                zero_sum_vector_checks=checked // 3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='One prescribed equal-weight positive fixture, all three paired sectors at q=2,3,4. No full source matrices, parameter search, or all-length theorem.',
                  prime=P, resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for q in (2, 3, 4):
            tables, data = fixture(q)
            geometry = geometry_controls(tables)
            sectors = [calculate_sector(tables, a) for a in range(3)]
            result['cases'].append(dict(old_blocks=q, fixture=data, geometry=geometry, sectors=sectors))
            print(json.dumps(dict(q=q, ranks=[s['certificate']['rank_certificate']['rank'] for s in sectors],
                                  determinants=[s['certificate']['rank_certificate']['determinant_mod_prime'] for s in sectors],
                                  complete_arrangement_geometry_passed=geometry['all_passed'])), flush=True)
        result['all_prescribed_paired_matrices_invertible'] = all(
            sector['full_rank'] for case in result['cases'] for sector in case['sectors'])
        result['status'] = ('PASS: all nine prescribed equal-weight paired matrices are invertible.'
                            if result['all_prescribed_paired_matrices_invertible'] else
                            'Completed finite diagnostic: some prescribed paired matrix is singular; no identically-singular conclusion.')
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete prescribed fixture; no replacement fixture used.',
                      error=str(error), traceback=traceback.format_exc())
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active during writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
