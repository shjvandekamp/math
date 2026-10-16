#!/usr/bin/env python3
"""Actual source residue bases inside the weighted preserving common family.

Use only r=(2,3,5), Gtilde=diag(r)+11^T, row normalization of its first
column, and times (8^t,8^(2t)), t=1,...,q, for q=3,4 over F_1000003.
The square matrix has the actual F_tsab double residues, with its negative
completed-word sign and the A_t(a,b) factor retained. The generation order
is t, then s, then all other blocks in increasing order.

An independent control clears every kernel polynomially. If
 C_t(a,b)=A_t(a,b) X_b product_(h!=a) L_th,
then the common-denominator F numerator at a cross-block pair is
 -X_a A_t(a,b) X_b product_(h!=a) L_th * e_b product_word C_j.
Divide only by the product of the remaining nonzero row forms to recover
the full vector double residue, and compare all three components with the
two recorded residue coordinates. No ordinary kernel is evaluated at a pole.

Full ranks are finite certificates within this fixed weighted family, not
an arbitrary-length source theorem. No parameter or time-fixture search.
"""

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

import normalized_sparse_source24 as sparse
import source24_residue as residue
import source24_residue_differences as geometry


P = 1000003
R = (2, 3, 5)


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def product(values):
    result = 1
    for value in values:
        result = result * value % P
    return result


def fixture(q):
    original = [[1 + (R[a] if a == b else 0) for b in range(3)] for a in range(3)]
    multipliers = [Fraction(1, row[0]) for row in original]
    rational = [[multipliers[a] * original[a][b] for b in range(3)] for a in range(3)]
    G = [[value.numerator * pow(value.denominator, -1, P) % P for value in row] for row in rational]
    assert all(row[0] == 1 for row in G)
    G_certificate = residue.modular_rank(G, P)
    assert G_certificate['determinant_mod_prime'] == 61 * pow(3, -1, P) % P
    times = sparse.factors(q, 'economic')
    assert times == [(8 ** t, 8 ** (2 * t)) for t in range(1, q + 1)]
    tables = [[[value % P for value in row] for row in table]
              for table in sparse.coefficient_tables(G, times)]
    padded = [[row[:] for row in G] for _ in range(2)] + tables
    return tables, padded, dict(
        r=R, unnormalized_common_matrix=original,
        row_normalization=[str(value) for value in multipliers],
        normalized_common_matrix_rational=[[str(value) for value in row] for row in rational],
        normalized_common_matrix_mod_prime=G, normalized_common_matrix_certificate=G_certificate,
        time_factors=times, actual_coefficient_tables_mod_prime=tables,
        table_determinants=[G_certificate['determinant_mod_prime'] * u * v % P for u, v in times])


def ordinary_controls(tables, columns):
    records, checked = [], 0
    for X in ((1, 2, 3), (2, 3, 5)):
        ordinary = sparse.evaluated_columns(tables, X)
        assert ordinary is not None, ('Prescribed ordinary control point is a pole.', X)
        kernels = [residue.ordinary_kernel(tables, t, X, P) for t in range(len(tables))]
        for j, (t, s, a, b) in enumerate(columns):
            word = [s] + [u for u in range(len(tables)) if u not in (t, s)]
            tail = residue.word_product(kernels, word, P)
            actual = [X[a] * kernels[t][a][b] * (int(c == b) - tail[b][c]) % P for c in range(3)]
            restored = [tables[t][a][b] * value % P for value in ordinary[3 * len(tables) + j]]
            assert actual == restored
            checked += 3
        records.append(dict(point=X, all_denominators_units=True,
                            denominators=[[residue.dot(row, X, P) for row in table] for table in tables]))
    return dict(points=records, actual_A_factor_and_word_component_checks=checked)


def polynomial_pair_controls(tables, columns, matrix):
    q = len(tables)
    records, rows, checked = [], [], 0
    for u, v in itertools.combinations(range(q), 2):
        for c, d in itertools.product(range(3), repeat=2):
            X = residue.cross(tables[u][c], tables[v][d], P)
            forms = [[residue.dot(row, X, P) for row in table] for table in tables]
            zeros = [(t, a) for t in range(q) for a in range(3) if not forms[t][a]]
            assert zeros == [(u, c), (v, d)] and all(X)
            remaining = product(forms[t][a] for t in range(q) for a in range(3)
                                if (t, a) not in ((u, c), (v, d)))
            assert remaining
            remaining_inverse = pow(remaining, -1, P)
            cleared_kernels = [[[tables[t][a][b] * X[b] *
                                 product(forms[t][h] for h in range(3) if h != a) % P
                                 for b in range(3)] for a in range(3)] for t in range(q)]
            words = {(t, s): residue.word_product(cleared_kernels,
                     [s] + [j for j in range(q) if j not in (t, s)], P)
                     for t in range(q) for s in range(q) if t != s}
            U = [tables[u][c][j] * X[j] % P for j in range(3)]
            V = [tables[v][d][j] * X[j] % P for j in range(3)]
            pair_position = len(records)
            for column, (t, s, a, b) in enumerate(columns):
                numerator = -X[a] * tables[t][a][b] * X[b] * product(
                    forms[t][h] for h in range(3) if h != a)
                actual = [numerator * entry * remaining_inverse % P for entry in words[t, s][b]]
                alpha, beta = matrix[2 * pair_position][column], matrix[2 * pair_position + 1][column]
                reconstructed = [(alpha * U[j] + beta * V[j]) % P for j in range(3)]
                assert actual == reconstructed, ('Polynomial residue discrepancy', u, v, c, d, columns[column])
                assert sum(actual) % P == 0
                checked += 3
            rows.extend([[u, v, c, d, coordinate] for coordinate in ('alpha', 'beta')])
            records.append(dict(lines=[[u, c], [v, d]], point=X,
                                row_form_values=forms, nonzero_remaining_denominator=remaining,
                                residue_basis=[U, V], all_three_components_verified=True))
    return rows, dict(cross_pair_records=records, polynomial_clearing_component_checks=checked)


def calculate(q):
    started = time.monotonic()
    tables, padded, data = fixture(q)
    # This stronger check includes same-block intersections and every coordinate
    # axis; fail explicitly at the prescribed fixture rather than replacing it.
    strong_geometry = geometry.check_geometry(q, padded)
    matrix, residue_geometry = residue.residue_matrix(q + 2, padded, P)
    columns = [(t, s, a, b) for t in range(q) for s in range(q) if t != s
               for a in range(3) for b in range(3)]
    size = 9 * q * (q - 1)
    assert len(matrix) == len(columns) == size and all(len(row) == size for row in matrix)
    rows, polynomial = polynomial_pair_controls(tables, columns, matrix)
    ordinary = ordinary_controls(tables, columns)
    certificate = residue.modular_rank(matrix, P)
    result = dict(q=q, prime=P, fixture=data,
                  block_numbering='Zero based active blocks; existing residue helper indices are shifted by two.',
                  source_formula='F_tsab=Xa K_t(a,b) e_b(I-P_s^omit_t), with the actual A_t(a,b) factor.',
                  full_generation_orders=[dict(column=j, word=[t, s] + [u for u in range(q) if u not in (t, s)])
                                          for j, (t, s, a, b) in enumerate(columns)],
                  residue_coordinate_convention='P=A_u(c,:) cross A_v(d,:); vector residue=alpha*A_u(c,:)diag(P)+beta*A_v(d,:)diag(P).',
                  row_labels=rows, column_labels=columns, matrix=matrix,
                  matrix_sha256=residue.matrix_hash(matrix), rank_certificate=certificate,
                  full_column_rank=certificate['rank'] == size, target_dimension=size,
                  strong_geometry=strong_geometry, residue_geometry=residue_geometry,
                  polynomial_clearing_control=polynomial, ordinary_source_control=ordinary,
                  elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(q=q, rank=certificate['rank'], size=size,
                          determinant=certificate['determinant_mod_prime'], geometry_pass=True)), flush=True)
    return result


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
    result = dict(scope='Only the prescribed weighted family r=(2,3,5), economic times, q=3,4; no search or all-length claim.',
                  interpretation='Exact actual-F double-residue matrices. Full ranks certify these finite weighted-family bases; the accepted E-kernel theorem is not re-proved here.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for q in (3, 4):
            result['cases'].append(calculate(q))
        result['status'] = ('PASS: both actual source residue matrices are invertible in the weighted family.'
                            if all(case['full_column_rank'] for case in result['cases']) else
                            'Completed: at least one prescribed finite residue matrix is deficient; no generic conclusion.')
    except Exception as error:
        failure = error
        result['status'] = 'FAILED or incomplete prescribed-fixture check; no replacement fixture used.'
        result['error'] = str(error)
        result['traceback'] = traceback.format_exc()
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
