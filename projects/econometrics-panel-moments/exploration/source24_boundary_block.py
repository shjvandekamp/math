#!/usr/bin/env python3
"""Extract one exact boundary block from the saved weighted q=4 source matrix.

No source residue matrix is regenerated. Rows meet active block zero and
columns have shared block zero or first tail block zero. The block-zero
state separates three 18-square sectors, each with nine new-head columns.
An actual column correction eliminates those 27 head columns and records
the remaining 27-square Schur determinant, including permutation signs.

For clarity, the input's q=4 counts all blocks. The boundary has three old
blocks, so its sizes are 18*3 and 9*3. The small paired-pole controls derive
the two-block formula from raw residue vectors at the saved points; they
are not substituted for the four-block tails. All conclusions are finite.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

import source24_residue as residue
import source24_schur as schur


P = 1000003


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def block(matrix, rows, columns):
    return [[matrix[i][j] for j in columns] for i in rows]


def certificate(matrix):
    return dict(shape=[len(matrix), len(matrix[0])], sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def two_block_controls(case):
    """Clear the two actual row poles before evaluating their raw vectors."""
    tables = case['fixture']['actual_coefficient_tables_mod_prime']
    records = []
    for v in range(1, 4):
        for a, b in itertools.product(range(3), repeat=2):
            X = residue.cross(tables[0][a], tables[v][b], P)
            assert all(X)
            assert residue.dot(tables[0][a], X, P) == 0
            assert residue.dot(tables[v][b], X, P) == 0
            U = [tables[0][a][j] * X[j] % P for j in range(3)]
            V = [tables[v][b][j] * X[j] % P for j in range(3)]
            # F_0v contributes -Xa A_0(a,b) Xb v_v; the reversed source
            # contributes -Xb A_v(b,a) Xa v_0. The identity terms have no
            # double pole. These are two-block vectors, without other tails.
            forward = [-X[a] * tables[0][a][b] * X[b] * value % P for value in V]
            reverse = [-X[b] * tables[v][b][a] * X[a] * value % P for value in U]
            coordinates = list(zip(residue.coordinates(forward, U, V, P),
                                   residue.coordinates(reverse, U, V, P)))
            paired = [list(row) for row in coordinates]
            expected = [[0, -tables[v][b][a] * X[a] * X[b] % P],
                        [-tables[0][a][b] * X[a] * X[b] % P, 0]]
            assert paired == expected
            determinant = (paired[0][0] * paired[1][1] - paired[0][1] * paired[1][0]) % P
            formula = -(X[a] * X[b]) ** 2 * tables[0][a][b] * tables[v][b][a] % P
            assert determinant == formula and determinant
            records.append(dict(lines=[[0, a], [v, b]], point=X, residue_basis=[U, V],
                                raw_two_block_vectors=[forward, reverse], matrix=paired,
                                determinant_mod_prime=determinant))
    return dict(scope='Two-block raw paired-pole identity at 27 saved-fixture points; not the four-block tail matrix.',
                formula='det=-Xa^2 Xb^2 A_0(a,b) A_v(b,a), columns (F_0v^ab,F_v0^ba), coordinates (v_0,v_v).',
                all_coordinate_and_entry_factors_nonzero=True,
                full_vector_reconstruction_checks=6 * len(records), records=records)


def calculate(input_path):
    data_bytes = input_path.read_bytes()
    saved = json.loads(data_bytes)
    cases = [case for case in saved['cases'] if case['q'] == 4]
    assert len(cases) == 1
    case = cases[0]
    assert case['prime'] == P == schur.P and case['fixture']['r'] == [2, 3, 5]
    matrix = case['matrix']
    rows, columns = case['row_labels'], case['column_labels']
    assert rows == [[u, v, a, b, coordinate]
                    for u, v in itertools.combinations(range(4), 2)
                    for a, b in itertools.product(range(3), repeat=2)
                    for coordinate in ('alpha', 'beta')]
    assert columns == [[t, s, a, b] for t in range(4) for s in range(4) if t != s
                       for a, b in itertools.product(range(3), repeat=2)]
    assert len(matrix) == 108 and all(len(row) == 108 for row in matrix)
    assert residue.matrix_hash(matrix) == case['matrix_sha256']
    assert case['rank_certificate']['rank'] == 108 and case['full_column_rank']
    assert all(case['strong_geometry'].values())
    assert case['polynomial_clearing_control']['polynomial_clearing_component_checks'] == 17496

    selected_rows = [i for i, row in enumerate(rows) if row[0] == 0]
    selected_columns = [j for j, col in enumerate(columns) if 0 in col[:2]]
    boundary = block(matrix, selected_rows, selected_columns)
    boundary_rows = [rows[i] for i in selected_rows]
    boundary_columns = [columns[j] for j in selected_columns]
    boundary_certificate = certificate(boundary)
    assert boundary_certificate['shape'] == [54, 54]
    assert boundary_certificate['rank_certificate']['determinant_mod_prime'] == 482791

    def sector(label):
        t, s, a, b = label
        return a if t == 0 else b

    off_sector_checks = 0
    for i, label in enumerate(boundary_rows):
        for j, column in enumerate(boundary_columns):
            if label[2] != sector(column):
                assert boundary[i][j] == 0, ('Off-sector entry', label, column)
                off_sector_checks += 1

    sectors, row_order, column_order = [], [], []
    sector_determinant_product = 1
    for a in range(3):
        rr = [i for i, label in enumerate(boundary_rows) if label[2] == a]
        head = [j for j, label in enumerate(boundary_columns) if label[0] == 0 and label[2] == a]
        first = [j for j, label in enumerate(boundary_columns) if label[1] == 0 and label[3] == a]
        assert len(rr) == 18 and len(head) == len(first) == 9
        sector_matrix = block(boundary, rr, head + first)
        sector_certificate = certificate(sector_matrix)
        head_certificate = certificate(block(boundary, rr, head))
        assert sector_certificate['rank_certificate']['rank'] == 18
        assert head_certificate['rank_certificate']['rank'] == 9
        sector_determinant_product *= sector_certificate['rank_certificate']['determinant_mod_prime']
        sector_determinant_product %= P
        row_order += rr
        column_order += head + first
        sectors.append(dict(state=a, boundary_row_indices=rr, boundary_column_indices=head + first,
                            row_labels=[boundary_rows[i] for i in rr],
                            head_column_labels=[boundary_columns[j] for j in head],
                            first_column_labels=[boundary_columns[j] for j in first],
                            matrix=sector_matrix, certificate=sector_certificate,
                            head_certificate=head_certificate))
    sector_sign = schur.permutation_sign(row_order) * schur.permutation_sign(column_order)
    original_determinant = boundary_certificate['rank_certificate']['determinant_mod_prime']
    assert sector_determinant_product == sector_sign * original_determinant % P

    head = [j for j, label in enumerate(boundary_columns) if label[0] == 0]
    first = [j for j, label in enumerate(boundary_columns) if label[1] == 0]
    head_matrix = block(boundary, range(54), head)
    first_matrix = block(boundary, range(54), first)
    head_certificate = certificate(head_matrix)
    assert head_certificate['rank_certificate']['rank'] == 27
    pivot_rows = head_certificate['rank_certificate']['nonzero_minor']['rows']
    other_rows = [i for i in range(54) if i not in pivot_rows]
    head_minor = [head_matrix[i] for i in pivot_rows]
    inverse_data = schur.invert(head_minor)
    assert inverse_data is not None
    inverse, inverse_certificate = inverse_data
    corrections = schur.matrix_product(inverse, [first_matrix[i] for i in pivot_rows])
    residual = schur.matrix_difference(first_matrix, schur.matrix_product(head_matrix, corrections))
    assert all(not any(residual[i]) for i in pivot_rows)
    first_schur = [residual[i] for i in other_rows]
    schur_certificate = certificate(first_schur)
    assert schur_certificate['shape'] == [27, 27]
    assert schur_certificate['rank_certificate']['rank'] == 27
    schur_sign = schur.permutation_sign(pivot_rows + other_rows) * schur.permutation_sign(head + first)
    factored = (inverse_certificate['determinant_mod_prime'] *
                schur_certificate['rank_certificate']['determinant_mod_prime']) % P
    assert factored == schur_sign * original_determinant % P

    return dict(total_blocks=4, boundary_old_blocks=3, prime=P,
                input_file=input_path.name, input_sha256=hashlib.sha256(data_bytes).hexdigest(),
                saved_full_matrix_sha256=case['matrix_sha256'], fixture=case['fixture'],
                saved_geometry=case['strong_geometry'],
                saved_polynomial_clearing_control_count=17496,
                saved_matrix_regenerated=False,
                residue_coordinate_convention=case['residue_coordinate_convention'],
                full_matrix_row_indices=selected_rows, full_matrix_column_indices=selected_columns,
                row_labels=boundary_rows, column_labels=boundary_columns,
                matrix=boundary, certificate=boundary_certificate,
                off_sector_zero_entries_checked=off_sector_checks, sectors=sectors,
                sector_factorization=dict(row_permutation=row_order, column_permutation=column_order,
                                          permutation_sign=sector_sign,
                                          product_of_sector_determinants_mod_prime=sector_determinant_product,
                                          determinant_identity_verified=True),
                head_elimination=dict(head_boundary_column_indices=head, first_boundary_column_indices=first,
                                      head_certificate=head_certificate, pivot_boundary_rows=pivot_rows,
                                      remaining_boundary_rows=other_rows, head_minor_matrix=head_minor,
                                      head_minor_inverse_certificate=inverse_certificate,
                                      head_correction_coefficients=corrections,
                                      correction_convention='First - Head * coefficients; pivot rows vanish exactly.',
                                      schur_matrix=first_schur, schur_certificate=schur_certificate,
                                      schur_row_labels=[boundary_rows[i] for i in other_rows],
                                      schur_column_labels=[boundary_columns[j] for j in first],
                                      permutation_sign=schur_sign,
                                      product_of_head_and_schur_determinants_mod_prime=factored,
                                      determinant_identity_verified=True),
                two_block_paired_pole_controls=two_block_controls(case))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('source24-weighted-source-base-results.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='One boundary extraction from the saved weighted four-block actual source residue matrix; no matrix regeneration, search, or all-length claim.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2))
    failure = None
    try:
        result['case'] = calculate(args.input)
        result['status'] = 'PASS: exact boundary/sector/head/Schur certificates and determinant factorizations.'
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete prescribed saved-matrix extraction.',
                      error=str(error), traceback=traceback.format_exc())
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active while writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)
    case = result['case']
    print(json.dumps(dict(boundary_determinant=case['certificate']['rank_certificate']['determinant_mod_prime'],
                          sector_determinants=[sector['certificate']['rank_certificate']['determinant_mod_prime']
                                               for sector in case['sectors']],
                          sector_head_ranks=[sector['head_certificate']['rank_certificate']['rank']
                                            for sector in case['sectors']],
                          first_schur_determinant=case['head_elimination']['schur_certificate']['rank_certificate']['determinant_mod_prime'])), flush=True)


if __name__ == '__main__':
    main()
