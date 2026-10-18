#!/usr/bin/env python3
"""Verify Pro48's supplied two-block tail/head transport certificate.

Use only G=I+11^T, sector0, old times (1,8,64),(1,64,4096), and
X=(x,-2*x-1,1) at x=100,...,107 modulo 1000003. The thirteen basis rows
are H_1c,H_2c,J_1c,J_2c in the existing order, followed by v=(2X0,X1,X2).
The targets are U_c=X_c e_c(I-K_2).

Independently clear the six old row forms in every actual basis and target
row. The resulting polynomial coordinates have degree at most seven, so
the eight distinct unit points certify each supplied expansion. Separately
check the supplied 13-square augmented evaluation minor and reconstruct
the head correction C2 from augmented head sums, including each expansion's
polynomial v margin. The proper head transport is A=I-C2; check it separately.

This establishes the prescribed finite correction C2 and proper transport A,
both of full rank. It does not establish a nonzero recursive coefficient for
all lengths.
"""

import argparse
import json
from pathlib import Path
import signal
import time
import traceback

import source24_residue as residue
import source24_equal_weight_boundary as paired
from source24_binary_terminal_response import Terminal, G, P, NORMAL, matvec


SOURCE_URL = 'https://chatgpt.com/c/6ad1cec4-13e8-83eb-9ad0-b37bf8146e02'
COEFFICIENTS = [
    [915965, 938418, 562648], [145911, 202607, 955422], [210998, 754630, 193382],
    [804951, 762019, 145382], [768204, 535201, 76966], [27471, 27438, 53546],
    [986114, 167016, 58457], [215870, 652500, 726132], [19314, 979078, 939713],
    [949509, 440475, 161562], [771867, 2335, 791497], [636242, 555211, 56755],
    [483749, 467476, 629805],
]
EXPECTED_CORRECTION = [[688408, 635383, 967637], [397861, 205281, 662190], [722218, 249541, 876733]]
EXPECTED_CORRECTION_DETERMINANT = 755800
EXPECTED_TRANSPORT_DETERMINANT = 241168
EXPECTED_MINOR_DETERMINANT = 434633
EXPECTED_VK2_HEAD = [20175, 336814, 429300]


def combine_rows(coefficients, rows):
    return [sum(value * row[j] for value, row in zip(coefficients, rows)) % P for j in range(3)]


def augmented_head(coefficients, labels):
    assert labels[-1] == ['v'] and len(coefficients) == len(labels)
    return [(sum(coefficients[i] for i, label in enumerate(labels[:-1])
                 if label[0] == 'H' and label[2] == j) + coefficients[-1] * NORMAL[j]) % P
            for j in range(3)]


def polynomial_rows(ctx, X, forms, D):
    """Degree-seven common-denominator numerators, without any division."""
    cleared = {t: [[ctx.tables[t][i][j] * X[j] *
                    paired.product(forms[t][h] for h in range(3) if h != i) % P
                    for j in range(3)] for i in range(3)] for t in (1, 2)}
    output = []
    for kind, t, c in ctx.old['column_labels']:
        word = ([t] + [s for s in (1, 2) if s != t] if kind == 'H' else [s for s in (1, 2) if s != t])
        whole = residue.word_product(cleared, word, P)
        if kind == 'H':
            output.append([X[c] * (int(c == j) * D - whole[c][j]) % P for j in range(3)])
        else:
            factor = -ctx.tables[t][c][0] * X[c] * paired.product(forms[t][h] for h in range(3) if h != c)
            output.append(paired.scale(factor, paired.rowmul(ctx.v(X), whole)))
    output.append(paired.scale(D, ctx.v(X)))
    targets = []
    for c in range(3):
        remaining = paired.product(forms[t][h] for t in (1, 2) for h in range(3) if (t, h) != (2, c))
        targets.append([X[c] * (int(c == j) * D - ctx.tables[2][c][j] * X[j] * remaining) % P
                        for j in range(3)])
    return output, targets


def calculate(record):
    ctx = Terminal(3)
    assert ctx.m == 2 and ctx.fixture['old_time_factors'] == [[1, 8, 64], [1, 64, 4096]]
    labels = ctx.old['column_labels'] + [['v']]
    expected_labels = [[kind, t, c] for kind in ('H', 'J') for t in (1, 2) for c in range(3)] + [['v']]
    assert labels == expected_labels
    record.update(fixture=ctx.fixture, geometry=ctx.geometry, augmented_basis_labels=labels,
                  supplied_coefficient_rows=COEFFICIENTS,
                  coefficient_column_labels=[['U', 2, c] for c in range(3)],
                  shorter_paired_matrix_sha256=residue.matrix_hash(ctx.old['matrix']),
                  shorter_paired_certificate=ctx.old['certificate'], point_records=[])
    evaluation_rows = {}
    for x in range(100, 108):
        X = [x, -2 * x - 1, 1]
        assert residue.dot(NORMAL, X, P) == 0 and all(value % P for value in X)
        forms = ctx.old_forms(X)
        assert all(value for row in forms.values() for value in row)
        D = paired.product(value for row in forms.values() for value in row)
        basis = ctx.old_rows(X) + [ctx.v(X)]
        K2 = ctx.kernels(X)[2]
        targets = [[X[c] * (int(c == j) - K2[c][j]) % P for j in range(3)] for c in range(3)]
        cleared_basis, cleared_targets = polynomial_rows(ctx, X, forms, D)
        reconstructed = [combine_rows([COEFFICIENTS[i][c] for i in range(13)], basis) for c in range(3)]
        cleared_reconstruction = [combine_rows([COEFFICIENTS[i][c] for i in range(13)], cleared_basis)
                                  for c in range(3)]
        point_record = dict(x=x, point=X, old_row_forms=forms, common_denominator=D,
                            actual_augmented_basis=basis, actual_targets=targets,
                            polynomial_augmented_basis=cleared_basis, polynomial_targets=cleared_targets,
                            reconstructed_targets=reconstructed, polynomial_reconstructed_targets=cleared_reconstruction,
                            certificate_matches=(reconstructed == targets and cleared_reconstruction == cleared_targets))
        record['point_records'].append(point_record)
        assert cleared_basis == [paired.scale(D, row) for row in basis], ('Actual basis clearing failed.', x)
        assert cleared_targets == [paired.scale(D, row) for row in targets], ('Actual target clearing failed.', x)
        assert point_record['certificate_matches'], ('Supplied Pro48 expansion failed.', x, targets, reconstructed)
        assert all(sum(row) % P == 0 for row in basis + targets)
        evaluation_rows[x] = [[row[j] for row in basis] for j in range(3)]

    minor_labels = [[x, j] for x in range(100, 106) for j in (0, 1)] + [[106, 0]]
    minor = [evaluation_rows[x][j] for x, j in minor_labels]
    minor_certificate = paired.certificate(minor)
    record['augmented_evaluation_minor'] = dict(row_labels=minor_labels, column_labels=labels,
                                                matrix=minor, certificate=minor_certificate,
                                                supplied_determinant=EXPECTED_MINOR_DETERMINANT)
    assert minor_certificate['rank_certificate']['rank'] == 13
    assert minor_certificate['rank_certificate']['determinant_mod_prime'] == EXPECTED_MINOR_DETERMINANT

    correction_columns = [augmented_head([COEFFICIENTS[i][c] for i in range(13)], labels) for c in range(3)]
    correction = [[correction_columns[c][j] for c in range(3)] for j in range(3)]
    correction_certificate = paired.certificate(correction)
    record['head_correction'] = dict(matrix=correction, certificate=correction_certificate,
                                     convention='Column c of C2 is Sigma2(U_c): the sum of actual H coefficients plus lambda_c*g. The last supplied coefficient row is lambda.',
                                     supplied_matrix=EXPECTED_CORRECTION, supplied_determinant=EXPECTED_CORRECTION_DETERMINANT)
    assert correction == EXPECTED_CORRECTION
    assert correction_certificate['rank_certificate']['rank'] == 3
    assert correction_certificate['rank_certificate']['determinant_mod_prime'] == EXPECTED_CORRECTION_DETERMINANT

    transport = [[(int(i == j) - correction[i][j]) % P for j in range(3)] for i in range(3)]
    transport_certificate = paired.certificate(transport)
    record['head_transport'] = dict(matrix=transport, certificate=transport_certificate,
                                    convention='The proper head transport is A=I-C2, where C2 is the head_correction matrix.',
                                    supplied_determinant=EXPECTED_TRANSPORT_DETERMINANT)
    assert transport_certificate['rank_certificate']['rank'] == 3
    assert transport_certificate['rank_certificate']['determinant_mod_prime'] == EXPECTED_TRANSPORT_DETERMINANT

    # v*K2 = v - sum_c g_c U_c, using the actual single-kernel targets.
    vk2_coefficients = [((1 if i == 12 else 0) - residue.dot(row, NORMAL, P)) % P
                        for i, row in enumerate(COEFFICIENTS)]
    vk2_head = augmented_head(vk2_coefficients, labels)
    identity_head = [(NORMAL[j] - value) % P for j, value in enumerate(matvec(correction, NORMAL))]
    transported_head = matvec(transport, NORMAL)
    record['vK2_transport'] = dict(actual_basis_coefficients=vk2_coefficients,
                                   augmented_head=vk2_head, g_minus_C2_g=identity_head,
                                   A_times_g=transported_head,
                                   supplied_augmented_head=EXPECTED_VK2_HEAD, point_controls=[])
    assert vk2_head == identity_head == transported_head == EXPECTED_VK2_HEAD
    for point_record in record['point_records']:
        X, basis = point_record['point'], point_record['actual_augmented_basis']
        actual = paired.rowmul(ctx.v(X), ctx.kernels(X)[2])
        reconstructed = combine_rows(vk2_coefficients, basis)
        point_control = dict(x=point_record['x'], actual_vK2=actual, reconstructed_vK2=reconstructed)
        record['vK2_transport']['point_controls'].append(point_control)
        assert actual == reconstructed

    record['validation'] = dict(distinct_unit_points=8, coordinate_polynomial_degree_bound=7,
                                common_denominator='Product of the six actual old row forms.',
                                actual_basis_polynomial_clearing_component_checks=8 * 13 * 3,
                                actual_target_polynomial_clearing_component_checks=8 * 3 * 3,
                                supplied_expansion_polynomial_component_checks=8 * 3 * 3,
                                actual_vK2_component_checks=8 * 3,
                                polynomial_identity_certificate_passed=True,
                                augmented_minor_independent_of_shorter_residue_inverse=True)


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
    result = dict(scope='One supplied Pro48 two-block head-transport certificate; no new parameter fixture or all-length nonvanishing claim.',
                  source_url=SOURCE_URL, prime=P,
                  supplied_coefficients=COEFFICIENTS, supplied_head_correction=EXPECTED_CORRECTION,
                  supplied_head_correction_determinant=EXPECTED_CORRECTION_DETERMINANT,
                  supplied_head_transport_determinant=EXPECTED_TRANSPORT_DETERMINANT,
                  supplied_augmented_minor_determinant=EXPECTED_MINOR_DETERMINANT,
                  supplied_vK2_head=EXPECTED_VK2_HEAD,
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), case={})
    failure = None
    try:
        calculate(result['case'])
        result['status'] = 'PASS: supplied actual-row expansions, augmented minor, full-rank head correction and proper transport, and vK2 head identity verified.'
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete supplied certificate; no replacement fixture used.',
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
    case = result['case']
    print(json.dumps(dict(head_correction_determinant=case['head_correction']['certificate']['rank_certificate']['determinant_mod_prime'],
                          head_transport_determinant=case['head_transport']['certificate']['rank_certificate']['determinant_mod_prime'],
                          augmented_minor_determinant=case['augmented_evaluation_minor']['certificate']['rank_certificate']['determinant_mod_prime'],
                          Sigma2_vK2=case['vK2_transport']['augmented_head'])), flush=True)


if __name__ == '__main__':
    main()
