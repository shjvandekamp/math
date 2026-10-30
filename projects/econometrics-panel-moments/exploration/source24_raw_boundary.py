#!/usr/bin/env python3
"""Finite raw-boundary ranks modulo the entire specified appended old frame.

For q old blocks and one terminal block, the old frame contains both
elementary directed E rows at each old cross-block line pair, every V_i,b,
and the three diagonal rows X_d e_d. Append the actual K_terminal on the
right. Add all 18q actual raw completed products whose shared or first
block is terminal. Evaluate at deterministic ordinary points off all poles.

A full combined minor certifies independence modulo this entire appended
frame at the stated rational fixture. A deficient evaluation matrix does
not prove a rational-function rank upper bound. The q=1 control separately
checks the direct identity placing every first-new row in the old frame.
This is not the source O matrix and proves no all-length induction theorem.

Reproduce:
  nice -n 19 python3 exploration/source24_raw_boundary.py --output exploration/source24-raw-boundary-results.json
  nice -n 19 python3 exploration/source24_raw_boundary.py --q4-followup --output exploration/source24-raw-boundary-results.json
"""

import argparse
import itertools
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming
import source24_residue_differences as differences


P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
POINT_SEED = 240015


def row_scale(scalar, row):
    return [scalar * x % P for x in row]


def row_subtract(left, right):
    return [(a - b) % P for a, b in zip(left, right)]


def ordinary_points(A, count):
    """Two independently advanced LCG coordinates; no fixed one-variable curve."""
    state, points, seen, rejected = POINT_SEED, [], set(), 0
    while len(points) < count:
        state = (1664525 * state + 1013904223) % (2 ** 32)
        x = 2 + state % 10007
        state = (1664525 * state + 1013904223) % (2 ** 32)
        y = 2 + state % 10007
        X = (1, x, y)
        if X in seen or any(residue.dot(row, X, P) == 0 for table in A[2:] for row in table):
            rejected += 1
            continue
        seen.add(X)
        points.append(X)
    return points, rejected


def labels(q):
    old = list(range(2, q + 2))
    terminal = q + 2
    frame = []
    for u, v in itertools.combinations(old, 2):
        for c, d in itertools.product(range(3), repeat=2):
            frame.append(dict(kind='elementary_pair', start=[u, c], end=[v, d]))
            frame.append(dict(kind='elementary_pair', start=[v, d], end=[u, c]))
    for u in old:
        for c, b in itertools.product(range(3), repeat=2):
            frame.append(dict(kind='V', line=[u, c], output=b))
    frame.extend(dict(kind='diagonal', state=d) for d in range(3))
    boundary = [dict(kind='shared_new', t=terminal, s=s, a=a, b=b)
                for s in old for a, b in itertools.product(range(3), repeat=2)]
    boundary += [dict(kind='first_new', t=t, s=terminal, a=a, b=b)
                 for t in old for a, b in itertools.product(range(3), repeat=2)]
    assert len(frame) == 9 * q * q + 3 and len(boundary) == 18 * q
    return frame, boundary


def evaluate(q, A, X, frame_labels, boundary_labels):
    old, blocks, terminal = list(range(2, q + 2)), list(range(2, q + 3)), q + 2
    kernels = {t: residue.ordinary_kernel(A, t, X, P) for t in blocks}
    Kterminal = kernels[terminal]
    frame, V_indices, diagonal_indices = [], {}, {}
    for label in frame_labels:
        if label['kind'] == 'elementary_pair':
            u, c = label['start']
            v, d = label['end']
            # E_i->j = Xc*K_u(c,d)*(e_d-K_v(d,:)).
            row = row_scale(X[c] * kernels[u][c][d],
                            row_subtract([int(j == d) for j in range(3)], kernels[v][d]))
        elif label['kind'] == 'V':
            u, c = label['line']
            b = label['output']
            row = [(X[c] * kernels[u][c][b] * int(j == b)
                    - int(c == b and j == c) * X[c]) % P for j in range(3)]
            V_indices[u, c, b] = len(frame)
        else:
            d = label['state']
            row = [X[d] * int(j == d) % P for j in range(3)]
            diagonal_indices[d] = len(frame)
        frame.append(residue.matmul([row], Kterminal, P)[0])

    products = {}
    boundary = []
    for label in boundary_labels:
        t, s, a, b = (label[name] for name in ('t', 's', 'a', 'b'))
        if (t, s) not in products:
            actual_word = [s] + [u for u in blocks if u not in (t, s)]
            products[t, s] = residue.word_product(kernels, actual_word, P)
        row = row_scale(X[a] * kernels[t][a][b], products[t, s][b])
        boundary.append(row)
    calibration_checks = 0
    if q == 1:
        for label, row in zip(boundary_labels, boundary):
            if label['kind'] != 'first_new':
                continue
            t, a, b = label['t'], label['a'], label['b']
            vrow, diagonal = frame[V_indices[t, a, b]], frame[diagonal_indices[a]]
            expected = [(vrow[d] + int(a == b) * diagonal[d]) % P for d in range(3)]
            assert row == expected, ('q1 containment control failed.', X, t, a, b)
            calibration_checks += 1
    return frame + boundary, calibration_checks


def calculate(q, mode, count_multiplier=1, case_label=None, prefix_reference=None, point_count_override=None):
    started = time.monotonic()
    m = q + 1
    times = sparse.factors(m, mode)
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    geometry = differences.check_geometry(m, A)
    frame_labels, boundary_labels = labels(q)
    old_size, boundary_size = len(frame_labels), len(boundary_labels)
    target = old_size + boundary_size
    # The row-sum space has dimension only 6m+3. Three components at each
    # point therefore do not supply three unrestricted independent rows.
    minimum_points = (target + 1) // 2 + 12
    assert count_multiplier >= 1
    point_count = point_count_override if point_count_override is not None else count_multiplier * minimum_points
    assert point_count > 0
    points, rejected = ordinary_points(A, point_count)
    matrix, calibration_checks = [], 0
    for X in points:
        values, checks = evaluate(q, A, X, frame_labels, boundary_labels)
        assert len(values) == target
        matrix.extend([[value[d] for value in values] for d in range(3)])
        calibration_checks += checks
    if prefix_reference is not None:
        prefix_count = prefix_reference['point_count']
        assert [list(X) for X in points[:prefix_count]] == prefix_reference['evaluation_points']
        assert residue.matrix_hash(matrix[:3 * prefix_count]) == prefix_reference['combined_evaluation']['sha256']
    old_matrix = [row[:old_size] for row in matrix]
    old_certificate = incoming.matrix_certificate(old_matrix)
    combined_certificate = incoming.matrix_certificate(matrix)
    old_rank = old_certificate['rank_certificate']['rank']
    combined_rank = combined_certificate['rank_certificate']['rank']
    old_full = old_rank == old_size
    full = combined_rank == target
    if q == 1:
        assert combined_rank <= old_rank + 9 and not full
    result = dict(q=q, m=m, time_fixture=mode, case_label=case_label, prime=P, G=G, time_factors=times,
                  full_old_line_geometry=geometry,
                  appended_old_frame_columns=old_size, raw_boundary_columns=boundary_size,
                  combined_target_rank=target, evaluation_points=points,
                  point_count=point_count, evaluation_rows=3 * point_count,
                  minimum_requested_point_count=minimum_points, point_count_multiplier=count_multiplier,
                  point_count_policy='explicit historical-control override' if point_count_override is not None else 'ceil(columns/2)+12',
                  row_sum_space_dimension=6 * m + 3,
                  sampling_rank_upper_bound=min(3 * point_count, 2 * point_count + 6 * m + 3, target),
                  sampling_can_support_target=2 * point_count + 6 * m + 3 >= target,
                  point_generator_seed=POINT_SEED,
                  rejected_pole_or_duplicate_points=rejected,
                  every_evaluation_point_off_every_actual_block_pole=True,
                  appended_old_frame=old_certificate, appended_old_frame_full_rank=old_full,
                  combined_evaluation=combined_certificate,
                  boundary_rank_gain_at_evaluation=combined_rank - old_rank,
                  boundary_evaluation_deficiency=boundary_size - (combined_rank - old_rank),
                  finite_independence_modulo_entire_appended_frame_certified=old_full and full,
                  q1_direct_first_new_containment_checks=calibration_checks,
                  q1_containment_identity='Qhat_(t,m,a,b)=V_(t,a,b)*K_m+delta_ab*X_a*e_a*K_m' if q == 1 else None,
                  frame_column_labels=frame_labels, boundary_column_labels=boundary_labels,
                  evaluation_row_order='Point order as listed; component 0,1,2 within each point.',
                  elapsed_seconds=time.monotonic() - started)
    if prefix_reference is not None:
        result['original_evaluation_prefix_verified'] = dict(
            point_count=prefix_reference['point_count'],
            combined_matrix_sha256=prefix_reference['combined_evaluation']['sha256'])
    print(json.dumps(dict(q=q, m=m, time_fixture=mode, old_rank=old_rank, old_columns=old_size,
                          case_label=case_label, point_count=point_count,
                          combined_rank=combined_rank, target=target, boundary_rank_gain=combined_rank - old_rank,
                          boundary_columns=boundary_size, full_modulo_frame=old_full and full,
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--q4-followup', action='store_true',
                        help='Append only the q4 independent and doubled-point economic diagnostics to an existing result file.')
    args = parser.parse_args()
    existing = None
    if args.q4_followup:
        if args.output is None or not args.output.is_file():
            parser.error('--q4-followup needs --output pointing to the original saved results.')
        existing = json.loads(args.output.read_text())
        original_q4 = next(case for case in existing['cases'] if case['q'] == 4
                           and case['time_fixture'] == 'economic' and not case.get('case_label'))
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second raw-boundary cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB raw-boundary RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation = None
    try:
        if args.q4_followup:
            cases.append(calculate(4, 'independent', case_label='q4_independent_followup',
                                   point_count_override=original_q4['point_count']))
            cases.append(calculate(4, 'economic', count_multiplier=2,
                                   case_label='q4_economic_double_points', prefix_reference=original_q4,
                                   point_count_override=2 * original_q4['point_count']))
        else:
            for q in (1, 2, 3, 4):
                cases.append(calculate(q, 'economic'))
            if time.monotonic() - started < 18:
                cases.append(calculate(3, 'independent'))
    except TimeoutError as error:
        limitation = str(error)
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite exact ordinary-evaluation ranks of actual raw boundary rows modulo the specified entire appended old frame.',
                  frame='Two directed elementary E rows per old cross-block line pair; all 9q V_i,b rows; three X_d e_d rows; every row right-multiplied by the actual terminal K_m.',
                  boundary='The actual raw ordered Qhat_(t,s,a,b), with t=m or s=m, and the remaining blocks ascending after s; 18q columns.',
                  limitations='A full combined minor certifies finite independence modulo the appended old frame after denominator clearing. Evaluation or modular deficiencies do not give rational-function rank upper bounds. The q1 first-new containment is checked separately by its explicit constant-coefficient formula. No source-O or all-length induction assertion is made.',
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if existing is not None:
        existing['q4_followup_run'] = dict(elapsed_seconds=result['elapsed_seconds'],
                                         maximum_rss_bytes=result['maximum_rss_bytes'],
                                         bounded_limitation=limitation,
                                         original_cases_preserved=len(existing['cases']),
                                         added_case_labels=[case['case_label'] for case in cases])
        existing['cases'].extend(cases)
        result = existing
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
