#!/usr/bin/env python3
"""Component-two observation ranks on the actual binary-quotient subspace N.

Use the actual pair-source matrix O and the exact axis values T0. Convert
each alpha/beta pair to its third vector component, then append T_(i,2).
N has the generators in SOURCE24_BINARY_QUOTIENT: first-slot differences,
long empty rows, and selected output-zero rows. The long empty rows include
their local E term, whose pair residues vanish and whose axis value is -1.

The empty-row observations are independently computed from the complete
ordered transition word. All certificates are finite-field statements at
the specified m=3,4,5 fixtures, not an all-length rank theorem or a proof of
the separate identification of the observation kernel with W01.

Reproduce:
  nice -n 19 python3 exploration/source24_component_two.py --output exploration/source24-component-two-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming
import source24_residue_differences as differences


P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
dual, regular = incoming.dual, incoming.regular


def source_observations(m, A, O, T0):
    """Preserve the exact cross-point representatives used to construct O."""
    residue_labels, columns = schur.canonical_labels(m + 2)
    pair_rows, pair_labels = [], []
    for row in range(0, len(residue_labels), 2):
        u, v, c, d, coordinate = residue_labels[row]
        assert coordinate == 'alpha'
        assert residue_labels[row + 1] == (u, v, c, d, 'beta')
        X = residue.cross(A[u][c], A[v][d], P)
        U2, V2 = A[u][c][2] * X[2] % P, A[v][d][2] * X[2] % P
        pair_rows.append([(U2 * x + V2 * y) % P for x, y in zip(O[row], O[row + 1])])
        pair_labels.append((u, v, c, d))
    lines = [(u, c) for u in range(2, m + 2) for c in range(3)]
    T2 = [T0[3 * i + 2] for i in range(len(lines))]
    assert len(pair_rows) == 9 * m * (m - 1) // 2
    assert len(T0) == 3 * len(lines)
    assert all(len(row) == len(columns) for row in pair_rows + T2)
    return pair_rows + T2, pair_labels, lines, columns


def generators(m, columns):
    """Actual source coefficients and the independent local E correction."""
    old = list(range(2, m + 2))
    index = {label: j for j, label in enumerate(columns)}
    first = {t: min(s for s in old if s != t) for t in old}
    labels, terms, gauge = [], [], []
    for t in old:
        for s in old:
            if s in (t, first[t]):
                continue
            for a in range(3):
                for b in range(3):
                    labels.append(dict(kind='first_slot_difference', t=t, s=s, r=first[t], a=a, b=b))
                    terms.append([(index[t, s, a, b], 1), (index[t, first[t], a, b], -1)])
                    gauge.append(None)
    difference_count = len(labels)
    empty_indices = {}
    for t in old:
        for a in range(3):
            empty_indices[t, a] = len(labels)
            labels.append(dict(kind='long_empty', t=t, r=first[t], a=a))
            terms.append([(index[t, first[t], a, b], 1) for b in range(3)])
            gauge.append((t, a))
    for t in old:
        for a in range(3):
            labels.append(dict(kind='selected_output_zero', t=t, r=first[t], a=a, b=0))
            terms.append([(index[t, first[t], a, 0], 1)])
            gauge.append(None)
    assert difference_count == 9 * m * (m - 2)
    assert len(terms) == len(columns) - 3 * m
    C = [[0] * len(terms) for _ in columns]
    for j, entries in enumerate(terms):
        for i, scalar in entries:
            C[i][j] = (C[i][j] + scalar) % P
    return labels, terms, gauge, empty_indices, C


def apply_generators(matrix, terms):
    return [[sum(scalar * row[i] for i, scalar in entries) % P for entries in terms]
            for row in matrix]


def check_empty_pairs(m, A, pair_labels, N_observations, empty_indices):
    """Direct residue of Xa*(e_a - K_t*ascending_remaining), component 2."""
    old = list(range(2, m + 2))
    checks = 0
    for row, (u, v, c, d) in enumerate(pair_labels):
        X = residue.cross(A[u][c], A[v][d], P)
        assert all(X)
        U = [A[u][c][i] * X[i] % P for i in range(3)]
        V = [A[v][d][i] * X[i] % P for i in range(3)]
        kernels = {}
        for k in old:
            if k == u:
                kernels[k] = [U[:] if a == c else [0, 0, 0] for a in range(3)]
            elif k == v:
                kernels[k] = [V[:] if a == d else [0, 0, 0] for a in range(3)]
            else:
                kernels[k] = residue.ordinary_kernel(A, k, X, P)
        for t in old:
            product = residue.word_product(kernels, residue.ordered_word(old, t), P)
            for a in range(3):
                value = -X[a] * product[a][2] % P
                assert N_observations[row][empty_indices[t, a]] == value, (
                    'Long-empty pair component disagrees with the direct word.', m, u, v, c, d, t, a)
                checks += 1
    return checks


def check_empty_axis(m, A, lines, pair_count, N_observations, empty_indices):
    """Direct divided component residue; one exact jet removes X0 when c=0."""
    old = list(range(2, m + 2))
    checks, derivative_checks = 0, 0
    for row, (u, c) in enumerate(lines):
        line = (u, c)
        X = regular.edge_point(A, line, 0)
        kernels = {k: regular.kernel_or_residue(A, k, line, X, False) for k in old}
        stripped = {k: regular.kernel_or_residue(A, k, line, X, True) for k in old}
        for t in old:
            word = residue.ordered_word(old, t)
            product = dual.identity()
            for position, k in enumerate(word):
                product = dual.mmul(product, stripped[k] if position == len(word) - 1 else kernels[k])
            for a in range(3):
                divided_residue = dual.scale(-1, dual.mul(X[a], product[a][2]))
                if c == 0:
                    assert divided_residue[0] == 0
                    value = divided_residue[1] * pow(A[u][c][2], -1, P) % P
                    derivative_checks += 1
                else:
                    value = divided_residue[0] * pow(A[u][c][2] * X[c][0] % P, -1, P) % P
                assert N_observations[pair_count + row][empty_indices[t, a]] == value, (
                    'Long-empty T_i2 disagrees with the direct word and local E sign.', m, u, c, t, a)
                checks += 1
    return checks, derivative_checks


def calculate(m):
    started = time.monotonic()
    times = sparse.factors(m, 'economic')
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    geometry = differences.check_geometry(m, A)
    O, source_geometry = residue.residue_matrix(m + 2, A, P)
    _, _, T0 = incoming.feedback_limit(m, A)
    observations, pair_labels, lines, columns = source_observations(m, A, O, T0)
    labels, terms, gauge, empty_indices, C = generators(m, columns)
    N_observations = apply_generators(observations, terms)
    pair_count = len(pair_labels)
    for i, line in enumerate(lines):
        for j, local_E in enumerate(gauge):
            if local_E == line:
                N_observations[pair_count + i][j] = (N_observations[pair_count + i][j] - 1) % P
    pair_checks = check_empty_pairs(m, A, pair_labels, N_observations, empty_indices)
    axis_checks, derivative_checks = check_empty_axis(m, A, lines, pair_count, N_observations, empty_indices)

    old_certificate = incoming.matrix_certificate(O)
    coefficient_certificate = incoming.matrix_certificate(C)
    observation_certificate = incoming.matrix_certificate(N_observations)
    n, k, target = len(columns), len(labels), pair_count + 3 * m
    old_rank = old_certificate['rank_certificate']['rank']
    coefficient_rank = coefficient_certificate['rank_certificate']['rank']
    rank = observation_certificate['rank_certificate']['rank']
    assert old_rank == n, 'This fixture does not have independent actual old source columns.'
    assert coefficient_rank == k, 'Listed N generators do not have independent source coefficients.'
    full = rank == target
    result = dict(m=m, prime=P, G=G, time_fixture='economic', time_factors=times,
                  geometry=geometry, actual_source_geometry=source_geometry,
                  actual_source_matrix=old_certificate, N_source_coefficient_matrix=coefficient_certificate,
                  source_observation_matrix_sha256=residue.matrix_hash(observations),
                  N_component_two_observations=observation_certificate,
                  scalar_pair_rows=pair_count, axis_rows=3 * m, target_observation_rank=target,
                  N_generator_count=k, N_generators_independent_at_fixture=True,
                  first_slot_difference_count=9 * m * (m - 2), long_empty_count=3 * m,
                  selected_output_zero_count=3 * m,
                  observation_map_full_row_rank=full,
                  observation_cokernel_dimension=target - rank,
                  exact_modular_coefficient_kernel_dimension=k - rank,
                  expected_kernel_dimension_if_surjective=pair_count - 6 * m,
                  direct_empty_word_pair_component_checks=pair_checks,
                  direct_empty_word_axis_component_checks=axis_checks,
                  removable_X0_first_jet_checks=derivative_checks,
                  local_E_axis_correction_included=True,
                  pair_row_labels=pair_labels, axis_row_labels=lines, N_generator_labels=labels,
                  interpretation='The displayed kernel dimension is over F_p for the actual N coefficient map. Identifying it with N intersect W01 uses the separate observation-kernel theorem.',
                  elapsed_seconds=time.monotonic() - started)
    if full:
        assert k - rank == pair_count - 6 * m
    print(json.dumps(dict(m=m, source_rank=old_rank, N_generators=k, observation_rank=rank,
                          target=target, kernel_dimension=k - rank, full_row_rank=full,
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second component-two cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB component-two RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation = None
    current_m = None
    try:
        for current_m in (3, 4, 5):
            cases.append(calculate(current_m))
    except TimeoutError as error:
        limitation = dict(m=current_m, reason=str(error))
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Exact modular component-two observation certificates on actual N generators; no all-length theorem.',
                  normalization='Pair rows use raw component 2 at the same oriented cross points as O; axis rows use T_(i,2) from feedback_limit. Long empty rows include T_(i,2)(E_ta)=-delta_(i,(t,a)).',
                  independent_check='Every long-empty pair and axis observation is independently evaluated from its full t-first ordered transition word, including the removable X0 first jet.',
                  limitations='Nonzero minors lift after clearing denominators. Modular deficiencies alone are not real rank upper bounds. W01 identification and uniform surjectivity are not proved here.',
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
