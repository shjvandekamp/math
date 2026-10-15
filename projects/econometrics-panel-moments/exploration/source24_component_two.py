#!/usr/bin/env python3
"""Component-two observation ranks on the actual binary-quotient subspace N.

Use the actual pair-source matrix O and the exact axis values T0. Convert
each alpha/beta pair to its third vector component, then append T_(i,2).
N has the generators in SOURCE24_BINARY_QUOTIENT: first-slot differences,
long empty rows, and selected output-zero rows. The long empty rows include
their local E term, whose pair residues vanish and whose axis value is -1.

The empty-row observations are independently computed from the complete
ordered transition word. Also check B25--B37's parity block, seed subtraction,
odd inverse projection, and even left-kernel residual directions. All
certificates are finite-field statements at
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


def long_empty_blocks(m, A, lines, BL):
    """B27/B28 and the actual two-state residue scaling B29."""
    old = list(range(2, m + 2))
    index = {line: j for j, line in enumerate(lines)}
    D, jet_checks = [], 0
    for u in old:
        X = (0, 1, -A[u][0][1] * pow(A[u][0][2], -1, P) % P)
        diagonal = -1
        for t in old:
            if t != u:
                K = residue.ordinary_kernel(A, t, X, P)
                determinant = (K[1][1] * K[2][2] - K[1][2] * K[2][1]) % P
                assert determinant
                diagonal = diagonal * determinant % P
        assert diagonal
        D.append(diagonal)
        for t in old:
            assert BL[index[u, 0]][index[t, 0]] == diagonal * int(u == t) % P
            for c in (1, 2):
                assert BL[index[u, c]][index[t, 0]] == 0

        # B28 uses its stated chart X0=x, X2=1, with L_(u,0)=0 exactly.
        inverse_a1 = pow(A[u][0][1], -1, P)
        Xjet = [(0, 1),
                (-A[u][0][2] * inverse_a1 % P, -inverse_a1 % P), dual.ONE]
        regular.geometry_at_point(A, (u, 0), Xjet)
        kernels = {t: regular.kernel_or_residue(A, t, (u, 0), Xjet, False) for t in old}
        for t in old:
            product = dual.identity()
            for block in residue.ordered_word(old, t):
                product = dual.mmul(product, kernels[block])
            for a in (1, 2):
                numerator = dual.mul(Xjet[a], product[a][2])
                assert numerator[0] == 0
                value = -numerator[1] * pow(A[u][0][2], -1, P) % P
                assert value == BL[index[u, 0]][index[t, a]], ('B28 row-zero jet mismatch.', m, u, t, a)
                jet_checks += 1

    binary_labels = [(t, a) for t in old for a in (1, 2)]
    Mres, checks = [], 0
    for u, c in binary_labels:
        z = -A[u][c][1] * pow(A[u][c][2], -1, P) % P
        kernels = {}
        for t in old:
            rows = []
            for a in (1, 2):
                numerator = [A[t][a][1] % P, A[t][a][2] * z % P]
                if t == u:
                    rows.append(numerator if a == c else [0, 0])
                else:
                    inverse = pow(sum(numerator) % P, -1, P)
                    rows.append([x * inverse % P for x in numerator])
            kernels[t] = rows
        products = {}
        for t in old:
            product = [[1, 0], [0, 1]]
            for block in residue.ordered_word(old, t):
                product = residue.matmul(product, kernels[block], P)
            products[t] = product
        row = []
        for t, a in binary_labels:
            value = (1 if a == 1 else z) * products[t][a - 1][1] % P
            row.append(value)
            denominator = A[u][c][2] * (1 if c == 1 else z) * z % P
            assert -value * pow(denominator, -1, P) % P == BL[index[u, c]][index[t, a]], ('B29 binary residue scaling failed.', m, u, c, t, a)
            checks += 1
        Mres.append(row)
    return dict(B27_nonzero_diagonal=D, B27_lower_left_zero=True,
                B28_row_zero_chart_first_jet_entries=jet_checks,
                B29_binary_residue_entries=checks,
                actual_binary_residue_matrix=incoming.matrix_certificate(Mres),
                binary_row_and_column_labels=binary_labels)


def parity_reduction(m, A, observations, N_observations, labels, lines, pair_count, empty_indices, full_rank):
    """Keep the actual selected rows and local-E correction in B25--B37."""
    empty_columns = [empty_indices[line] for line in lines]
    selected = {(label['t'], label['a']): j for j, label in enumerate(labels)
                if label['kind'] == 'selected_output_zero'}
    diff_columns = [j for j, label in enumerate(labels) if label['kind'] == 'first_slot_difference']
    AL = [[row[j] for j in empty_columns] for row in N_observations[:pair_count]]
    BL = [[row[j] for j in empty_columns] for row in N_observations[pair_count:]]
    BLcertificate = incoming.matrix_certificate(BL)
    expected_rank = 3 * m if m % 2 else 3 * m - 2
    assert BLcertificate['rank_certificate']['rank'] == expected_rank, ('B30 long-empty parity failed.', m)
    block_checks = long_empty_blocks(m, A, lines, BL)
    assert block_checks['actual_binary_residue_matrix']['rank_certificate']['rank'] == expected_rank - m

    seed_coefficients, _, seed_labels, constants = differences.seed_coefficients(m, A)
    assert seed_labels == lines and all(row[0] == 1 for table in A[2:] for row in table)
    by_label = {(entry['t'], entry['A']): entry for entry in constants}
    seed_observations = []
    for row in N_observations:
        seed_observations.append([(row[selected[t, a]] - by_label[t, a]['c_tA']
                                   * row[empty_indices[by_label[t, a]['r'], 0]]) % P for t, a in lines])
    rho2_U = schur.matrix_product(observations[:pair_count], seed_coefficients)
    assert seed_observations[:pair_count] == rho2_U
    assert seed_observations[pair_count:] == [[0] * (3 * m) for _ in lines], 'B32 seed T2 cancellation failed.'
    result = dict(B_L=BLcertificate, expected_B_L_parity_rank=expected_rank,
                  A_L_sha256=residue.matrix_hash(AL), block_checks=block_checks,
                  selected_minus_c_long_empty_T2_zero=True,
                  selected_minus_c_long_empty_pair_equals_actual_rho2_U=True,
                  rho2_U_sha256=residue.matrix_hash(rho2_U), seed_constants=constants)
    axis_differences = [[row[j] for j in diff_columns] for row in N_observations[pair_count:]]
    if m % 2:
        inverse, inverse_certificate = schur.invert(BL)
        projection_correction = schur.matrix_product(schur.matrix_product(AL, inverse), N_observations[pair_count:])
        projected = schur.matrix_difference(N_observations[:pair_count], projection_correction)
        assert all(row[j] == 0 for row in projected for j in empty_columns)
        assert [[row[selected[line]] for line in lines] for row in projected] == rho2_U
        remaining = [seed_row + [row[j] for j in diff_columns] for seed_row, row in zip(rho2_U, projected)]
        certificate = incoming.matrix_certificate(remaining)
        assert full_rank == 3 * m + certificate['rank_certificate']['rank'], 'B35 exact elimination rank identity failed.'
        result.update(odd_B_L_inverse=inverse_certificate,
                      odd_projected_all_generators_sha256=residue.matrix_hash(projected),
                      odd_projected_empty_columns_zero=True,
                      odd_projected_selected_columns_equal_rho2_U=True,
                      B35_remaining_matrix=certificate, B35_rank_identity_verified=True,
                      B35_expected_remaining_rank=full_rank - 3 * m)
    else:
        right_pivots, right_free, right_vectors = dual.rref_kernel(BL)
        left_pivots, left_free, left_vectors = dual.rref_kernel([list(row) for row in zip(*BL)])
        assert len(right_vectors) == len(left_vectors) == 2
        RL = [list(row) for row in zip(*right_vectors)]
        compatibility = schur.matrix_product(AL, RL)
        residual = schur.matrix_product(left_vectors, axis_differences)
        residual_certificate = incoming.matrix_certificate(residual)
        assert residual_certificate['rank_certificate']['rank'] == 2, 'B37 pure-axis directions were not resolved at this fixture.'
        selected_axis = [[row[selected[line]] for line in lines] for row in N_observations[pair_count:]]
        assert schur.matrix_product(left_vectors, selected_axis) == [[0] * (3 * m) for _ in range(2)]
        result.update(even_right_kernel_vectors=right_vectors, even_right_free_columns=right_free,
                      even_left_kernel_vectors=left_vectors, even_left_free_columns=left_free,
                      even_kernel_dimensions_verified=True,
                      B36_A_L_times_right_kernel=incoming.matrix_certificate(compatibility),
                      B37_left_kernel_times_difference_axis=residual_certificate,
                      even_selected_columns_leave_left_kernel_directions_unconstrained=True,
                      even_first_slot_differences_resolve_both_axis_directions=True)
    return result


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
    parity = parity_reduction(m, A, observations, N_observations, labels, lines, pair_count, empty_indices, rank)
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
                  parity_annihilator_reduction=parity,
                  pair_row_labels=pair_labels, axis_row_labels=lines, N_generator_labels=labels,
                  interpretation='The displayed kernel dimension is over F_p for the actual N coefficient map. Identifying it with N intersect W01 uses the separate observation-kernel theorem.',
                  elapsed_seconds=time.monotonic() - started)
    if full:
        assert k - rank == pair_count - 6 * m
    print(json.dumps(dict(m=m, source_rank=old_rank, N_generators=k, observation_rank=rank,
                          target=target, kernel_dimension=k - rank, full_row_rank=full,
                          long_empty_axis_rank=parity['B_L']['rank_certificate']['rank'],
                          odd_remaining_rank=parity.get('B35_expected_remaining_rank'),
                          even_axis_residual_rank=parity.get('B37_left_kernel_times_difference_axis', {}).get('rank_certificate', {}).get('rank'),
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
                  parity_checks='B27 triangular block and B28 chart jets; actual binary residue scaling B29 and rank B30; seed identity B32; odd projection and rank identity B33--B35; even kernel compatibility and residual rank B36--B37.',
                  limitations='Nonzero minors lift after clearing denominators. Modular deficiencies alone are not real rank upper bounds. W01 identification and uniform surjectivity are not proved here.',
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
