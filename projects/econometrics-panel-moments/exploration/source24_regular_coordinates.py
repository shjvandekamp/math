#!/usr/bin/env python3
"""Coordinate-edge regular functionals for actual transformed source columns.

Implements paper formulas S3--S7 in research/SOURCE24_INDUCTION.md.
Single-old-line residues use a stripped last kernel, avoiding division
by effect coordinates. At the matching coordinate edge, exact dual
arithmetic divides the residue component by its vanishing X_a factor.
Gamma, lambda, and Delta are fixed linear functionals on the full source
family; their quotient interpretation is checked after old and polar
column elimination. Only the finite fixtures m=2,3 are tested.

Reproduce:
  nice -n 19 python3 exploration/source24_regular_coordinates.py --output exploration/source24-regular-coordinates-results.json
"""

import argparse
import json
from pathlib import Path
import signal

import absorbing_firstjet as dual
import normalized_sparse_source24 as sparse
import source24_residue as residue
import source24_schur as schur


P, G = residue.PRIME, schur.G
ZERO, ONE, EPS = (0, 0), (1, 0), (0, 1)
ROOT = Path(__file__).resolve().parent


def dsum(values):
    answer = ZERO
    for value in values:
        answer = dual.add(answer, value)
    return answer


def dot(row, X):
    return dsum(dual.scale(x, y) for x, y in zip(row, X))


def row_product(row, matrix):
    return [dsum(dual.mul(row[i], matrix[i][j]) for i in range(3)) for j in range(3)]


def geometry_at_point(A, line, X):
    for t in range(2, len(A)):
        for a in range(3):
            value = dot(A[t][a], X)
            if (t, a) == line:
                assert value == ZERO
            else:
                assert value[0], ('Other denominator vanishes at evaluation point.', line, t, a, X)


def edge_point(A, line, i):
    t, a = line
    j = next(k for k in range(3) if k != i)
    k = next(k for k in range(3) if k not in (i, j))
    X = [ZERO] * 3
    X[i], X[j] = EPS, ONE
    X[k] = dual.scale(-pow(A[t][a][k], -1, P),
                      dual.add(dual.scale(A[t][a][i], EPS), (A[t][a][j] % P, 0)))
    geometry_at_point(A, line, X)
    return X


def generic_points(A, line):
    t, a = line
    answer = []
    for parameter in range(2, 200):
        z = -(A[t][a][0] + A[t][a][1] * parameter) * pow(A[t][a][2], -1, P) % P
        X = [(1, 0), (parameter, 0), (z, 0)]
        if not z:
            continue
        if any(dot(A[u][c], X)[0] == 0 for u in range(2, len(A)) for c in range(3)
               if (u, c) != line):
            continue
        geometry_at_point(A, line, X)
        answer.append(X)
        if len(answer) == 2:
            return answer
    raise ValueError('No generic old-line point found in bounded search.')


def inverse_tail(AN_inverse, LN):
    return [[dual.scale(AN_inverse[i][j], LN[j]) for j in range(3)] for i in range(3)]


def kernel_or_residue(A, block, line, X, stripped):
    t, a = line
    if block == t:
        return [[(A[t][a][i] % P, 0) if stripped else dual.scale(A[t][a][i], X[i])
                 for i in range(3)] if state == a else [ZERO] * 3 for state in range(3)]
    matrix = []
    for row in A[block]:
        inverse = dual.inverse(dot(row, X))
        matrix.append([dual.scale(row[i], inverse) if stripped
                       else dual.scale(row[i], dual.mul(X[i], inverse)) for i in range(3)])
    return matrix


def transformed_word(A, line, X, word, inverse_matrix):
    product = dual.identity()
    for position, block in enumerate(word):
        matrix = kernel_or_residue(A, block, line, X, position == len(word) - 1)
        product = dual.mmul(product, matrix)
    return dual.mmul(product, inverse_matrix)


def source_and_aux_residues(A, AN_inverse, line, X, source_labels, aux_labels):
    """Compute Res_(old line)(F K_N^-1), without inverse X coordinates."""
    t, a = line
    N = len(A) - 1
    LN = [dot(row, X) for row in A[N]]
    inverse_matrix = inverse_tail(AN_inverse, LN)
    words = {}
    for shared, first, _, _ in source_labels:
        if (shared, first) in words:
            continue
        word = [first] + [u for u in range(2, len(A)) if u not in (shared, first)]
        words[shared, first] = transformed_word(A, line, X, word, inverse_matrix)
    values = []
    for shared, first, d, b in source_labels:
        if shared == t and d != a:
            values.append([ZERO] * 3)
            continue
        product = words[shared, first]
        if shared == t:
            scalar = dual.scale(A[shared][d][b], X[d])
            vector = [dual.mul(scalar, dual.sub(inverse_matrix[b][i], dual.mul(X[b], product[b][i])))
                      for i in range(3)]
        else:
            scalar = dual.scale(-A[shared][d][b],
                                dual.mul(dual.mul(X[d], X[b]), dual.inverse(dot(A[shared][d], X))))
            vector = [dual.mul(scalar, value) for value in product[b]]
        assert dsum(vector) == ZERO
        values.append(vector)
    H = [[dual.sub(inverse_matrix[b][i], X[b] if i == b else ZERO) for i in range(3)]
         for b in range(3)]
    assert all(dsum(row) == ZERO for row in H)
    # The stripped one-block word N gives J_N*(A_N^-1 diag L_N)=I.
    assert transformed_word(A, line, X, [N], inverse_matrix) == dual.identity()
    for label in aux_labels:
        if label[0] == 'C' and label[1:3] == line:
            _, u, c, b = label
            scalar = dual.scale(A[u][c][b], X[c])
            values.append([dual.mul(scalar, value) for value in H[b]])
        elif label[0] == 'E_transformed' and label[1:3] == line:
            row = row_product([(value % P, 0) for value in A[t][a]], inverse_matrix)
            values.append([dual.scale(-1, dual.mul(X[a], value)) for value in row])
        else:
            values.append([ZERO] * 3)
    return values, H, LN


def setup_schur(m, numerator, denominator, saved):
    T = m + 3
    epsilon = numerator * pow(denominator, -1, P) % P
    old_times = sparse.factors(m, 'economic')
    AN = [[1, row[1] * epsilon % P, row[2] * pow(epsilon, 3, P) % P] for row in G]
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, old_times) + [AN]
    R, geometry = residue.residue_matrix(T, A, P)
    blocks, partition = schur.partition(R, T)
    Oinv, _ = schur.invert(blocks['O'])
    Pinv, _ = schur.invert(blocks['P'])
    AN_inverse, _ = schur.invert(AN)
    U = schur.matrix_product(Pinv, blocks['Q'])
    V = schur.matrix_product(Oinv, blocks['D'])
    W = schur.matrix_product(Oinv, blocks['E'])
    old_coefficients = schur.matrix_difference(schur.matrix_product(V, U), W)
    size = len(blocks['P'])
    ordered_coefficients = (old_coefficients + [[-x % P for x in row] for row in U]
                            + [[int(i == j) for j in range(size)] for i in range(size)])
    coefficients = [None] * len(R)
    for row, canonical_column in zip(ordered_coefficients, partition['column_permutation_new_to_original']):
        coefficients[canonical_column] = row
    eliminated = schur.matrix_product(R, coefficients)
    ordered_rows = [eliminated[i] for i in partition['row_permutation_new_to_original']]
    assert not any(value for row in ordered_rows[:-size] for value in row)
    H = ordered_rows[-size:]
    saved_case = next(case for case in saved['cases'] if case['old_block_count'] == m
                      and case['new_epsilon'] == f'{numerator}/{denominator}')
    assert residue.matrix_hash(R) == saved_case['full_residue_sha256']
    assert H == saved_case['H_matrix']
    return A, AN_inverse, R, blocks, partition, coefficients, H, U, geometry


def delta_matrix(A, AN_inverse, source_labels, coefficients):
    old_blocks = list(range(2, len(A) - 1))
    C_labels = [('C', t, a, b) for t in old_blocks for a in range(3) for b in range(3)]
    E_labels = [('E_transformed', t, a) for t in old_blocks for a in range(3)]
    aux_labels = C_labels + E_labels + [('H', b) for b in range(3)]
    source_count, column_count = len(source_labels), len(source_labels) + len(aux_labels)
    AN = A[-1]
    Delta, point_records = [], []
    for t in old_blocks:
        for a in range(3):
            line = (t, a)
            eta = [[0] * 3 for _ in range(column_count)]
            edges = []
            for i in range(3):
                X = edge_point(A, line, i)
                values, _, LN = source_and_aux_residues(A, AN_inverse, line, X, source_labels, aux_labels)
                edges.append([value[0] for value in X])
                for col, vector in enumerate(values):
                    if i == a:
                        assert vector[a][0] == 0
                        eta[col][i] = vector[a][1] * pow(LN[a][0], -1, P) % P
                    else:
                        eta[col][i] = vector[i][0] * pow(X[a][0] * LN[i][0], -1, P) % P
            gamma = schur.matrix_product(eta, AN)
            points = generic_points(A, line)
            values0, H0, _ = source_and_aux_residues(A, AN_inverse, line, points[0], source_labels, aux_labels)
            Xa_inverse = pow(points[0][a][0], -1, P)
            v0_inverse = pow(A[t][a][0] * points[0][0][0], -1, P)
            lambdas = [((vector[0][0] * Xa_inverse
                         - sum(gamma[col][b] * H0[b][0][0] for b in range(3))) * v0_inverse) % P
                       for col, vector in enumerate(values0)]
            for b in range(3):
                coefficient_inverse = pow(A[t][a][b], -1, P)
                Delta.append([(gamma[col][b] * coefficient_inverse - lambdas[col]) % P
                              for col in range(column_count)])
            # The linear divided-residue decomposition is checked on the
            # eliminated source columns, not asserted on each raw source.
            for point_index, X in enumerate(points):
                values, Hb, _ = ((values0, H0, None) if point_index == 0 else
                                 source_and_aux_residues(A, AN_inverse, line, X, source_labels, aux_labels))
                invXa = pow(X[a][0], -1, P)
                errors = [[(values[col][i][0] * invXa
                            - sum(gamma[col][b] * Hb[b][i][0] for b in range(3))
                            - lambdas[col] * A[t][a][i] * X[i][0]) % P
                           for col in range(column_count)] for i in range(3)]
                assert not any(value for row in schur.matrix_product([row[:source_count] for row in errors], coefficients)
                               for value in row)
                assert not any(value for row in errors for value in row[source_count:])
            point_records.append(dict(old_line=line, edge_points_mod_prime=edges,
                                      generic_points_mod_prime=[[value[0] for value in X] for X in points]))
    size = len(C_labels)
    assert [[row[source_count + j] for j in range(size)] for row in Delta] == [
        [int(i == j) for j in range(size)] for i in range(size)]
    assert not any(value for row in Delta for value in row[source_count + size:])
    return [row[:source_count] for row in Delta], point_records


def raw_new_half_diagnostic(blocks, partition, H, PinvQ):
    row_states = [label[3] for label in partition['beta_row_labels']]
    shared_states = [label[2] for label in partition['shared_new_column_labels']]
    first_states = [label[3] for label in partition['first_new_column_labels']]
    for name, states in (('P', shared_states), ('Q', first_states), ('R', shared_states), ('S', first_states)):
        assert all(value == 0 for i, row in enumerate(blocks[name]) for j, value in enumerate(row)
                   if row_states[i] != states[j])
    H0 = schur.matrix_difference(blocks['S'], schur.matrix_product(blocks['R'], PinvQ))
    assert all(value == 0 for i, row in enumerate(H0) for j, value in enumerate(row)
               if row_states[i] != first_states[j])
    local_ranks = []
    for state in range(3):
        rr = [i for i, a in enumerate(row_states) if a == state]
        cc = [i for i, a in enumerate(first_states) if a == state]
        local_ranks.append(residue.modular_rank([[H0[i][j] for j in cc] for i in rr], P)['rank'])
    feedback = schur.matrix_difference(H, H0)
    return dict(raw_new_blocks_diagonal_by_new_line_state=True,
                H0_definition='S-R*P^-1*Q, before eliminating old columns.',
                H0_rank=residue.modular_rank(H0, P)['rank'], H0_state_block_ranks=local_ranks,
                full_H_rank=residue.modular_rank(H, P)['rank'],
                old_feedback_rank=residue.modular_rank(feedback, P)['rank'],
                H0_sha256=residue.matrix_hash(H0), old_feedback_sha256=residue.matrix_hash(feedback),
                full_H_nonzero_entries_between_different_new_states=sum(
                    bool(value) for i, row in enumerate(H) for j, value in enumerate(row)
                    if row_states[i] != first_states[j]))


def check_case(m, numerator, denominator, saved):
    A, AN_inverse, R, blocks, partition, coefficients, H, U, geometry = setup_schur(m, numerator, denominator, saved)
    _, source_labels = schur.canonical_labels(len(A))
    Delta, points = delta_matrix(A, AN_inverse, source_labels, coefficients)
    H_Delta = schur.matrix_product(Delta, coefficients)
    J = []
    for t in range(2, len(A) - 1):
        for a in range(3):
            for b in range(3):
                X = residue.cross(A[t][a], A[-1][b], P)
                scalar = -A[t][a][b] * X[a] * X[b] % P
                assert scalar
                J.append(scalar)
    assert H == [[J[i] * value % P for value in row] for i, row in enumerate(H_Delta)]
    diagnostic = raw_new_half_diagnostic(blocks, partition, H, U)
    result = dict(old_blocks=m, source_panel_T=m + 3, prime=P, G=G,
                  epsilon=f'{numerator}/{denominator}', new_time_exponent=3,
                  parameter_scope='Old economic factors; the new block has v=u^3. This is a positive rational independent-time fixture.',
                  old_line_and_edge_geometry_checked=True, cross_pair_geometry=geometry,
                  evaluation_points=points, canonical_C_Delta_identity_verified=True,
                  transformed_old_E_Delta_zero_verified=True, new_polynomial_H_Delta_zero_verified=True,
                  matching_coordinate_division_verified_by_dual_arithmetic=True,
                  divided_residue_linear_decomposition_verified_after_elimination_at_two_points=True,
                  source_Delta_sha256=residue.matrix_hash(Delta),
                  elimination_coefficients_sha256=residue.matrix_hash(coefficients),
                  H_Delta_matrix=H_Delta, H_Delta_sha256=residue.matrix_hash(H_Delta),
                  raw_beta_diagonal_J=J, raw_H_sha256=residue.matrix_hash(H),
                  saved_schur_H_reproduced=True, H_equals_diag_J_times_H_Delta_verified=True,
                  new_half_diagnostic=diagnostic)
    print(json.dumps(dict(m=m, epsilon=result['epsilon'], Delta_comparison_verified=True,
                          H0_rank=diagnostic['H0_rank'], H_rank=diagnostic['full_H_rank'],
                          feedback_rank=diagnostic['old_feedback_rank'])), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Regular-coordinate checks exceeded 28 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    saved = json.loads((ROOT / 'source24-schur-results.json').read_text())
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(28)
    cases = [check_case(m, numerator, denominator, saved) for m in (2, 3)
             for numerator, denominator in ((1, 7), (2, 11))]
    _, _, _, blocks, partition, _, H, U, _ = setup_schur(4, 1, 7, saved)
    additional = raw_new_half_diagnostic(blocks, partition, H, U)
    print(json.dumps(dict(additional_m4_raw_new_diagnostic=additional)), flush=True)
    signal.alarm(0)
    result = dict(status='External exact modular verification of paper regular-coordinate identities; no Lean or all-length determinant theorem.',
                  source_residue_method='Strip the final kernel: F*diag(X)^-1=A_t(a,b)*X_a/L_ta*[e_b-X_b*e_b*P_prefix*diag(L_last)^-1*A_last], then multiply by A_N^-1*diag(L_N).',
                  coordinate_method='At each old line use the three coordinate-edge points to obtain eta, gamma=eta*A_N, and one generic point to recover lambda; Delta_b=gamma_b/A_t(a,b)-lambda.',
                  quotient_check='Apply exactly the old/polar source-column elimination from source24_schur; check raw H=diag(J)*Delta_eliminated with J=-A_t(a,b)*X_a*X_b at the corresponding old/new crosspoint.',
                  limitations='The code checks m=2,3 and the displayed finite rational fixtures modulo one prime. The m=4 extra check concerns only raw new-block ranks. No arbitrary-length nonvanishing follows.',
                  cases=cases, additional_m4_epsilon_one_seventh_new_half_diagnostic=additional)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
