#!/usr/bin/env python3
"""Exact modular Schur split of the actual equation (24) residue matrix.

Rows are reordered as old-old pairs (both coordinates), old-new alpha
(coefficient of the old residue vector), and old-new beta. Columns are
old-old indices, shared-new indices t=N, and first-new indices s=N.
The resulting matrix is [[O,D,E],[0,P,Q],[B,R,S]].

Where O and P are invertible, compute
H=S-B*O^-1*E-(R-B*O^-1*D)*P^-1*Q and verify its determinant factorization
against the full residue matrix, including both permutation signs.
This is finite exact modular evidence, not an all-length theorem.

Reproduce:
  nice -n 19 python3 exploration/source24_schur.py --output exploration/source24-schur-results.json
"""

import argparse
import itertools as it
import json
from pathlib import Path
import signal

import normalized_sparse_source24 as sparse
import source24_residue as residue


P = residue.PRIME
G = ((1, 1, 1), (1, 30, 10), (1, 3, 2))


def matrix_product(a, b):
    assert a and b and len(a[0]) == len(b)
    columns = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, column)) % P for column in columns]
            for row in a]


def matrix_difference(a, b):
    assert len(a) == len(b) and len(a[0]) == len(b[0])
    return [[(x - y) % P for x, y in zip(row_a, row_b)] for row_a, row_b in zip(a, b)]


def invert(matrix):
    """Gauss-Jordan inverse and determinant, independently checked by A*A^-1."""
    n = len(matrix)
    assert n and all(len(row) == n for row in matrix)
    a = [[value % P for value in row] + [int(i == j) for j in range(n)]
         for i, row in enumerate(matrix)]
    determinant, selected_rows, row_ids = 1, [], list(range(n))
    for c in range(n):
        found = next((i for i in range(c, n) if a[i][c]), None)
        if found is None:
            return None
        if found != c:
            a[c], a[found] = a[found], a[c]
            row_ids[c], row_ids[found] = row_ids[found], row_ids[c]
            determinant = -determinant
        selected_rows.append(row_ids[c])
        pivot = a[c][c]
        determinant = determinant * pivot % P
        inverse_pivot = pow(pivot, -1, P)
        a[c] = [x * inverse_pivot % P for x in a[c]]
        for i in range(n):
            if i != c and a[i][c]:
                factor = a[i][c]
                a[i] = [(x - factor * y) % P for x, y in zip(a[i], a[c])]
    inverse = [row[n:] for row in a]
    identity = [[int(i == j) for j in range(n)] for i in range(n)]
    assert [row[:n] for row in a] == identity
    assert matrix_product(matrix, inverse) == identity
    return inverse, dict(size=n, determinant_mod_prime=determinant,
                         pivot_rows_in_original_order=selected_rows,
                         pivot_columns=list(range(n)), inverse_checked=True,
                         inverse_sha256=residue.matrix_hash(inverse))


def permutation_sign(permutation):
    assert sorted(permutation) == list(range(len(permutation)))
    seen, cycles = set(), 0
    for i in range(len(permutation)):
        if i in seen:
            continue
        cycles += 1
        j = i
        while j not in seen:
            seen.add(j)
            j = permutation[j]
    return -1 if (len(permutation) - cycles) % 2 else 1


def canonical_labels(T):
    blocks = list(range(2, T))
    rows = [(u, v, c, d, coordinate) for u, v in it.combinations(blocks, 2)
            for c, d in it.product(range(3), repeat=2) for coordinate in ('alpha', 'beta')]
    columns = [(t, s, a, b) for t in blocks for s in blocks if t != s
               for a in range(3) for b in range(3)]
    return rows, columns


def partition(matrix, T):
    rows, columns = canonical_labels(T)
    N = T - 1
    old_rows = [i for i, label in enumerate(rows) if label[1] != N]
    alpha_rows = [i for i, label in enumerate(rows) if label[1] == N and label[-1] == 'alpha']
    beta_rows = [i for i, label in enumerate(rows) if label[1] == N and label[-1] == 'beta']
    old_columns = [i for i, label in enumerate(columns) if N not in label[:2]]
    shared_columns = [i for i, label in enumerate(columns) if label[0] == N]
    first_columns = [i for i, label in enumerate(columns) if label[1] == N]
    row_permutation = old_rows + alpha_rows + beta_rows
    column_permutation = old_columns + shared_columns + first_columns
    assert len(old_rows) == len(old_columns)
    assert len(alpha_rows) == len(beta_rows) == len(shared_columns) == len(first_columns)

    def block(rr, cc):
        return [[matrix[i][j] for j in cc] for i in rr]

    blocks = dict(O=block(old_rows, old_columns), D=block(old_rows, shared_columns),
                  E=block(old_rows, first_columns), zero=block(alpha_rows, old_columns),
                  P=block(alpha_rows, shared_columns), Q=block(alpha_rows, first_columns),
                  B=block(beta_rows, old_columns), R=block(beta_rows, shared_columns),
                  S=block(beta_rows, first_columns))
    assert not any(value for row in blocks['zero'] for value in row)
    labels = dict(row_permutation_new_to_original=row_permutation,
                  column_permutation_new_to_original=column_permutation,
                  row_permutation_sign=permutation_sign(row_permutation),
                  column_permutation_sign=permutation_sign(column_permutation),
                  old_coordinate_rows=len(old_rows), new_alpha_rows=len(alpha_rows),
                  new_beta_rows=len(beta_rows),
                  alpha_row_labels=[rows[i][:-1] for i in alpha_rows],
                  beta_row_labels=[rows[i][:-1] for i in beta_rows],
                  shared_new_column_labels=[columns[i] for i in shared_columns],
                  first_new_column_labels=[columns[i] for i in first_columns])
    return blocks, labels


def check_old_transport(T, A, O):
    """Verify O is the previous residue matrix with local K_N changes of basis."""
    old_matrix, _ = residue.residue_matrix(T - 1, A[:-1], P)
    old_rank = residue.modular_rank(old_matrix, P)
    determinants, position = [], 0
    for u, v in it.combinations(range(2, T - 1), 2):
        for c, d in it.product(range(3), repeat=2):
            X = residue.cross(A[u][c], A[v][d], P)
            U = [A[u][c][i] * X[i] % P for i in range(3)]
            V = [A[v][d][i] * X[i] % P for i in range(3)]
            kernel = residue.ordinary_kernel(A, T - 1, X, P)
            moved = residue.matmul([U, V], kernel, P)
            alpha_u, beta_u = residue.coordinates(moved[0], U, V, P)
            alpha_v, beta_v = residue.coordinates(moved[1], U, V, P)
            transform = [[alpha_u, alpha_v], [beta_u, beta_v]]
            determinant = (alpha_u * beta_v - alpha_v * beta_u) % P
            assert determinant
            determinants.append(determinant)
            assert matrix_product(transform, old_matrix[position:position + 2]) == O[position:position + 2]
            position += 2
    assert position == len(O)
    transport_determinant = 1
    for determinant in determinants:
        transport_determinant = transport_determinant * determinant % P
    return dict(old_panel_residue_rank=old_rank['rank'],
                old_panel_residue_determinant_mod_prime=old_rank['determinant_mod_prime'],
                old_panel_residue_sha256=residue.matrix_hash(old_matrix),
                local_two_coordinate_maps_invertible=True, entrywise_transport_verified=True,
                transport_map_determinants=determinants,
                transport_determinant_product_mod_prime=transport_determinant)


def check_case(m, numerator, denominator):
    T, N = m + 3, m + 2
    epsilon = numerator * pow(denominator, -1, P) % P
    old_times = sparse.factors(m, 'economic')
    old_tables = sparse.coefficient_tables(G, old_times)
    new_table = [[1, row[1] * epsilon % P, row[2] * pow(epsilon, 3, P) % P] for row in G]
    A = [[list(row) for row in G] for _ in range(2)] + old_tables + [new_table]
    matrix, geometry = residue.residue_matrix(T, A, P)
    blocks, labels = partition(matrix, T)
    full_rank = residue.modular_rank(matrix, P)
    old_transport = check_old_transport(T, A, blocks['O'])
    result = dict(old_block_count=m, total_block_count=m + 1, source_panel_T=T,
                  new_block_id=N, prime=P, G=G, old_time_factors=old_times,
                  new_epsilon=f'{numerator}/{denominator}', new_epsilon_mod_prime=epsilon,
                  new_time_factors_mod_prime=[epsilon, pow(epsilon, 3, P)],
                  parameter_scope='Positive rational common-G tables. Old blocks satisfy v=u^2; the new block uses v=u^3, so this fixture does not use slopes (0,1,2) across every block.',
                  geometry=geometry, partition=labels,
                  old_column_new_alpha_block_is_zero=True,
                  zero_block_entries_checked=len(blocks['zero']) * len(blocks['zero'][0]),
                  block_sha256={key: residue.matrix_hash(value) for key, value in blocks.items()},
                  full_residue_sha256=residue.matrix_hash(matrix),
                  full_residue_rank_certificate=full_rank, old_block_transport=old_transport)
    inverse_O = invert(blocks['O'])
    inverse_P = invert(blocks['P'])
    if inverse_O is None or inverse_P is None:
        result.update(schur_computed=False, O_invertible=inverse_O is not None,
                      P_invertible=inverse_P is not None)
        print(json.dumps(dict(m=m, epsilon=result['new_epsilon'], schur_computed=False,
                              O_invertible=inverse_O is not None, P_invertible=inverse_P is not None)), flush=True)
        return result
    Oinv, O_certificate = inverse_O
    Pinv, P_certificate = inverse_P
    old_size, new_size = len(blocks['O']), len(blocks['P'])
    assert O_certificate['determinant_mod_prime'] == (
        old_transport['old_panel_residue_determinant_mod_prime']
        * old_transport['transport_determinant_product_mod_prime']) % P
    OinvD = matrix_product(Oinv, blocks['D'])
    OinvE = matrix_product(Oinv, blocks['E'])
    regular_shared = matrix_difference(blocks['R'], matrix_product(blocks['B'], OinvD))
    regular_first = matrix_difference(blocks['S'], matrix_product(blocks['B'], OinvE))
    H = matrix_difference(regular_first, matrix_product(regular_shared, matrix_product(Pinv, blocks['Q'])))
    H_rank = residue.modular_rank(H, P)
    permutation_factor = labels['row_permutation_sign'] * labels['column_permutation_sign']
    factored_determinant = (permutation_factor * O_certificate['determinant_mod_prime']
                           * P_certificate['determinant_mod_prime'] * H_rank['determinant_mod_prime']) % P
    assert factored_determinant == full_rank['determinant_mod_prime']
    assert old_size + new_size + H_rank['rank'] == full_rank['rank']
    result.update(schur_computed=True, O_invertible=True, P_invertible=True,
                  O_inverse_certificate=O_certificate, P_inverse_certificate=P_certificate,
                  regular_shared_after_old_elimination_sha256=residue.matrix_hash(regular_shared),
                  regular_first_after_old_elimination_sha256=residue.matrix_hash(regular_first),
                  H_matrix=H, H_sha256=residue.matrix_hash(H), H_rank_certificate=H_rank,
                  determinant_factorization_mod_prime=factored_determinant,
                  determinant_factorization_verified=True, rank_factorization_verified=True)
    print(json.dumps(dict(m=m, epsilon=result['new_epsilon'], O_rank=old_size, P_rank=new_size,
                          H_rank=H_rank['rank'], full_rank=full_rank['rank'],
                          full_size=len(matrix), determinant_mod_prime=factored_determinant,
                          permutation_sign=permutation_factor)), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Residue Schur checks exceeded 28 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(28)
    cases = [check_case(m, numerator, denominator) for m in (2, 3, 4)
             for numerator, denominator in ((1, 7), (2, 11))]
    signal.alarm(0)
    result = dict(status='External exact modular residue Schur computations; no Lean or all-length theorem.',
                  original_residue_definition='Unnormalized source24_residue.residue_matrix: columns (t,s,a,b); local rows are coefficients of U_old and V_new.',
                  ordered_block_matrix='[[O,D,E],[0,P,Q],[B,R,S]]',
                  schur_formula='H=S-B*O^-1*E-(R-B*O^-1*D)*P^-1*Q',
                  determinant_identity='det(R_canonical)=sign(row_permutation)*sign(column_permutation)*det(O)*det(P)*det(H)',
                  zero_block_reason='For an old-old column the new block is last in its word. Its old/new double residue is proportional to the new residue vector, so its old-vector coordinate vanishes.',
                  interpretation='Nonzero determinants certify these finite rational specializations after denominator clearing. They do not prove an arbitrary-length regular-half or source-family determinant.',
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
