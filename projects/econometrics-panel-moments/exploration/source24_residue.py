#!/usr/bin/env python3
"""Quadratic-size equation (24) residue matrices; external exact discovery.

This implements research/SOURCE24_INDUCTION.md. It does not contain a Lean
proof or establish an arbitrary-T nonvanishing theorem. In the note's
one-based previous-outcome convention the blocks are 2,...,T-1; these are
also the zero-based coefficient-table indices of their outgoing transitions.

Run from the project directory:
  nice -n 19 python3 exploration/source24_residue.py --output exploration/residue-results.json

The default run checks both G[2][2]=16 and 17 at T=4,5,6, compares with
path-space calculations, and then checks G[2][2]=17 at T=7,8 without
enumerating paths. The optional scans stay at T=5. Standard library only.
"""

import argparse
import hashlib
import importlib.util
import itertools as it
import json
from pathlib import Path


Q = 3
PRIME = 1000003
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('path_model', ROOT / 'exploration/general_source24.py')
path_model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(path_model)


def transition_table(T, transition22=17, time_exponents=None):
    G = ((1, 1, 1), (1, 2, 4), (1, 4, transition22))
    powers = time_exponents if time_exponents is not None else [3 * (t + 1) for t in range(T)]
    assert len(powers) >= T and transition22 > 0
    # A[t][lag][outcome], unlike the earlier PI[t][outcome][lag].
    return [[[G[q][a] * (1 << (q * powers[t])) for q in range(Q)]
             for a in range(Q)] for t in range(T)]


def dot(a, b, p):
    return sum(x * y for x, y in zip(a, b)) % p


def cross(a, b, p):
    return [(a[1] * b[2] - a[2] * b[1]) % p,
            (a[2] * b[0] - a[0] * b[2]) % p,
            (a[0] * b[1] - a[1] * b[0]) % p]


def identity():
    return [[int(a == b) for b in range(Q)] for a in range(Q)]


def matmul(a, b, p):
    columns = list(zip(*b))
    return [[dot(row, col, p) for col in columns] for row in a]


def word_product(matrices, word, p):
    ans = identity()
    for t in word:
        ans = matmul(ans, matrices[t], p)
    return ans


def ordered_word(blocks, first):
    assert first in blocks
    return [first] + [t for t in blocks if t != first]


def ordinary_kernel(A, t, point, p):
    kernel = []
    for a in range(Q):
        denominator = dot(A[t][a], point, p)
        if denominator == 0:
            raise ValueError('Ordinary transition evaluated at a pole.')
        inverse = pow(denominator, -1, p)
        kernel.append([A[t][a][i] * point[i] * inverse % p for i in range(Q)])
    assert all(sum(row) % p == 1 for row in kernel)
    return kernel


def coordinates(vector, U, V, p):
    minor = next(((i, j, (U[i] * V[j] - U[j] * V[i]) % p)
                  for i, j in it.combinations(range(Q), 2)
                  if (U[i] * V[j] - U[j] * V[i]) % p), None)
    if minor is None:
        raise ValueError('The two pole residue vectors are dependent.')
    i, j, determinant = minor
    inverse = pow(determinant, -1, p)
    alpha = (vector[i] * V[j] - vector[j] * V[i]) * inverse % p
    beta = (U[i] * vector[j] - U[j] * vector[i]) * inverse % p
    assert all((alpha * U[k] + beta * V[k] - vector[k]) % p == 0 for k in range(Q))
    return alpha, beta


def modular_rank(matrix, p):
    """Independent forward Gaussian loop, with explicit row interchanges.

    The recorded minor uses original row IDs in pivot-selection order.
    For a full square matrix we also give its determinant in original order.
    This does not import or reuse general_source24.Echelon.
    """
    a = [[x % p for x in row] for row in matrix]
    nrows, ncols = len(a), len(a[0]) if a else 0
    ids = list(range(nrows))
    selected_rows, selected_columns = [], []
    rank, pivot_product, sign = 0, 1, 1
    for c in range(ncols):
        pivot_row = next((i for i in range(rank, nrows) if a[i][c]), None)
        if pivot_row is None:
            continue
        if pivot_row != rank:
            a[rank], a[pivot_row] = a[pivot_row], a[rank]
            ids[rank], ids[pivot_row] = ids[pivot_row], ids[rank]
            sign = -sign
        pivot = a[rank][c]
        pivot_product = pivot_product * pivot % p
        selected_rows.append(ids[rank])
        selected_columns.append(c)
        inverse = pow(pivot, -1, p)
        pivot_tail = a[rank][c + 1:]
        for i in range(rank + 1, nrows):
            factor = a[i][c] * inverse % p
            if factor:
                a[i][c] = 0
                a[i][c + 1:] = [(x - factor * y) % p
                                 for x, y in zip(a[i][c + 1:], pivot_tail)]
        rank += 1
        if rank == nrows:
            break
    result = dict(rank=rank, full_rank=(rank == min(nrows, ncols)),
                  nonzero_minor=dict(size=rank, rows=selected_rows,
                                     columns=selected_columns,
                                     determinant_mod_prime=pivot_product,
                                     order='Rows and columns in listed order.'))
    if nrows == ncols:
        result['determinant_mod_prime'] = sign * pivot_product % p if rank == nrows else 0
    return result


def matrix_hash(matrix):
    h = hashlib.sha256()
    for row in matrix:
        h.update((','.join(map(str, row)) + '\n').encode())
    return h.hexdigest()


def residue_matrix(T, A, p):
    blocks = list(range(2, T))
    columns = [(t, s, a, b) for t in blocks for s in blocks if t != s
               for a in range(Q) for b in range(Q)]
    matrix = []
    point_count = 0
    for u, v in it.combinations(blocks, 2):
        for c, d in it.product(range(Q), repeat=2):
            point = cross(A[u][c], A[v][d], p)
            if not all(point):
                raise ValueError(f'Cross point has a zero coordinate: {(u, c, v, d)}.')
            values = {(t, a): dot(A[t][a], point, p) for t in blocks for a in range(Q)}
            zeros = {key for key, value in values.items() if value == 0}
            if zeros != {(u, c), (v, d)}:
                raise ValueError(f'No-third-line condition fails: {(u, c, v, d)}, {sorted(zeros)}.')
            U = [A[u][c][i] * point[i] % p for i in range(Q)]
            V = [A[v][d][i] * point[i] % p for i in range(Q)]
            assert sum(U) % p == sum(V) % p == 0
            coordinates(U, U, V, p)
            matrices = {}
            for t in blocks:
                if t == u:
                    matrices[t] = [U[:] if a == c else [0, 0, 0] for a in range(Q)]
                elif t == v:
                    matrices[t] = [V[:] if a == d else [0, 0, 0] for a in range(Q)]
                else:
                    matrices[t] = ordinary_kernel(A, t, point, p)
            words = {}
            for t in blocks:
                remaining = [s for s in blocks if s != t]
                for s in remaining:
                    words[t, s] = word_product(matrices, ordered_word(remaining, s), p)

            alpha_row, beta_row = [], []
            for t, s, a, b in columns:
                if (t == u and a != c) or (t == v and a != d):
                    alpha_row.append(0)
                    beta_row.append(0)
                    continue
                prefactor = A[t][a][b] * point[b] % p
                if t not in (u, v):
                    prefactor = prefactor * pow(values[t, a], -1, p) % p
                scalar = -point[a] * prefactor % p
                vector = [scalar * x % p for x in words[t, s][b]]
                assert sum(vector) % p == 0
                alpha, beta = coordinates(vector, U, V, p)
                alpha_row.append(alpha)
                beta_row.append(beta)
            # The two corresponding local-pair columns have independent
            # residues (0,-A_u(c,d)X_cX_d) and (-A_v(d,c)X_cX_d,0).
            local_beta = -A[u][c][d] * point[c] * point[d] % p
            local_alpha = -A[v][d][c] * point[d] * point[c] % p
            assert local_alpha and local_beta
            matrix.extend((alpha_row, beta_row))
            point_count += 1
    assert len(matrix) == len(columns) == 9 * len(blocks) * (len(blocks) - 1)
    return matrix, dict(cross_line_points=point_count,
                        coordinates_nonzero=True, no_third_denominator_line=True,
                        two_residue_vectors_independent=True,
                        local_pair_residue_blocks_invertible=True)


def quotient_formula(idx, A, point, p):
    T = len(A)
    blocks = list(range(2, T))
    matrices = {t: ordinary_kernel(A, t, point, p) for t in blocks}
    s = idx['s2'] + 1
    if idx['j'] == 0:
        a = idx['values'][0]
        word = word_product(matrices, ordered_word(blocks, s), p)
        return [point[a] * (int(i == a) - word[a][i]) % p for i in range(Q)]
    assert idx['j'] == 1 and idx['shared'][0] > 0
    t = idx['shared'][0] + 1
    b, a = idx['values']
    word = word_product(matrices, ordered_word([u for u in blocks if u != t], s), p)
    scalar = point[a] * matrices[t][a][b] % p
    return [scalar * (int(i == b) - word[b][i]) % p for i in range(Q)]


def check_path_formula(T, transition22, A, p):
    """Compare both source formulas with actual path sums, entry by entry."""
    assert T <= 6
    G = ((1, 1, 1), (1, 2, 4), (1, 4, transition22))
    paths = list(it.product(range(Q), repeat=T))
    indices = [idx for idx in path_model.source_indices(T) if 0 not in idx['shared']]
    rows = [path_model.source_row(paths, idx, G=G) for idx in indices]
    points = [(1, 2, 3), (2, 3, 5)]
    for point in points:
        denominators = [[dot(A[t][a], point, p) for a in range(Q)] for t in range(T)]
        assert all(value for row in denominators for value in row)
        weights = []
        for y in paths:
            weight = 1
            for t, a in enumerate(y):
                weight = weight * point[a] % p
                if t:
                    weight = weight * pow(denominators[t][y[t - 1]], -1, p) % p
            weights.append(weight)
        for idx, row in zip(indices, rows):
            actual = [0, 0, 0]
            first_outcome = idx['values'][1 if idx['j'] else 0]
            inverse_initial_coefficient = pow(A[0][0][first_outcome], -1, p)
            for y, numerator, weight in zip(paths, row, weights):
                actual[y[0]] = (actual[y[0]] + numerator * weight) % p
            actual = [x * inverse_initial_coefficient % p for x in actual]
            predicted = quotient_formula(idx, A, point, p)
            assert actual == predicted, (T, transition22, idx, point, actual, predicted)
        # Also check the constant-coefficient j0 -> single-block operation.
        blocks = list(range(2, T))
        matrices = {t: ordinary_kernel(A, t, point, p) for t in blocks}
        for s in blocks:
            r = min(t for t in blocks if t != s)
            for a in range(Q):
                idx0 = dict(j=0, s2=s - 1, values=(a,))
                source0 = quotient_formula(idx0, A, point, p)
                correction = [0, 0, 0]
                for b in range(Q):
                    idx1 = dict(j=1, shared=(s - 1,), s2=r - 1, values=(b, a))
                    value = quotient_formula(idx1, A, point, p)
                    correction = [(x + y) % p for x, y in zip(correction, value)]
                single = [point[a] * (int(i == a) - matrices[s][a][i]) % p for i in range(Q)]
                assert [(x - y) % p for x, y in zip(source0, correction)] == single
    return dict(prime=p, effect_points=points, checked_extension_rows=len(indices),
                path_sum_formula_equal=True, j0_single_block_reduction_equal=True,
                scope='Exact finite-field comparisons at the displayed effect points, not a symbolic identity proof.')


def saved_path_checks():
    stored = json.loads((ROOT / 'exploration/general-source24-results.json').read_text())
    results = {}
    for experiment in [stored] + stored.get('additional_experiments', []):
        g22 = experiment['witness'].get('G', [[1, 1, 1], [1, 2, 4], [1, 4, 16]])[2][2]
        for period in experiment['periods']:
            for check in period['modular_checks']:
                results[g22, period['T'], check['prime']] = check
    return results


def check_original_minor(p):
    """A second elimination algorithm verifies one saved 162-square minor."""
    source = saved_path_checks()[17, 5, p]['nonzero_original_integer_minor_mod_prime']
    indices = path_model.source_indices(5)
    paths = list(it.product(range(Q), repeat=5))
    G = ((1, 1, 1), (1, 2, 4), (1, 4, 17))
    minor = []
    for i in source['rows']:
        row = path_model.source_row(paths, indices[i], G=G)
        minor.append([row[j] for j in source['columns']])
    result = modular_rank(minor, p)
    assert result['rank'] == 162
    assert result['determinant_mod_prime'] == source['determinant_mod_prime']
    return dict(T=5, transition22=17, prime=p, size=162,
                independently_recomputed_determinant=result['determinant_mod_prime'],
                matches_saved_minor=True,
                method='Separate forward Gaussian elimination with explicit row interchanges; does not use general_source24.Echelon.')


def run_case(T, transition22, p, path_checks, time_exponents=None, validate_paths=True):
    A = transition_table(T, transition22, time_exponents)
    matrix, geometry = residue_matrix(T, A, p)
    rank = modular_rank(matrix, p)
    n = T - 2
    result = dict(T=T, n=n, transition22=transition22, prime=p,
                  time_exponents=time_exponents or [3 * (t + 1) for t in range(T)],
                  residue_matrix_size=len(matrix), residue_matrix_sha256=matrix_hash(matrix),
                  geometry=geometry, residue_rank=rank['rank'],
                  residue_nullity=len(matrix) - rank['rank'],
                  predicted_extension_rank=3 * n + rank['rank'],
                  full_extension_row_count=3 * n * (3 * n - 2),
                  determinant_mod_prime=rank['determinant_mod_prime'],
                  nonzero_residue_minor=rank['nonzero_minor'])
    if T <= 6 and time_exponents is None and validate_paths:
        result['path_formula_check'] = check_path_formula(T, transition22, A, p)
        check = path_checks.get((transition22, T, p))
        if check is None:
            # The stored initial experiment did not include perturbed T4.
            indices = path_model.source_indices(T)
            paths = list(it.product(range(Q), repeat=T))
            G = ((1, 1, 1), (1, 2, 4), (1, 4, transition22))
            rows = [path_model.source_row(paths, idx, G=G) for idx in indices]
            check = path_model.check_prime(T, indices, rows, p)
        result['path_quotient_rank'] = check['extension_quotient_rank']
        result['path_rank_comparison_equal'] = result['predicted_extension_rank'] == check['extension_quotient_rank']
        assert result['path_rank_comparison_equal']
    print(json.dumps({key: result[key] for key in
                      ('T', 'transition22', 'prime', 'residue_matrix_size', 'residue_rank',
                       'residue_nullity', 'predicted_extension_rank', 'determinant_mod_prime')}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--scan-transition22', action='store_true')
    parser.add_argument('--irregular-conic', action='store_true')
    args = parser.parse_args()
    checks = saved_path_checks()
    cases = [run_case(T, transition22, PRIME, checks)
             for transition22, periods in ((16, (4, 5, 6)), (17, (4, 5, 6, 7, 8)))
             for T in periods]
    result = dict(status='Exact external residue-matrix discovery; not Lean-verified and not an arbitrary-T proof.',
                  mathematical_specification='research/SOURCE24_INDUCTION.md',
                  matrix_definition='Columns F[t,s,a,b] = X_a K_t(a,b) e_b (I-P_s^(B\\{t})); each row pair is the double-pole residue at L[u,c]=L[v,d]=0 in the basis (v[u,c],v[v,d]).',
                  row_order='u<v ascending block pairs, c,d lexicographic, alpha then beta',
                  column_order='t ascending, s ascending except t, shared outcome a then divergence outcome b',
                  block_labels='B=2,...,T-1, equal to zero-based coefficient-table indices; n=T-2.',
                  table='A[t][lag][outcome] = G[outcome][lag] * 2^(3*outcome*(t+1)), except explicitly supplied time exponents.',
                  rank_interpretation='3n+rank(R_n) is the extension rank under the stated quotient and residue-basis argument. Small-T comparisons test the formulas against actual source path sums and existing path elimination.',
                  nonzero_interpretation='A full nonzero modular determinant proves nonvanishing of the rational residue determinant at this economic specialization, because every evaluated denominator was checked nonzero. Modular deficiency alone does not give a real-rank upper bound.',
                  cases=cases,
                  independent_saved_original_minor_check=check_original_minor(PRIME))
    if args.scan_transition22:
        result['transition22_scan_T5'] = [run_case(5, h, PRIME, checks, validate_paths=False)
                                          for h in (5, 9, 15, 16, 17, 18, 25, 36)]
    if args.irregular_conic:
        result['irregular_conic_T5'] = run_case(5, 16, PRIME, checks,
                                               time_exponents=[3, 7, 12, 18, 25],
                                               validate_paths=False)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
