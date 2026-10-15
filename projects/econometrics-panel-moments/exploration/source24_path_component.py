#!/usr/bin/env python3
"""Actual component-two path factorization and cleared polynomial ranks.

For a path a indexed by blocks, phi_a=X2*prod_t(X_(a_t)/L_(t,a_t)).
The actual raw marked word (t,s,remaining ascending), ending in output 2,
has coefficient prod A along that word, including its final transition to 2.
Every all-2 path has coefficient C22=prod_t A_t(2,2), independent of order.
Thus psi_a=phi_a, except psi_all2=phi_all2-X2/C22, absorbs the long-empty
delta term. First-slot differences cancel that coefficient, and selected
output-zero columns do not contain it. The actual N coefficient matrix in
psi is consequently minus its raw-word matrix times the existing source
generator matrix; the local E correction is included, not discarded.

Clearing by D/X2 gives prod_t f_(t,a_t), where
f_(t,a)=X_a*prod_(b!=a)L_(t,b), and subtracts D/C22 for the all-2 path.
We check these actual-source formulas at three ordinary points and compute
exact finite-field polynomial ranks, rather than sampled evaluation ranks.
Only finite m=3,4,5 fixtures are certified; no all-length theorem is claimed.

Reproduce:
  nice -n 19 python3 exploration/source24_path_component.py --output exploration/source24-path-component-results.json
"""

import argparse
import itertools as it
import json
from pathlib import Path
import signal
import time

import source24_component_two as component


incoming = component.incoming
P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
differences = component.differences
HERE = Path(__file__).resolve().parent
ONE = {(0, 0, 0): 1}
AXES = tuple(tuple(int(i == j) for i in range(3)) for j in range(3))


def polynomial_product(left, right):
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            exponent = tuple(u + v for u, v in zip(a, b))
            result[exponent] = (result.get(exponent, 0) + x * y) % P
    return {a: x for a, x in result.items() if x}


def monomials(degree):
    return [(a, b, degree - a - b) for a in range(degree + 1)
            for b in range(degree - a + 1)]


def monomial_values(exponents, X):
    degree = sum(exponents[0])
    powers = [[pow(x, k, P) for k in range(degree + 1)] for x in X]
    return [powers[0][a] * powers[1][b] * powers[2][c] % P for a, b, c in exponents]


def row_times_matrix(row, matrix):
    return schur.matrix_product([row], matrix)[0]


def path_polynomials(tables):
    paths, polynomials, D = [()], [ONE], ONE
    for table in tables:
        lines = [dict(zip(AXES, (x % P for x in row))) for row in table]
        factors = []
        for a in range(3):
            factor = {AXES[a]: 1}
            for b in range(3):
                if b != a:
                    factor = polynomial_product(factor, lines[b])
            factors.append(factor)
        polynomials = [polynomial_product(poly, factors[a]) for poly in polynomials for a in range(3)]
        paths = [path + (a,) for path in paths for a in range(3)]
        for line in lines:
            D = polynomial_product(D, line)
    assert paths == list(it.product(range(3), repeat=len(tables)))
    return paths, polynomials, D


def word_coefficient(path, word, A):
    value = A[word[-1]][path[word[-1] - 2]][2] % P
    for left, right in zip(word, word[1:]):
        value = value * A[left][path[left - 2]][path[right - 2]] % P
    return value


def marked_word_coefficients(m, A, paths, columns):
    old = list(range(2, m + 2))
    matrix = []
    for path in paths:
        weights = {(t, s): word_coefficient(path, [t, s] + [u for u in old if u not in (t, s)], A)
                   for t in old for s in old if t != s}
        matrix.append([weights[t, s] if path[t - 2] == a and path[s - 2] == b else 0
                       for t, s, a, b in columns])
    return matrix


def basepoints(tables):
    points, labels = [], []
    for t, table in enumerate(tables, start=2):
        for a in range(3):
            points.append(residue.cross(table[a], AXES[a], P))
            labels.append(dict(kind='matching_coordinate', t=t, a=a))
        for a, b in it.combinations(range(3), 2):
            points.append(residue.cross(table[a], table[b], P))
            labels.append(dict(kind='same_block_intersection', t=t, a=a, b=b))
    assert all(any(point) for point in points)
    return points, labels


def D_membership(raw, Dcolumn, paths, raw_certificate):
    """Solve in a certified column basis; verify every polynomial coefficient."""
    indices = raw_certificate['rank_certificate']['nonzero_minor']['columns']
    augmented = [[row[j] for j in indices] + [d] for row, d in zip(raw, Dcolumn)]
    pivots, free, kernel = incoming.dual.rref_kernel(augmented)
    target = len(indices)
    belongs = target in free
    result = dict(in_raw_path_span_over_Fp=belongs, augmented_rank=len(pivots),
                  basis_path_indices=indices, augmented_matrix_sha256=residue.matrix_hash(augmented))
    if belongs:
        vector = kernel[free.index(target)]
        assert vector[-1] == 1
        coefficients = [-x % P for x in vector[:-1]]
        assert all(sum(row[j] * c for j, c in zip(indices, coefficients)) % P == d
                   for row, d in zip(raw, Dcolumn))
        result.update(polynomial_coefficient_equation_verified=True,
                      nonzero_path_coefficients=[dict(path_index=j, path=paths[j], coefficient=c)
                                                 for j, c in zip(indices, coefficients) if c])
    else:
        assert len(pivots) == target + 1
        result['nonmembership_scope'] = 'Exact over this finite field; not a characteristic-zero nonmembership conclusion.'
    return result


def ordinary_checks(m, A, tables, paths, columns, labels, terms, gauge,
                    W, Cpath, exponents, raw, normalized, Npolynomial, Dcolumn, C22):
    points = [(1, 2, 3), (2, 3, 5), (3, 5, 7)]
    raw_checks = N_checks = long_checks = clearing_checks = 0
    old = list(range(2, m + 2))
    saved_points = []
    for X in points:
        values = sparse.evaluated_columns(tables, X)
        assert values is not None
        evaluated = dict(zip(sparse.column_labels(m), values))
        denominators = [[residue.dot(A[t][a], X, P) for a in range(3)] for t in old]
        assert all(x for row in denominators for x in row)
        kernels = {t: residue.ordinary_kernel(A, t, X, P) for t in old}
        phi = []
        for path in paths:
            value = X[2]
            for t, a in enumerate(path):
                value = value * X[a] * pow(denominators[t][a], -1, P) % P
            phi.append(value)
        psi = phi[:]
        psi[-1] = (psi[-1] - X[2] * pow(C22, -1, P)) % P
        source2 = [A[t][a][b] * evaluated['Fbar', t - 2, s - 2, a, b][2] % P
                   for t, s, a, b in columns]
        raw2 = [(X[a] * kernels[t][a][b] * int(b == 2) - value) % P
                for (t, s, a, b), value in zip(columns, source2)]
        assert row_times_matrix(phi, W) == raw2, ('Actual raw-word factorization failed.', m, X)
        raw_checks += len(columns)
        N2 = component.apply_generators([source2], terms)[0]
        for j, local_E in enumerate(gauge):
            if local_E is not None:
                t, a = local_E
                N2[j] = (N2[j] + evaluated['E', t - 2, a][2]) % P
        assert row_times_matrix(psi, Cpath) == N2, ('Normalized N factorization failed.', m, X)
        N_checks += len(labels)
        products = {t: residue.word_product(kernels, residue.ordered_word(old, t), P) for t in old}
        for j, label in enumerate(labels):
            if label['kind'] == 'long_empty':
                t, a = label['t'], label['a']
                assert N2[j] == X[a] * (int(a == 2) - products[t][a][2]) % P
                long_checks += 1
        powers = monomial_values(exponents, X)
        DX = sum(x * y for x, y in zip(powers, Dcolumn)) % P
        expected_D = 1
        for row in denominators:
            for d in row:
                expected_D = expected_D * d % P
        assert DX == expected_D and DX
        multiplier = DX * pow(X[2], -1, P) % P
        for matrix, values_at_X in ((raw, phi), (normalized, psi), (Npolynomial, N2)):
            assert row_times_matrix(powers, matrix) == [multiplier * value % P for value in values_at_X]
            clearing_checks += len(values_at_X)
        saved_points.append(dict(X=X, all_denominators_nonzero=True, D=DX,
                                 actual_N_component_sha256=residue.matrix_hash([N2])))
    return dict(points=saved_points, raw_marked_word_checks=raw_checks,
                normalized_N_component_checks=N_checks, independent_long_empty_word_checks=long_checks,
                polynomial_clearing_checks=clearing_checks,
                evaluator='normalized_sparse_source24.evaluated_columns with A_t(a,b) restored; local E added for long-empty generators.')


def calculate(m, saved_case):
    started = time.monotonic()
    times = sparse.factors(m, 'economic')
    tables = sparse.coefficient_tables(G, times)
    A = [[list(row) for row in G] for _ in range(2)] + tables
    geometry = differences.check_geometry(m, A)
    paths, polynomials, D = path_polynomials(tables)
    exponents = monomials(3 * m)
    raw = [[poly.get(exponent, 0) for poly in polynomials] for exponent in exponents]
    Dcolumn = [D.get(exponent, 0) for exponent in exponents]
    C22 = 1
    for table in tables:
        C22 = C22 * table[2][2] % P
    assert C22
    normalized = [row[:-1] + [(row[-1] - d * pow(C22, -1, P)) % P]
                  for row, d in zip(raw, Dcolumn)]
    _, columns = schur.canonical_labels(m + 2)
    labels, terms, gauge, empty_indices, _ = component.generators(m, columns)
    W = marked_word_coefficients(m, A, paths, columns)
    Cpath = [[-x % P for x in row] for row in component.apply_generators(W, terms)]
    old = list(range(2, m + 2))
    all2 = paths.index((2,) * m)
    for j, label in enumerate(labels):
        assert Cpath[all2][j] == (-C22 if label['kind'] == 'long_empty' and label['a'] == 2 else 0) % P
    long_coefficient_checks = 0
    for i, path in enumerate(paths):
        for t in old:
            coefficient = -word_coefficient(path, residue.ordered_word(old, t), A) % P
            for a in range(3):
                assert Cpath[i][empty_indices[t, a]] == (coefficient if path[t - 2] == a else 0)
                long_coefficient_checks += 1
    Npolynomial = schur.matrix_product(normalized, Cpath)
    direct_checks = ordinary_checks(m, A, tables, paths, columns, labels, terms, gauge,
                                   W, Cpath, exponents, raw, normalized, Npolynomial, Dcolumn, C22)

    points, point_labels = basepoints(tables)
    base_evaluation = [monomial_values(exponents, X) for X in points]
    normalized_evaluation = base_evaluation + [monomial_values(exponents, (0, 0, 1))]
    assert not any(x for row in schur.matrix_product(base_evaluation, raw) for x in row)
    assert not any(x for row in schur.matrix_product(normalized_evaluation, normalized) for x in row)
    assert all(sum(x * y for x, y in zip(row, Dcolumn)) % P == 0 for row in base_evaluation)
    base_certificate = incoming.matrix_certificate(base_evaluation)
    constraint_certificate = incoming.matrix_certificate(normalized_evaluation)
    assert base_certificate['rank_certificate']['rank'] == 6 * m
    assert constraint_certificate['rank_certificate']['rank'] == 6 * m + 1
    raw_certificate = incoming.matrix_certificate(raw)
    normalized_certificate = incoming.matrix_certificate(normalized)
    N_certificate = incoming.matrix_certificate(Npolynomial)
    D_span = D_membership(raw, Dcolumn, paths, raw_certificate)
    assert saved_case['prime'] == P and saved_case['G'] == [list(row) for row in G]
    assert saved_case['time_factors'] == [list(pair) for pair in times]
    prior = saved_case['N_component_two_observations']
    N_rank = N_certificate['rank_certificate']['rank']
    assert N_rank == prior['rank_certificate']['rank'], 'Cleared actual N rank differs from the saved residue/axis rank.'
    r = 9 * m * (m - 1) // 2
    raw_ambient = len(exponents) - 6 * m
    normalized_ambient = len(exponents) - 6 * m - 1
    assert normalized_ambient == r + 3 * m
    result = dict(m=m, prime=P, G=G, time_fixture='economic', time_factors=times,
                  geometry=geometry, path_count=len(paths), N_generator_count=len(labels),
                  polynomial_degree=3*m, monomial_exponents=exponents,
                  path_order='Lexicographic tuples in {0,1,2}^m; position t-2 is actual block t.',
                  raw_path_polynomials=raw_certificate, normalized_path_polynomials=normalized_certificate,
                  actual_N_polynomials=N_certificate,
                  raw_path_span_equals_basepoint_kernel_over_Fp=raw_certificate['rank_certificate']['rank'] == raw_ambient,
                  normalized_path_span_equals_basepoint_and_e2_kernel_over_Fp=normalized_certificate['rank_certificate']['rank'] == normalized_ambient,
                  N_image_equals_normalized_path_span_over_Fp=N_rank == normalized_certificate['rank_certificate']['rank'],
                  raw_ambient_dimension=raw_ambient, normalized_ambient_dimension=normalized_ambient,
                  D_span=D_span, D_polynomial_sha256=residue.matrix_hash([Dcolumn]),
                  basepoint_evaluation=base_certificate, normalized_constraint_evaluation=constraint_certificate,
                  basepoints=points, basepoint_labels=point_labels,
                  all_raw_paths_vanish_at_6m_basepoints=True, all_normalized_paths_also_vanish_at_e2=True,
                  all2_path_coefficient=C22, all2_normalization_generator_check=True,
                  long_empty_path_coefficient_checks=long_coefficient_checks,
                  marked_word_coefficient_matrix_sha256=residue.matrix_hash(W),
                  N_path_coefficient_matrix_sha256=residue.matrix_hash(Cpath),
                  N_generator_labels=labels, ordinary_checks=direct_checks,
                  saved_observation_comparison=dict(file='source24-component-two-results.json',
                      N_observation_matrix_sha256=prior['sha256'], rank=prior['rank_certificate']['rank'],
                      matches_cleared_polynomial_rank=True, previous_residue_calculation_rerun=False),
                  elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(m=m, raw_path_rank=raw_certificate['rank_certificate']['rank'],
                          normalized_path_rank=normalized_certificate['rank_certificate']['rank'],
                          N_rank=N_rank, ambient=normalized_ambient,
                          D_in_raw_span=D_span['in_raw_path_span_over_Fp'],
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def two_block_interpolation():
    times = sparse.factors(2, 'economic')
    tables = sparse.coefficient_tables(G, times)
    A = [[list(row) for row in G] for _ in range(2)] + tables
    geometry = differences.check_geometry(2, A)
    points, labels = basepoints(tables)
    exponents = monomials(4)
    evaluation = [monomial_values(exponents, point) for point in points]
    certificate = incoming.matrix_certificate(evaluation)
    assert certificate['rank_certificate']['rank'] == 12
    return dict(m=2, degree=4, prime=P, G=G, time_factors=times, geometry=geometry,
                points=points, point_labels=labels, monomial_exponents=exponents,
                evaluation=certificate, independent_point_conditions=True,
                limitation='A 12-by-12 nonzero minor at this two-block fixture; no grouping or extension theorem is asserted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases, interpolation = time.monotonic(), [], None
    saved = json.loads((HERE / 'source24-component-two-results.json').read_text())

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second path-component cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB path-component RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation, current = None, 'two_block_interpolation'
    try:
        interpolation = two_block_interpolation()
        for current in (3, 4, 5):
            saved_case = next(case for case in saved['cases'] if case['m'] == current)
            cases.append(calculate(current, saved_case))
    except TimeoutError as error:
        limitation = dict(stage=current, reason=str(error))
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite exact polynomial and actual-source path-factorization checks; no all-length theorem.',
                  prime=P, normalization='psi_all2=phi_all2-X2/prod_t A_t(2,2); other paths unchanged. Polynomial clearing multiplier is D/X2.',
                  source_coefficients='Actual order (t,s,remaining ascending), with every transition coefficient including the final output 2; N coefficients are minus raw-word coefficients times the actual source generator matrix.',
                  independent_check='Path sums and polynomial evaluations are compared with the existing actual kernel-product evaluator at three ordinary points, with A_t(a,b) restored and local E included.',
                  rank_scope='All ranks and D membership are exact over F_1000003 at the recorded fixtures. Nonzero minors lift after clearing denominators; modular rank deficiencies alone are not characteristic-zero upper bounds.',
                  limitations='No all-m interpolation, path-span, N-surjectivity, or equation-(24) independence theorem is asserted. Ordinary-point checks are finite checks of the displayed algebraic expansion.',
                  limits=dict(seconds=28, maximum_rss_bytes=95*1024**2),
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, two_block_degree_four_interpolation=interpolation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
