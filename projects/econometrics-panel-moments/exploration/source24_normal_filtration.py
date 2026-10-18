#!/usr/bin/env python3
"""Successive X0-normal layers of the actual cleared component-two family.

At the existing m=4,5 economic fixtures, p2=D*R2/X2 is constructed with the
actual N generator coefficients, including each long-empty local E term.
The comparison matrix consists of all normalized pure paths in the identical
monomial order.  Rows of layer k are the coefficients of X0^k.

The current kernel basis R_<k stays in the ORIGINAL column coordinates.
The next map is A_k R_<k, and R_<=k is obtained by multiplying by the kernel
basis of that map.  Thus gains are coupled cumulative ranks, not sums of
independently ranked normal layers.  Each update retains systematic free
coordinates and an exact layer-kernel certificate.

The detailed X0^3 kernel separates coefficient relations that give the zero
polynomial from a basis of nonzero polynomials divisible by X0^3.  A separate
ten-point cubic evaluation tests the two-block off-axis interpolation base.
All ranks
are exact over the stated finite field at these two fixtures only; they are
not a uniform formula or a characteristic-zero upper-bound claim.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_path_component as path


incoming, component = path.incoming, path.component
P, G = path.P, path.G
residue, schur, sparse = path.residue, path.schur, path.sparse
HERE = Path(__file__).resolve().parent


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def image_on_vectors(matrix, vectors):
    return [[sum(x*y for x, y in zip(row, vector)) % P for vector in vectors] for row in matrix]


def systematic_update(vectors, pivots, free, local_kernel):
    """Sparse multiplication R_new=R_old*K; no change of source coordinates."""
    updated = []
    for f, vector in zip(free, local_kernel):
        result = vectors[f][:]
        for p in pivots:
            factor = vector[p]
            if factor:
                result = [(x+factor*y) % P for x, y in zip(result, vectors[p])]
        updated.append(result)
    return updated


def normal_filtration(matrix, exponents, detailed=False):
    columns = len(matrix[0])
    degree = sum(exponents[0])
    vectors = [[int(i == j) for i in range(columns)] for j in range(columns)]
    free_original = list(range(columns))
    stages, through_two, prefix_end = [], None, 0
    for k in range(degree+1):
        row_indices = [i for i, exponent in enumerate(exponents) if exponent[0] == k]
        assert row_indices == list(range(prefix_end, prefix_end+len(row_indices)))
        prefix_end += len(row_indices)
        layer = [matrix[i] for i in row_indices]
        image = image_on_vectors(layer, vectors)
        input_hash = residue.matrix_hash(vectors)
        pivots, free, kernel = incoming.dual.rref_kernel(image)
        image_certificate = incoming.matrix_certificate(image)
        gain = len(pivots)
        assert image_certificate['rank_certificate']['rank'] == gain
        old_dimension = len(vectors)
        vectors = systematic_update(vectors, pivots, free, kernel)
        free_original = [free_original[f] for f in free]
        assert len(vectors) == old_dimension-gain
        assert all(vector[f] == int(i == j) for i, vector in enumerate(vectors)
                   for j, f in enumerate(free_original))
        # rref_kernel has checked (A_k R_<k)*K=0 and systematic K free rows.
        # Together with the verified update, prior zero layers stay zero.
        if k in (2, degree):
            assert not any(x for row in image_on_vectors(matrix[:prefix_end], vectors) for x in row)
        stage = dict(normal_order=k, coefficient_row_indices=row_indices,
                     input_coefficient_kernel_dimension=old_dimension,
                     input_kernel_basis_sha256=input_hash,
                     layer_image_matrix=image, layer_image_certificate=image_certificate,
                     local_pivot_coordinates=pivots, local_free_coordinates=free,
                     local_kernel_basis_sha256=residue.matrix_hash(kernel),
                     retained_original_free_columns=free_original[:],
                     coefficient_kernel_dimension=len(vectors),
                     coefficient_kernel_basis_sha256=residue.matrix_hash(vectors),
                     cumulative_rank=columns-len(vectors), incremental_gain=gain,
                     systematic_free_coordinate_identity_verified=True,
                     layer_kernel_equation_verified=True)
        stages.append(stage)
        if k == 2 and detailed:
            through_two = dict(vectors=[v[:] for v in vectors], free_columns=free_original[:])
    full_rank = columns-len(vectors)
    full_certificate = incoming.matrix_certificate(matrix)
    assert full_certificate['rank_certificate']['rank'] == full_rank
    for stage in stages:
        stage['nonzero_polynomial_kernel_dimension'] = full_rank-stage['cumulative_rank']
        stage['full_polynomial_relation_dimension'] = columns-full_rank
    result = dict(column_count=columns, full_rank=full_rank,
                  full_coefficient_certificate=full_certificate,
                  cumulative_ranks=[s['cumulative_rank'] for s in stages],
                  incremental_gains=[s['incremental_gain'] for s in stages], stages=stages,
                  convention='Through order k means coefficients X0^0,...,X0^k. Its polynomial kernel consists of polynomials divisible by X0^(k+1).',
                  coupling='Layer k is applied to the preceding systematic kernel in the original coefficient coordinates. No independent layer ranks are added.')
    if detailed:
        R = through_two['vectors']
        polynomial_image = image_on_vectors(matrix, R)
        certificate = incoming.matrix_certificate(polynomial_image)
        selected = certificate['rank_certificate']['nonzero_minor']['columns']
        expected = full_rank-stages[2]['cumulative_rank']
        assert len(selected) == expected
        basis_polynomials = [[row[j] for row in polynomial_image] for j in selected]
        assert all(value == 0 for poly in basis_polynomials for exponent, value in zip(exponents, poly)
                   if exponent[0] < 3)
        assert len(R)-expected == columns-full_rank
        result['divisible_by_X0_cubed'] = dict(
            source_coefficient_kernel_vectors=R,
            retained_original_free_columns=through_two['free_columns'],
            coefficient_kernel_dimension=len(R), nonzero_polynomial_dimension=expected,
            zero_polynomial_relation_dimension=columns-full_rank,
            image_certificate=certificate,
            independent_nonzero_polynomial_kernel_vector_indices=selected,
            independent_polynomial_coefficient_vectors=basis_polynomials,
            next_layer_stage_index=3,
            prior_coefficients_zero_verified=True,
            interpretation='The listed kernel vectors use the original N generator labels. Selected vectors form a basis of the polynomial image; the other kernel directions are not asserted individually to be zero polynomials.')
    return result


def two_block_off_axis_interpolation():
    """One specified 10-by-10 cubic minor, with no fixture or minor scan."""
    times = sparse.factors(2, 'economic')
    tables = sparse.coefficient_tables(G, times)
    exponents = path.monomials(3)
    points, labels, raw_points, denominators = [], [], [], []
    for t, table in enumerate(tables, start=2):
        definitions = [(dict(kind='same_block_intersection', t=t, a=a, b=b),
                        table[a], table[b]) for a, b in ((0, 1), (0, 2), (1, 2))]
        definitions += [(dict(kind='matching_coordinate', t=t, a=a), table[a], path.AXES[a])
                        for a in (1, 2)]
        for label, left, right in definitions:
            raw = residue.cross(left, right, P)
            assert raw[0], ('Off-axis normalization denominator is zero.', label)
            assert residue.dot(left, raw, P) == residue.dot(right, raw, P) == 0
            point = [x*pow(raw[0], -1, P) % P for x in raw]
            assert point[0] == 1
            points.append(point)
            raw_points.append(raw)
            denominators.append(raw[0])
            labels.append(label)
    assert len({tuple(point) for point in points}) == 10
    # C_t=L_(t,1)*L_(t,2) vanishes at its five points and separates the other block.
    separator_values = [[residue.dot(table[1], point, P)*residue.dot(table[2], point, P) % P
                         for point in points] for table in tables]
    for t, values in enumerate(separator_values):
        assert all(value == 0 for i, value in enumerate(values) if i//5 == t)
        assert all(value != 0 for i, value in enumerate(values) if i//5 != t)
    matrix = [path.monomial_values(exponents, point) for point in points]
    certificate = incoming.matrix_certificate(matrix)
    result = dict(prime=P, G=G, time_fixture='economic', time_factors=times,
                  row_point_labels=labels, raw_cross_product_points=raw_points,
                  normalized_points=points, point_normalization_denominators=denominators,
                  all_normalization_denominators_are_units=True,
                  point_convention='P_ab=cross(L_a,L_b), Q_a=cross(L_a,e_a), normalized to X0=1. Per block: P01,P02,P12,Q1,Q2.',
                  monomial_column_labels=exponents, cubic_evaluation_matrix=matrix,
                  certificate=certificate,
                  determinant_convention='Original listed point-row and monomial-column order, after X0=1 normalization.',
                  quadratic_separator_values=separator_values,
                  own_five_points_zero_and_other_five_units_verified=True,
                  scope='One specified two-block cubic interpolation matrix at the existing economic fixture. No scan and no actual-source rank implication are asserted here.')
    print(json.dumps(dict(two_block_off_axis_cubic_rank=certificate['rank_certificate']['rank'],
                          determinant_mod_prime=certificate['rank_certificate']['determinant_mod_prime'])), flush=True)
    return result


def calculate(m, saved):
    started = time.monotonic()
    times = sparse.factors(m, 'economic')
    tables = sparse.coefficient_tables(G, times)
    A = [[list(row) for row in G] for _ in range(2)]+tables
    paths, polynomials, D = path.path_polynomials(tables)
    exponents = path.monomials(3*m)
    assert exponents == sorted(exponents)
    raw = [[poly.get(exponent, 0) for poly in polynomials] for exponent in exponents]
    Dcolumn = [D.get(exponent, 0) for exponent in exponents]
    C22 = 1
    for table in tables:
        C22 = C22*table[2][2] % P
    assert C22
    normalized = [row[:-1]+[(row[-1]-d*pow(C22, -1, P)) % P]
                  for row, d in zip(raw, Dcolumn)]
    _, columns = schur.canonical_labels(m+2)
    labels, terms, gauge, _, coefficients = component.generators(m, columns)
    W = path.marked_word_coefficients(m, A, paths, columns)
    Cpath = [[-x % P for x in row] for row in component.apply_generators(W, terms)]
    all2 = paths.index((2,)*m)
    assert all(Cpath[all2][j] == (-C22 if label['kind'] == 'long_empty' and label['a'] == 2 else 0) % P
               for j, label in enumerate(labels))
    actual = schur.matrix_product(normalized, Cpath)
    checks = path.ordinary_checks(m, A, tables, paths, columns, labels, terms, gauge,
                                 W, Cpath, exponents, raw, normalized, actual, Dcolumn, C22)
    assert saved['prime'] == P and saved['G'] == [list(row) for row in G]
    assert saved['time_factors'] == [list(pair) for pair in times]
    assert residue.matrix_hash(actual) == saved['actual_N_polynomials']['sha256']
    assert residue.matrix_hash(normalized) == saved['normalized_path_polynomials']['sha256']

    source = normal_filtration(actual, exponents, detailed=True)
    ambient = normal_filtration(normalized, exponents)
    assert source['full_rank'] == ambient['full_rank'] == {4: 66, 5: 105}[m]
    assert source['cumulative_ranks'] == ambient['cumulative_ranks']
    assert source['incremental_gains'] == ambient['incremental_gains']
    result = dict(m=m, prime=P, G=G, time_fixture='economic', time_factors=times,
                  cleared_polynomial='p2=D*R2/X2, D=product_(t,a) L_(t,a).', degree=3*m,
                  monomial_row_labels=exponents,
                  row_order='Increasing X0 exponent, then increasing X1 exponent; X2 exponent completes degree3m.',
                  original_source_column_labels=columns,
                  N_generator_labels=labels,
                  N_generator_source_terms=terms, N_generator_local_E_gauge=gauge,
                  N_source_coefficient_matrix_sha256=residue.matrix_hash(coefficients),
                  N_path_coefficient_matrix_sha256=residue.matrix_hash(Cpath),
                  path_column_labels=paths,
                  normalized_path_definition='prod_t f_(t,a_t), with D/C22 subtracted only from the all-2 path; f_(t,a)=X_a*product_(b!=a)L_(t,b).',
                  all2_coefficient=C22,
                  actual_N_coefficient_matrix=actual,
                  normalized_path_coefficient_matrix=normalized,
                  actual_N_filtration=source, normalized_path_filtration=ambient,
                  every_normal_layer_rank_matches=True,
                  previous_polynomial_coefficient_hashes_match=True,
                  previous_result_reference='source24-path-component-results.json; matching hashes, no old residue/axis rank calculation rerun.',
                  ordinary_word_and_clearing_checks=checks,
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(m=m, cumulative=source['cumulative_ranks'], gains=source['incremental_gains'],
                          X0_cubed_polynomial_kernel=source['divisible_by_X0_cubed']['nonzero_polynomial_dimension'],
                          ambient_matches=True, elapsed_seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-path-component-results.json').read_text())
    started, cases, limitation = time.monotonic(), [], None
    interpolation = None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        interpolation = two_block_off_axis_interpolation()
        for m in (4, 5):
            prior = next(case for case in saved['cases'] if case['m'] == m)
            cases.append(calculate(m, prior))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite coupled normal-layer investigation for actual N and normalized pure paths.',
                  scope='Only m=4,5 at the saved economic fixtures. Equal finite layer ranks do not prove an all-m pattern. Coefficient kernels include the full polynomial-map relations; nonzero polynomial kernels are reported separately.',
                  elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(), bounded_limitation=limitation,
                  two_block_off_axis_interpolation=interpolation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('elapsed_seconds', 'maximum_rss_bytes', 'bounded_limitation')}), flush=True)


if __name__ == '__main__':
    main()
