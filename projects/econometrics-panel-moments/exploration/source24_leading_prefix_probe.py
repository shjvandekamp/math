#!/usr/bin/env python3
"""Six actual LC31 preimages and LC32 prefix defects at q=4 and q=5.

For a != b and third state i, solve the recorded ordinary evaluations of
  delta_ab = R(c) K_q + h v_i (I-K_q),
  delta_ab = p_qab e_b (Q K_q-K_q Q),  Q=K_1...K_(q-1).
R(c) uses the actual old E/F columns, including their A_t(a,b) factors.
The scalar basis for h is 1 and X_a/L_ta, omitting only (q,i).
After fitting and separate ordinary-point checks, a triangular unisolvent
grid certifies the identities as rational-function identities over F_p.
D_old*Delta_q clears every component, with homogeneous degree 3q+4.

The actual source prefix is computed from its coefficients, not guessed:
  I_old(c)_b = X_b [sum_t lambda_tb
                    + sum_ta A_t(a,b)(sum_s alpha_tsab-lambda_ta) X_a/L_ta].
Subtracting h v_i gives all 9q old-pole coefficients in an explicit basis.
Support, per-time ranks and nonzero minors are retained to probe structure.
The fixed six rows at each time are states a=0,1 and outputs b=0,1,2.
No all-q conclusion or symbolic parameter formula is inferred.
"""

import argparse
import itertools
import json
from pathlib import Path
import signal
import time

import source24_last_time_coalescence as collision
import source24_odd_incoming as incoming
import source24_residue_differences as geometry


P, G = collision.P, collision.G
residue, sparse, schur = incoming.residue, incoming.sparse, incoming.schur
QCOUNT = 4


def certificate(matrix):
    return dict(shape=[len(matrix), len(matrix[0])], sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def scalar_labels(q, i):
    return [('constant',)] + [('pole', t, a) for t in range(q) for a in range(3)
                             if (t, a) != (q - 1, i)]


def scalar_values(labels, ratios):
    return [1 if label[0] == 'constant' else ratios[label[1]][label[2]] for label in labels]


def prepare_point(tables, X, source_labels, defects, raw_control):
    q, last = len(tables), len(tables) - 1
    old = collision.actual_values(tables, X)
    kernels = [residue.ordinary_kernel(tables, t, X, P) for t in range(q)]
    K, Q = kernels[-1], residue.word_product(kernels, list(range(last)), P)
    appended = residue.matmul(old, K, P)
    commutator = schur.matrix_difference(residue.matmul(Q, K, P), residue.matmul(K, Q, P))
    delta = [[X[a] * K[a][b] * entry % P for entry in commutator[b]] for a, b in defects]
    rows_v = [[tables[-1][i][b] * X[b] % P for b in range(3)] for i in range(3)]
    prefix_rows = schur.matrix_difference(rows_v, residue.matmul(rows_v, K, P))
    ratios = [[X[a] * pow(residue.dot(tables[t][a], X, P), -1, P) % P
               for a in range(3)] for t in range(q)]
    for row in appended + delta + prefix_rows:
        assert sum(row) % P == 0
    if raw_control:
        full = collision.actual_values(tables + [tables[-1]], X)
        full_index = {label: k for k, label in enumerate(collision.labels(q + 1))}
        for column, (a, b) in enumerate(defects):
            W = full[full_index['F', last, q, a, b]]
            copied = full[full_index['F', last, 0, a, b]]
            assert [(x - y) % P for x, y in zip(W, copied)] == delta[column]
    return dict(X=X, old=old, kernels=kernels, appended=appended, delta=delta,
                rows_v=rows_v, prefix_rows=prefix_rows, ratios=ratios,
                raw_control=raw_control)


def system_rows(points, labels, i, selected_defects):
    matrix, rhs = [], []
    for point in points:
        hvalues = scalar_values(labels, point['ratios'])
        for component in (0, 1):
            matrix.append([row[component] for row in point['appended']] +
                          [h * point['prefix_rows'][i][component] % P for h in hvalues])
            rhs.append([point['delta'][column][component] for column in selected_defects])
    return matrix, rhs


def source_prefix_coefficients(q, tables, source_labels, coefficients):
    constant = [0] * 3
    poles = {(t, a, b): 0 for t in range(q) for a in range(3) for b in range(3)}
    for label, value in zip(source_labels, coefficients):
        if label[0] == 'E':
            _, t, a = label
            constant[a] = (constant[a] + value) % P
            for b in range(3):
                poles[t, a, b] = (poles[t, a, b] - value * tables[t][a][b]) % P
        else:
            _, t, _, a, b = label
            poles[t, a, b] = (poles[t, a, b] + value * tables[t][a][b]) % P
    return constant, poles


def check_holdout(point, tables, source_labels, i, hlabels, coefficients, hcoefficients,
                  defect_column, prefix_constant, prefix_poles, defect_constant, defect_poles):
    X = point['X']
    h = sum(x * y for x, y in zip(scalar_values(hlabels, point['ratios']), hcoefficients)) % P
    actual = [(sum(c * row[b] for c, row in zip(coefficients, point['appended'])) +
               h * point['prefix_rows'][i][b]) % P for b in range(3)]
    assert actual == point['delta'][defect_column]
    direct_prefix = [0] * 3
    for label, value, old_row in zip(source_labels, coefficients, point['old']):
        if label[0] == 'E':
            for b in range(3):
                direct_prefix[b] = (direct_prefix[b] + value * old_row[b]) % P
        else:
            _, t, _, a, b = label
            direct_prefix[b] = (direct_prefix[b] + value * X[a] * point['kernels'][t][a][b]) % P
    for b in range(3):
        expanded = X[b] * (prefix_constant[b] + sum(
            value * point['ratios'][t][a] for (t, a, out), value in prefix_poles.items() if out == b)) % P
        assert direct_prefix[b] == expanded
        defect_expanded = X[b] * (defect_constant[b] + sum(
            value * point['ratios'][t][a] for (t, a, out), value in defect_poles.items() if out == b)) % P
        assert (direct_prefix[b] - h * point['rows_v'][i][b]) % P == defect_expanded


def interpolation_grid(tables):
    """A translated total-degree grid, with every old row form a unit.

    The Newton basis indexed by i+j<=d is
    prod_(r<i)(x-c-r) prod_(s<j)(y-e-s). Ordering nodes and basis by
    total degree gives a triangular evaluation matrix with diagonal i!j!.
    Since p>d, its determinant is nonzero; no sampled-rank assumption is used.
    """
    q, degree = len(tables), 3 * len(tables) + 4
    indices = [(i, total - i) for total in range(degree + 1) for i in range(total + 1)]
    assert P > degree and len(indices) == (degree + 1) * (degree + 2) // 2
    rejected = []
    for attempt in range(1000):
        c, e = 2 + attempt, 3 + 2 * attempt
        points = [(1, c + i, e + j) for i, j in indices]
        bad = next(((point_id, t, a) for point_id, X in enumerate(points)
                    for t in range(q) for a in range(3)
                    if residue.dot(tables[t][a], X, P) == 0), None)
        if bad is None:
            break
        rejected.append(dict(offsets=[c, e], first_zero=dict(point=bad[0], t=bad[1], a=bad[2])))
    else:
        raise ValueError('No unit-denominator grid among the prescribed small translates.')
    factorials = [1]
    for k in range(1, degree + 1):
        factorials.append(factorials[-1] * k % P)
    newton_determinant = 1
    for i, j in indices:
        newton_determinant = newton_determinant * factorials[i] * factorials[j] % P
    assert newton_determinant
    clearing_values = []
    for X in points:
        blocks = []
        for t in range(q):
            block = 1
            for a in range(3):
                block = block * residue.dot(tables[t][a], X, P) % P
            assert block
            blocks.append(block)
        common = blocks[-1]
        for block in blocks:
            common = common * block % P
        assert common
        clearing_values.append(common)
    return dict(degree=degree, offsets=[c, e], rejected_offsets=rejected,
                indices=indices, points=points, point_count=len(points),
                all_row_denominators_units=True, common_denominator_values=clearing_values,
                newton_evaluation_determinant_mod_prime=newton_determinant,
                newton_basis='prod_(r<i)(x-c-r) prod_(s<j)(y-e-s), ordered by i+j then i.',
                unisolvence_argument='The Newton polynomials have distinct leading monomials x^i*y^j and form a basis for total degree <=d. At a node of smaller total degree at least one falling-factorial factor vanishes; distinct nodes of equal degree also give zero. Diagonal entries are i!j!, nonzero because p>d.',
                denominator='D_old*Delta_last, where Delta_t=prod_a L_ta and D_old is the product over all q old times. Delta_last is Delta_(q-1) in the stored zero-based labels, and Delta_q in the paper.',
                degree_argument='Every old E/F term uses each old block at most once. Appending K_q uses block q at most twice. The h*v_i*(I-K_q) and commutator terms have the same bounds. D_old*Delta_q of degree 3q+3 clears them; each row is homogeneous of degree 1, giving degree 3q+4. Setting X0=1 gives total degree at most d in X1,X2.',
                arbitrary_X_conclusion='Zero evaluations on this unisolvent grid force each cleared affine polynomial to be zero. Homogeneity then forces the homogeneous cleared polynomial to be zero, including on X0=0. The identities hold over F_p(X0,X1,X2), and at every point where the common denominator is nonzero.')


def calculate(q=QCOUNT):
    assert q in (4, 5), 'Only the two prescribed cases are authorized.'
    times = sparse.factors(q, 'economic')
    tables = sparse.coefficient_tables(G, times)
    padded = [[list(row) for row in G] for _ in range(2)] + tables
    geometry_record = geometry.check_geometry(q, padded)
    source_labels = collision.labels(q)
    defect_labels = [(a, b) for a in range(3) for b in range(3) if a != b]
    pole_labels = [(t, a, b) for t in range(q) for a in range(3) for b in range(3)]
    unknown_count, control_count = len(source_labels) + 3 * q, 12
    fit_count = (unknown_count + 1) // 2 + 12
    assert len(source_labels) == 3 * q * (3 * q - 2)
    Xpoints, skipped = collision.ordinary_points(tables, fit_count + control_count)
    points = [prepare_point(tables, X, source_labels, defect_labels, j < 3 or j >= fit_count)
              for j, X in enumerate(Xpoints)]
    fit, controls = points[:fit_count], points[fit_count:]
    source_coefficients = [[0] * 6 for _ in source_labels]
    defect_matrix = [[0] * 6 for _ in pole_labels]
    defect_constants = [[0] * 6 for _ in range(3)]
    systems, support, recovered = [], [None] * 6, []
    for i in range(3):
        selected = [column for column, (a, b) in enumerate(defect_labels) if i not in (a, b)]
        hlabels = scalar_labels(q, i)
        assert len(hlabels) == 3 * q
        matrix, rhs = system_rows(fit, hlabels, i, selected)
        matrix_certificate = certificate(matrix)
        rank_certificate = matrix_certificate['rank_certificate']
        assert rank_certificate['rank'] == unknown_count, ('Prescribed system not injective.', i)
        rows = rank_certificate['nonzero_minor']['rows']
        selected_matrix, selected_rhs = [matrix[r] for r in rows], [rhs[r] for r in rows]
        solution, solve_certificate = incoming.solve_old_source(selected_matrix, selected_rhs)
        assert solution is not None and solve_certificate['invertible']
        assert solve_certificate['determinant_mod_prime'] == rank_certificate['nonzero_minor']['determinant_mod_prime']
        assert schur.matrix_product(matrix, solution) == rhs
        for local, column in enumerate(selected):
            coefficients = [row[local] for row in solution[:len(source_labels)]]
            hcoefficients = [row[local] for row in solution[len(source_labels):]]
            constant, poles = source_prefix_coefficients(q, tables, source_labels, coefficients)
            hmap = {(label[1], label[2]): value for label, value in zip(hlabels, hcoefficients)
                    if label[0] == 'pole'}
            dconstant = [(constant[b] - tables[-1][i][b] * hcoefficients[0]) % P for b in range(3)]
            dpoles = {(t, a, b): (value - tables[-1][i][b] * hmap.get((t, a), 0)) % P
                      for (t, a, b), value in poles.items()}
            for point in controls:
                check_holdout(point, tables, source_labels, i, hlabels, coefficients, hcoefficients,
                              column, constant, poles, dconstant, dpoles)
            recovered.append((i, hlabels, coefficients, hcoefficients, column,
                              constant, poles, dconstant, dpoles))
            for row, value in enumerate(coefficients):
                source_coefficients[row][column] = value
            for row, label in enumerate(pole_labels):
                defect_matrix[row][column] = dpoles[label]
            for b in range(3):
                defect_constants[b][column] = dconstant[b]
            source_indices = [r for r, value in enumerate(coefficients) if value]
            source_groups = []
            for t, s in itertools.permutations(range(q), 2):
                indices = [r for r in source_indices if source_labels[r][0] == 'F'
                           and source_labels[r][1:3] == (t, s)]
                if indices:
                    source_groups.append(dict(t=t, s=s, count=len(indices), source_indices=indices))
            support[column] = dict(defect_label=defect_labels[column], third_state=i,
                                   source_nonzero_count=len(source_indices), source_nonzero_indices=source_indices,
                                   source_E_indices=[r for r in source_indices if source_labels[r][0] == 'E'],
                                   source_F_groups=source_groups,
                                   h_nonzero_terms=[dict(label=label, coefficient=value)
                                                    for label, value in zip(hlabels, hcoefficients) if value],
                                   defect_nonzero_rows=[r for r, label in enumerate(pole_labels) if dpoles[label]])
        systems.append(dict(third_state=i, defect_column_indices=selected, h_labels=hlabels,
                            omitted_h_label=['pole', q - 1, i], matrix=matrix_certificate,
                            rhs_sha256=residue.matrix_hash(rhs), solution=solution,
                            solution_sha256=residue.matrix_hash(solution), solve_certificate=solve_certificate,
                            fit_all_rows_verified=True, holdout_three_component_rows=control_count * 2 * 3,
                            direct_source_prefix_control=True))
    grid = interpolation_grid(tables)
    for X in grid['points']:
        point = prepare_point(tables, X, source_labels, defect_labels, False)
        for data in recovered:
            check_holdout(point, tables, source_labels, *data)
    grid.update(all_six_preimage_identities_verified=True,
                preimage_component_checks=grid['point_count'] * 6 * 3,
                both_prefix_expansions_verified=True,
                prefix_component_checks=grid['point_count'] * 6 * 3 * 2,
                maximum_cleared_residual_mod_prime=0)
    per_time = [dict(t=t, certificate=certificate(defect_matrix[9 * t:9 * (t + 1)]),
                     fixed_six_row_labels=pole_labels[9 * t:9 * t + 6],
                     fixed_six_by_six_matrix=defect_matrix[9 * t:9 * t + 6],
                     fixed_six_certificate=certificate(defect_matrix[9 * t:9 * t + 6]))
                for t in range(q)]
    cumulative = [dict(through_time=t, certificate=certificate(defect_matrix[:9 * (t + 1)])) for t in range(q)]
    return dict(q=q, prime=P, G=G, time_factors=times, coefficient_tables=tables,
                geometry=geometry_record, indexing='All times, states, matrix row indices and source labels are zero based.',
                source_column_labels=source_labels, defect_column_labels=defect_labels,
                fit_points=Xpoints[:fit_count], holdout_points=Xpoints[fit_count:], skipped_points=skipped,
                fit_row_order='For each fit point, component 0 then component 1.',
                actual_raw_difference_controls=dict(points=[Xpoints[j] for j in range(len(points))
                                                            if points[j]['raw_control']],
                                                   vector_checks=(3 + control_count) * 6,
                                                   formula='W_ab-C(F_(q,first,a,b))=p_qab e_b(QK-KQ)'),
                systems=systems, arbitrary_X_identity_control=grid,
                source_coefficient_matrix=source_coefficients,
                source_coefficients_sha256=residue.matrix_hash(source_coefficients),
                prefix_defect=dict(row_labels=pole_labels,
                                   row_basis='At row (t,a,b), the vector is X_a X_b/L_ta times e_b.',
                                   matrix=defect_matrix, certificate=certificate(defect_matrix),
                                   constant_coefficients=defect_constants,
                                   constant_basis='X_b e_b, b=0,1,2; excluded from the pole rank.',
                                   per_time=per_time, cumulative_time=cumulative), support=support)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    previous = json.loads(args.output.read_text()) if args.output.exists() else None
    previous_q4 = (next((case for case in previous['cases'] if case['q'] == 4), None)
                   if previous and 'cases' in previous else previous)

    def guard(_signal, _frame):
        if time.monotonic() - started >= 27 or collision.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, 0.05, 0.05)
    cases, limitation = [], None
    try:
        cases.append(calculate(4))
        if previous_q4 is not None:
            assert cases[0]['source_coefficients_sha256'] == previous_q4['source_coefficients_sha256']
            assert cases[0]['prefix_defect']['matrix'] == previous_q4['prefix_defect']['matrix']
        if time.monotonic() - started < 15:
            cases.append(calculate(5))
        else:
            limitation = 'q=5 omitted to preserve the completed q=4 certificate within the guard.'
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    if not cases and previous_q4 is not None:
        cases = [previous_q4]
        limitation = 'Previous q=4 data preserved; the new grid check did not finish: ' + str(limitation)
    result = dict(schema_version=2,
                  status='Prescribed q=4 and q=5 leading-prefix recoveries and fixed six-row diagnostics.',
                  scope='At each completed fixture, unisolvent-grid clearing proves the preimage identities over F_p(X0,X1,X2). The defect rank and fixed-row pattern are finite parameter witnesses, not all-q claims.',
                  paper_reference='research/SOURCE24_LAST_TIME_COALESCENCE.md LC30-LC32',
                  resource_limits=dict(seconds=28, computation_alarm_seconds=27,
                                       maximum_rss_bytes=95 * 1024 ** 2),
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=collision.maximum_rss_bytes(),
                  resource_measurement_scope='Calculation before JSON serialization; external time records complete-process use.',
                  previous_q4_coefficients_and_defect_preserved=previous_q4 is not None,
                  bounded_limitation=limitation, cases=cases)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(cases=[dict(q=case['q'],
                                     rank=case['prefix_defect']['certificate']['rank_certificate']['rank'],
                                     grid_points=case.get('arbitrary_X_identity_control', {}).get('point_count'),
                                     fixed_six_determinants=[x['fixed_six_certificate']['rank_certificate']['determinant_mod_prime']
                                                             for x in case['prefix_defect']['per_time']
                                                             if 'fixed_six_certificate' in x]) for case in cases],
                          elapsed_seconds=result['elapsed_seconds'], maximum_rss_bytes=collision.maximum_rss_bytes(),
                          bounded_limitation=limitation)))
    if limitation:
        raise SystemExit(2)


if __name__ == '__main__':
    main()
