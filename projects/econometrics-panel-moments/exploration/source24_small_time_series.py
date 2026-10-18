#!/usr/bin/env python3
"""One prescribed m=3 small-time residue-series calculation, not a sweep.

Work over F_1000003 with G=I+11^T, g=(2,1,1),
a=(5/4,3/2,7/4), b=(1,2,3), u_t=a_t*epsilon,
w_t=b_t*epsilon^3, and X=(1,-r/epsilon,r/epsilon-2).
The 18 columns are the actual ordered H_tc,J_tc, multiplied respectively
by (1,epsilon,epsilon) and (epsilon,epsilon^2,epsilon^2).
The observations are ordinary-r residues of output 1 and output 2/epsilon^2.

Compute their Taylor series modulo epsilon^17. Symbolically removing the
epsilon^2 factor from the last kernel's third column avoids an unrecorded
precision loss. Singular kernels are replaced by their rank-one row-form
residues; their ordinary-r slopes are divided out separately.

A separate scalar evaluation of this same recipe at epsilon=2 is compared
with the existing actual paired-matrix evaluator, including chart, column,
and output normalizations. No Taylor polynomial is evaluated at a unit.
Minimum-valuation complete-pivot Gaussian elimination uses only unit-series
inverses and records each pivot and its precision. No larger order or
replacement parameter fixture is tried if this calculation is incomplete.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import time
import traceback

import source24_residue as residue
import source24_equal_weight_boundary as paired


P = 1000003
PRECISION = 17  # Known coefficients 0,...,16, with error O(epsilon^17).
G = [[1 + int(i == j) for j in range(3)] for i in range(3)]
A = [5 * pow(4, -1, P) % P, 3 * pow(2, -1, P) % P, 7 * pow(4, -1, P) % P]
B = [1, 2, 3]
LABELS = [[kind, t + 1, c] for kind in ('H', 'J') for t in range(3) for c in range(3)]


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()


class Scalar:
    """Plain rational finite-field evaluation, independent of Taylor truncation."""

    @staticmethod
    def c(value):
        return value % P

    @staticmethod
    def add(left, right):
        return (left + right) % P

    @staticmethod
    def neg(value):
        return -value % P

    @staticmethod
    def mul(left, right):
        return left * right % P

    @staticmethod
    def scale(value, scalar):
        return value * scalar % P

    @staticmethod
    def inv(value):
        assert value
        return pow(value, -1, P)

    @staticmethod
    def iszero(value):
        return value == 0

    @staticmethod
    def constant(value):
        return value


class Taylor:
    """F_p[[epsilon]]/(epsilon^17); inverse is allowed only for units."""

    def __init__(self):
        self.operations = dict(add=0, neg=0, mul=0, scale=0, inverse=0)

    @staticmethod
    def c(value):
        return (value % P,) + (0,) * (PRECISION - 1)

    @staticmethod
    def epsilon():
        return (0, 1) + (0,) * (PRECISION - 2)

    def add(self, left, right):
        self.operations['add'] += 1
        return tuple((a + b) % P for a, b in zip(left, right))

    def neg(self, value):
        self.operations['neg'] += 1
        return tuple(-a % P for a in value)

    def mul(self, left, right):
        self.operations['mul'] += 1
        return convolution(left, right, PRECISION)

    def scale(self, value, scalar):
        self.operations['scale'] += 1
        return tuple(a * scalar % P for a in value)

    def inv(self, value):
        self.operations['inverse'] += 1
        return unit_inverse(value, PRECISION)

    @staticmethod
    def iszero(value):
        return not any(value)

    @staticmethod
    def constant(value):
        return value[0]


def convolution(left, right, precision):
    answer = [0] * precision
    for i, value in enumerate(left[:precision]):
        if value:
            for j, other in enumerate(right[:precision - i]):
                if other:
                    answer[i + j] += value * other
    return tuple(value % P for value in answer)


def unit_inverse(value, precision):
    assert value[0], 'Attempted inversion of a nonunit Taylor series.'
    inverse_constant = pow(value[0], -1, P)
    answer = [inverse_constant]
    for k in range(1, precision):
        answer.append(-inverse_constant * sum(value[i] * answer[k - i]
                                              for i in range(1, k + 1)) % P)
    return tuple(answer)


def rowmul(field, vector, matrix):
    result = []
    for j in range(3):
        value = field.c(0)
        for i in range(3):
            value = field.add(value, field.mul(vector[i], matrix[i][j]))
        result.append(value)
    return result


def normalized_residues(field, epsilon):
    """Actual residue formula, shared by scalar and formal-series backends."""
    one, zero = field.c(1), field.c(0)
    epsilon2 = field.mul(epsilon, epsilon)
    epsilon3 = field.mul(epsilon2, epsilon)
    matrix, nodes = [], []
    for u in range(3):
        for d in range(3):
            denominator = field.add(field.c(G[d][1] * A[u]),
                                    field.scale(epsilon2, -G[d][2] * B[u]))
            numerator = field.add(field.c(G[d][0]),
                                  field.scale(epsilon3, -2 * G[d][2] * B[u]))
            r = field.mul(numerator, field.inv(denominator))
            slope = field.neg(denominator)
            inverse_slope = field.inv(slope)
            r_minus_2e = field.add(r, field.scale(epsilon, -2))
            h = [one, field.neg(r), r_minus_2e]
            vbar = [field.scale(epsilon, 2), field.neg(r), r_minus_2e]
            forms, ordinary, last = [], {}, {}
            for t in range(3):
                weighted = [one, field.scale(r, -A[t]),
                            field.scale(field.mul(epsilon2, r_minus_2e), B[t])]
                weighted_last = [weighted[0], weighted[1], field.scale(r_minus_2e, B[t])]
                L = []
                for i in range(3):
                    value = zero
                    for j in range(3):
                        value = field.add(value, field.scale(weighted[j], G[i][j]))
                    L.append(value)
                forms.append(L)
                if t == u:
                    assert field.iszero(L[d]), 'The moving node is not the selected pole.'
                    assert all(field.constant(L[i]) for i in range(3) if i != d)
                    # Only the selected row contributes to the row-form residue.
                    ordinary[t] = [[field.scale(weighted[j], G[i][j]) if i == d else zero
                                    for j in range(3)] for i in range(3)]
                    last[t] = [[field.scale(weighted_last[j], G[i][j]) if i == d else zero
                                for j in range(3)] for i in range(3)]
                else:
                    assert all(field.constant(value) for value in L), 'Another pole collides.'
                    inverses = [field.inv(value) for value in L]
                    ordinary[t] = [[field.mul(field.scale(weighted[j], G[i][j]), inverses[i])
                                    for j in range(3)] for i in range(3)]
                    last[t] = [[field.mul(field.scale(weighted_last[j], G[i][j]), inverses[i])
                                for j in range(3)] for i in range(3)]

            def word(vector, indices):
                assert indices, 'Last-column normalization needs a nonempty word.'
                for index, t in enumerate(indices):
                    vector = rowmul(field, vector, last[t] if index == len(indices) - 1 else ordinary[t])
                return vector

            columns = []
            for kind, t1, c in LABELS:
                t = t1 - 1
                if kind == 'H':
                    indices = [t] + [s for s in range(3) if s != t]
                    row = word([one if j == c else zero for j in range(3)], indices)
                    factor = field.neg(field.mul(h[c], inverse_slope))
                elif t == u and c != d:
                    row, factor = [zero, zero, zero], zero
                else:
                    indices = [s for s in range(3) if s != t]
                    row = word(vbar, indices)
                    factor = field.scale(field.mul(h[c], inverse_slope), -G[c][0])
                    if t != u:
                        factor = field.mul(factor, field.inv(forms[t][c]))
                row = [field.mul(factor, value) for value in row]
                assert field.iszero(field.add(field.add(row[0], row[1]), field.mul(epsilon2, row[2])))
                columns.append(row)
            matrix.extend([[column[j] for column in columns] for j in (1, 2)])
            nodes.append(dict(block=u + 1, state=d, r=r, ordinary_r_slope=slope,
                              row_forms=forms, leading_r=field.constant(r),
                              all_other_row_forms_units=True))
    assert len(matrix) == 18 and all(len(row) == 18 for row in matrix)
    return matrix, nodes


def scalar_control():
    epsilon = 2  # The sole unit specialization; not a Taylor-polynomial evaluation.
    matrix, nodes = normalized_residues(Scalar(), epsilon)
    times = [[1, 1, 1]] + [[1, a * epsilon % P, b * pow(epsilon, 3, P) % P]
                           for a, b in zip(A, B)]
    tables = [[[G[i][j] * factors[j] % P for j in range(3)] for i in range(3)]
              for factors in times]
    actual = paired.calculate_sector(tables, 0)
    assert actual['column_labels'] == LABELS
    transformed = []
    for i, node in enumerate(nodes):
        r, slope = node['r'], node['ordinary_r_slope']
        chart = [1, -r * pow(epsilon, -1, P) % P, (r * pow(epsilon, -1, P) - 2) % P]
        assert sum(chart) % P == P - 1
        assert actual['node_records'][i]['point'] == [-x % P for x in chart]
        row0, row1 = actual['matrix'][2 * i:2 * i + 2]
        transformed_rows = [[], []]
        for j, (kind, _t, c) in enumerate(LABELS):
            power = int(c != 0) + int(kind == 'J')
            factor = pow(epsilon, power, P) * pow(slope, -1, P) % P
            transformed_rows[0].append(row1[j] * factor % P)
            transformed_rows[1].append(-(row0[j] + row1[j]) * factor * pow(epsilon ** 2, -1, P) % P)
        transformed.extend(transformed_rows)
    assert matrix == transformed, 'Unit control disagrees with the existing actual paired evaluator.'
    return dict(epsilon=epsilon, time_factors=times, moving_nodes=nodes,
                recipe_matrix=matrix, recipe_matrix_sha256=residue.matrix_hash(matrix),
                existing_actual_matrix=actual['matrix'], existing_actual_certificate=actual['certificate'],
                existing_actual_polynomial_clearing_checks=actual['polynomial_clearing_component_checks'],
                transformed_actual_matrix_sha256=residue.matrix_hash(transformed),
                comparisons=18 * 18, all_matched=True,
                projective_rule='Existing points are -X; row-form residues are homogeneous of degree two, so they agree. Divide by dL/dr, apply the column powers, and use output2=-output0-output1.',
                warning='This control evaluates the rational construction directly. It does not evaluate truncated Taylor series at epsilon=2.')


def valuation(value):
    return next((i for i, coefficient in enumerate(value) if coefficient), PRECISION)


def determinant_certificate(matrix):
    """Complete-pivot elimination, retaining absolute entry precision 17.

    At a minimum-valuation pivot v every residual entry is divisible by e^v.
    Write the pivot e^v*u and compute the Schur update as
      e^v * (a_ij/e^v - (a_ik/e^v)*u^-1*(a_kj/e^v)).
    The expression in parentheses is known modulo e^(17-v), so its product
    with e^v is still known modulo e^17. Only the unit u is inverted.
    Thus no untracked precision loss accumulates. A pivot with valuation
    below 17 has an exact valuation and leading coefficient. The product
    gives the determinant leading term after the row and column signs.
    """
    work = [[tuple(entry) for entry in row] for row in matrix]
    row_ids, column_ids = list(range(18)), list(range(18))
    pivots, sign, determinant_order, coefficient = [], 1, 0, 1
    for k in range(18):
        v, i, j = min((valuation(work[i][j]), i, j) for i in range(k, 18) for j in range(k, 18))
        if v == PRECISION:
            return dict(complete=False, reason='Residual block is zero modulo epsilon^17; no higher precision was attempted.',
                        pivots=pivots, eliminated_size=k, residual_size=18-k,
                        determinant_order_lower_bound=determinant_order + (18-k) * PRECISION,
                        residual_block_sha256=digest([row[k:] for row in work[k:]]))
        if i != k:
            work[k], work[i] = work[i], work[k]
            row_ids[k], row_ids[i] = row_ids[i], row_ids[k]
            sign = -sign
        if j != k:
            for row in work:
                row[k], row[j] = row[j], row[k]
            column_ids[k], column_ids[j] = column_ids[j], column_ids[k]
            sign = -sign
        pivot = work[k][k]
        q = PRECISION - v
        inverse = unit_inverse(pivot[v:], q)
        assert convolution(pivot[v:], inverse, q) == (1,) + (0,) * (q - 1)
        pivots.append(dict(step=k, original_row=row_ids[k], original_column=column_ids[k],
                           row_swap_from=i, column_swap_from=j, valuation=v,
                           leading_coefficient=pivot[v], pivot_series=pivot,
                           absolute_entry_precision=PRECISION, unit_inverse_precision=q,
                           unit_inverse_verified=True,
                           residual_block_sha256=digest([row[k:] for row in work[k:]])))
        determinant_order += v
        coefficient = coefficient * pivot[v] % P
        for i2 in range(k + 1, 18):
            ratio = convolution(work[i2][k][v:], inverse, q)
            for j2 in range(k + 1, 18):
                product = convolution(ratio, work[k][j2][v:], q)
                updated = tuple((a - b) % P for a, b in zip(work[i2][j2][v:], product))
                work[i2][j2] = (0,) * v + updated
            work[i2][k] = (0,) * PRECISION
    return dict(complete=True, pivots=pivots, determinant_order=determinant_order,
                determinant_leading_coefficient_mod_prime=sign * coefficient % P,
                determinant_coefficient_within_requested_order=(determinant_order <= PRECISION - 1),
                permutation_sign=sign, final_original_rows=row_ids, final_original_columns=column_ids,
                pivot_valuation_multiplicities={str(v): sum(p['valuation'] == v for p in pivots)
                                                for v in sorted(set(p['valuation'] for p in pivots))},
                precision_argument='Minimum-valuation pivoting factors epsilon^v from the whole residual block before the unit Schur update, then restores it. Every residual entry retains absolute precision 17; each inverse has precision 17-v.',
                coefficient_argument='Every selected pivot has valuation below 17; its valuation and leading coefficient are exact. Multiply the eighteen pivot leading terms and the two permutation signs.')


def calculate(record):
    record['scalar_control'] = scalar_control()
    field = Taylor()
    matrix, nodes = normalized_residues(field, field.epsilon())
    leading_nodes = [node['leading_r'] for node in nodes]
    assert len(set(leading_nodes)) == 9 and all(leading_nodes)
    record.update(moving_nodes=nodes, leading_nodes_distinct=True, leading_node_count=9,
                  matrix_series=matrix, matrix_series_sha256=digest(matrix),
                  matrix_series_layout='[observation row][actual column][epsilon exponent 0,...,16]',
                  coefficient_matrix_sha256=[residue.matrix_hash([[entry[k] for entry in row] for row in matrix])
                                             for k in range(PRECISION)],
                  series_arithmetic_operations=field.operations,
                  leading_matrix_certificate=paired.certificate([[entry[0] for entry in row] for row in matrix]))
    record['determinant'] = determinant_certificate(matrix)
    leading_rank = record['leading_matrix_certificate']['rank_certificate']['rank']
    assert leading_rank <= 14, 'The prescribed leading-rank paper bound failed.'
    assert leading_rank == sum(p['valuation'] == 0 for p in record['determinant']['pivots'])
    if record['determinant']['complete']:
        assert record['determinant']['determinant_order'] >= 8, 'The prescribed determinant-order paper bound failed.'
    record['paper_bounds_verified_at_fixture'] = dict(leading_rank_at_most=14, determinant_order_at_least=8)


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
    source = Path(__file__)
    result = dict(scope='One prescribed m=3 small-time fixture; no parameter sweep, no increased precision, no all-length rank claim.',
                  prime=P, old_blocks=3, common_matrix=G, sector_normal=[2, 1, 1],
                  a_rational=['5/4', '3/2', '7/4'], a_mod_prime=A, b=B,
                  time_factors='(1,a_t*epsilon,b_t*epsilon^3)', moving_chart='X=(1,-r/epsilon,r/epsilon-2)',
                  column_labels=LABELS,
                  column_normalization=dict(H=[0, 1, 1], J=[1, 2, 2], convention='Powers of epsilon multiplying the actual columns.'),
                  row_labels=[[t+1, c, j] for t in range(3) for c in range(3) for j in (1, 2)],
                  row_convention='Ordinary-r residues of output 1 and output 2/epsilon^2, interleaved at the nine moving poles.',
                  coefficient_orders=list(range(PRECISION)), absolute_precision=PRECISION,
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  dependency_sha256={name: hashlib.sha256(source.with_name(name).read_bytes()).hexdigest()
                                     for name in ('source24_residue.py', 'source24_equal_weight_boundary.py')}, case={})
    failure = None
    try:
        calculate(result['case'])
        determinant = result['case']['determinant']
        result['status'] = ('PASS: actual normalized residue series, independent unit control, leading rank and determinant leading term certified.'
                            if determinant['complete'] and determinant['determinant_coefficient_within_requested_order'] else
                            'INCOMPLETE within determinant order 16; fixed prescribed calculation saved without further precision or fixtures.')
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete prescribed calculation; no replacement fixture or higher precision used.',
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
    determinant = result['case']['determinant']
    print(json.dumps(dict(leading_rank=result['case']['leading_matrix_certificate']['rank_certificate']['rank'],
                          determinant_complete=determinant['complete'],
                          determinant_order=determinant.get('determinant_order'),
                          determinant_leading_coefficient_mod_prime=determinant.get('determinant_leading_coefficient_mod_prime'),
                          pivot_valuation_multiplicities=determinant.get('pivot_valuation_multiplicities'))), flush=True)


if __name__ == '__main__':
    main()
