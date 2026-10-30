#!/usr/bin/env python3
"""One exact actual-source triple-collision jet certificate, using only stdlib.

This ports the prescribed Pro60 fixture without importing or executing its
SymPy script. All source values and first jets are over Q; four determinant
certificates use the one fixed prime 1000003. No sweep or all-length claim.
"""

import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback


PRIME = 1000003
WEIGHTS = {0: (F(1), F(4, 11), F(2)),
           1: (F(1), F(2), F(3)), 2: (F(1), F(5), F(7))}
SELECTED = {0: 0, 1: 0, 2: 1}
REFERENCE_SHA256 = '474465d5259a51135165d20c72448460b9676385963320d957fdd7c647cc6db1'
REFERENCE_CHAT_URL = 'https://chatgpt.com/c/6ad1f8af-06d4-83ed-8c87-66df96686a1f'
DENOMINATORS = set()


def qstr(value):
    value = F(value)
    DENOMINATORS.add(value.denominator)
    return str(value)


def json_q(value):
    if isinstance(value, (list, tuple)):
        return [json_q(item) for item in value]
    return qstr(value)


def zeros():
    return [[F(0) for _ in range(3)] for _ in range(3)]


def identity():
    return [[F(i == j) for j in range(3)] for i in range(3)]


def dot(left, right):
    return sum((x * y for x, y in zip(left, right)), F(0))


def matmul(left, right):
    return [[dot(row, column) for column in zip(*right)] for row in left]


def add(left, right):
    return [[x + y for x, y in zip(lrow, rrow)] for lrow, rrow in zip(left, right)]


def apply(matrix, vector):
    return [dot(row, vector) for row in matrix]


def right_diag(matrix, vector):
    return [[x * y for x, y in zip(row, vector)] for row in matrix]


def cross(x, y):
    return [x[1] * y[2] - x[2] * y[1],
            x[2] * y[0] - x[0] * y[2],
            x[0] * y[1] - x[1] * y[0]]


def require(record, name, condition):
    record['checks'].append(dict(name=name, passed=bool(condition)))
    if not condition:
        raise AssertionError(name)


def unit(record, name, value):
    value = F(value)
    record['nonzero_rational_divisors'].append(dict(name=name, value=qstr(value)))
    if not value:
        raise ZeroDivisionError(name)
    return value


def jet_product(left, right):
    return (left[0] * right[0],
            left[1] * right[0] + left[0] * right[1],
            left[2] * right[0] + left[0] * right[2])


def rational_mod(value):
    value = F(value)
    DENOMINATORS.add(value.denominator)
    denominator = value.denominator % PRIME
    if not denominator:
        raise ArithmeticError('Fixed prime divides a rational denominator.')
    return value.numerator % PRIME * pow(denominator, -1, PRIME) % PRIME


def determinant_certificate(matrix):
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    original = [[rational_mod(x) for x in row] for row in matrix]
    work = [row[:] for row in original]
    operations, pivots, determinant = [], [], 1
    for j in range(n):
        chosen = next((i for i in range(j, n) if work[i][j]), None)
        if chosen is None:
            raise ArithmeticError('Prescribed matrix is singular modulo the fixed prime.')
        if chosen != j:
            work[j], work[chosen] = work[chosen], work[j]
            operations.append(dict(kind='swap', row=j, other=chosen))
            determinant = -determinant
        pivot = work[j][j]
        pivots.append(dict(column=j, chosen_row=chosen, value=pivot))
        determinant = determinant * pivot % PRIME
        for i in range(j + 1, n):
            factor = -work[i][j] * pow(pivot, -1, PRIME) % PRIME
            if factor:
                operations.append(dict(kind='add', row=i, other=j, factor=factor))
                work[i] = [(x + factor * y) % PRIME for x, y in zip(work[i], work[j])]
    replay = [row[:] for row in original]
    for step in operations:
        i, j = step['row'], step['other']
        if step['kind'] == 'swap':
            replay[i], replay[j] = replay[j], replay[i]
        else:
            replay[i] = [(x + step['factor'] * y) % PRIME
                         for x, y in zip(replay[i], replay[j])]
    assert replay == work and all(work[i][j] == 0 for i in range(n) for j in range(i))
    return dict(size=n, determinant=determinant % PRIME, matrix_mod_prime=original,
                pivots=pivots, row_operations=operations, upper_triangular=work,
                exact_modular_operation_replay_passed=True)


def calculate(record):
    require(record, 'fixed_prime_is_prime_by_trial_division',
            PRIME > 1 and all(PRIME % d for d in range(2, 1001)))
    matrices = {t: [[F(1 + (i == j)) * weights[j] for j in range(3)]
                    for i in range(3)] for t, weights in WEIGHTS.items()}
    point = cross(matrices[1][0], matrices[2][1])
    scale = unit(record, 'triple_projective_coordinate_zero', point[0])
    point = [x / scale for x in point]
    aa, ab = matrices[1][0][1:]
    ba, bb = matrices[2][1][1:]
    determinant = unit(record, 'selected_line_coordinate_jacobian', aa * bb - ab * ba)
    directions = [[F(0), bb / determinant, -ba / determinant],
                  [F(0), -ab / determinant, aa / determinant]]
    alpha = unit(record, 'alpha', dot(matrices[0][0], directions[0]))
    beta = unit(record, 'beta', dot(matrices[0][0], directions[1]))
    line_values = {t: apply(matrix, point) for t, matrix in matrices.items()}
    line_jets = {t: (line_values[t][SELECTED[t]],
                    dot(matrix[SELECTED[t]], directions[0]),
                    dot(matrix[SELECTED[t]], directions[1])) for t, matrix in matrices.items()}
    require(record, 'all_three_selected_lines_vanish', all(jet[0] == 0 for jet in line_jets.values()))
    require(record, 'x_y_are_selected_line_coordinates',
            line_jets[1] == (0, 1, 0) and line_jets[2] == (0, 0, 1))
    require(record, 'third_selected_line_equals_alpha_x_plus_beta_y', line_jets[0] == (0, alpha, beta))
    scaled, derivatives = {}, {}
    for t, matrix in matrices.items():
        selected = SELECTED[t]
        values = right_diag(matrix, point)
        scaled[t] = zeros()
        scaled[t][selected] = values[selected][:]
        derivatives[t] = []
        for c in range(3):
            if c != selected:
                unit(record, f'triple_nonselected_line_{t}_{c}', line_values[t][c])
        for direction in directions:
            derivative = zeros()
            derivative[selected] = right_diag(matrix, direction)[selected]
            numerator = dot(matrix[selected], direction)
            for c in range(3):
                if c != selected:
                    derivative[c] = [numerator / line_values[t][c] * x for x in values[c]]
            derivatives[t].append(derivative)

    new = [(0, s, a, b) for s in (1, 2) for a, b in product(range(3), repeat=2)]
    boundary = [(t, 0, a, b) for t in (1, 2) for a, b in product(range(3), repeat=2)]
    old = [(t, s, a, b) for t, s in ((1, 2), (2, 1)) for a, b in product(range(3), repeat=2)]
    columns = new + boundary + old
    old_pairs = [(1, 2, a, b) for a, b in product(range(3), repeat=2)]
    new_pairs = [(0, t, a, b) for t in (1, 2) for a, b in product(range(3), repeat=2)]
    pairs = old_pairs + new_pairs
    triple = []
    for t, s, a, b in columns:
        other = next(k for k in (0, 1, 2) if k not in (t, s))
        tail = matmul(scaled[s], scaled[other])[b]
        value = [-point[a] * scaled[t][a][b] * x for x in tail]
        ds = []
        for d in range(2):
            tail_d = add(matmul(derivatives[s][d], scaled[other]),
                         matmul(scaled[s], derivatives[other][d]))[b]
            ds.append([-directions[d][a] * scaled[t][a][b] * x
                       -point[a] * derivatives[t][d][a][b] * x
                       -point[a] * scaled[t][a][b] * dx for x, dx in zip(tail, tail_d)])
        head = jet_product((point[a], directions[0][a], directions[1][a]),
                           (scaled[t][a][b], derivatives[t][0][a][b], derivatives[t][1][a][b]))
        for k in sorted(matrices):
            if k != t:
                head = jet_product(head, line_jets[k])
        require(record, f'actual_head_value_and_both_jets_zero_{t}_{s}_{a}_{b}', head == (0, 0, 0))
        require(record, f'triple_full_source_jets_zero_sum_{t}_{s}_{a}_{b}',
                sum(value) == 0 and all(sum(row) == 0 for row in ds))
        triple.append((value, ds))

    pair_records = []
    def raw_pair(pair, column_list, times):
        t, s, a, b = pair
        pt = cross(times[t][a], times[s][b])
        normalization = unit(record, f'pair_projective_coordinate_{tuple(times)}_{pair}', pt[0])
        pt = [x / normalization for x in pt]
        selected_values = (dot(times[t][a], pt), dot(times[s][b], pt))
        require(record, f'pair_selected_lines_zero_{tuple(times)}_{pair}', selected_values == (0, 0))
        mats = {}
        for k, matrix in times.items():
            values = right_diag(matrix, pt)
            if k in (t, s):
                mats[k] = zeros()
                index = a if k == t else b
                mats[k][index] = values[index][:]
                for c, line in enumerate(apply(matrix, pt)):
                    if c != index:
                        unit(record, f'pair_same_block_nonselected_{tuple(times)}_{pair}_{k}_{c}', line)
            else:
                lines = apply(matrix, pt)
                for c, line in enumerate(lines):
                    unit(record, f'pair_remaining_line_{pair}_{k}_{c}', line)
                mats[k] = [[x / lines[i] for x in row] for i, row in enumerate(values)]
        result, all_heads_zero = [], True
        for ht, fs, ha, hb in column_list:
            tail = identity()
            for k in sorted(times):
                if k not in (ht, fs):
                    tail = matmul(tail, mats[k])
            completed = matmul(mats[fs], tail)[hb]
            row = [-pt[ha] * mats[ht][ha][hb] * x for x in completed]
            head_scalar = pt[ha] * mats[ht][ha][hb]
            if ht == t:
                head_scalar *= selected_values[1]
            elif ht == s:
                head_scalar *= selected_values[0]
            else:
                head_scalar *= selected_values[0] * selected_values[1]
            all_heads_zero &= head_scalar == 0
            assert sum(row) == 0
            result.append(row)
        require(record, f'pair_full_source_heads_zero_{tuple(times)}_{pair}', all_heads_zero)
        pair_records.append(dict(times=list(times), pair=list(pair), point=json_q(pt),
                                 exact_rows_zero_sum=True, actual_head_values_zero=True))
        return [[row[c] for row in result] for c in (1, 2)]

    rows, row_kinds = [], []
    for pair in pairs:
        if pair == (1, 2, 0, 1):
            rows.extend([[jet[1][1][c] / beta for jet in triple] for c in (1, 2)])
            kind = 'triple_dy_div_beta'
        elif pair == (0, 1, 0, 0):
            rows.extend([[jet[0][c] for jet in triple] for c in (1, 2)])
            kind = 'triple_value'
        elif pair == (0, 2, 0, 1):
            rows.extend([[alpha * jet[1][1][c] - beta * jet[1][0][c]
                          for jet in triple] for c in (1, 2)])
            kind = 'triple_alpha_dy_minus_beta_dx'
        else:
            rows.extend(raw_pair(pair, columns, matrices))
            kind = 'ordinary_pair_cleared_value'
        row_kinds.extend([dict(pair=list(pair), coordinate=c, kind=kind) for c in (1, 2)])
    old_matrix = []
    for pair in old_pairs:
        old_matrix.extend(raw_pair(pair, old, {1: matrices[1], 2: matrices[2]}))
    u = [row[:36] for row in rows[18:]]
    v = [row[:36] for row in rows[:18]]
    w = [row[36:] for row in rows[18:]]
    a_matrix = [row[36:] for row in rows[:18]]
    require(record, 'old_D2_first_off_diagonal_block_zero',
            all(old_matrix[i][j] == 0 for i in range(2) for j in (1, 12)))
    require(record, 'old_D2_second_off_diagonal_block_zero',
            all(old_matrix[i][j] == 0 for i in range(2, 4) for j in (0, 9)))
    require(record, 'uneliminated_A_0_1_zero', a_matrix[0][1] == 0)
    cert_u = determinant_certificate(u)
    cert_old = determinant_certificate(old_matrix)
    require(record, 'boundary_U_determinant_matches', cert_u['determinant'] == 313525)
    require(record, 'old_D2_determinant_matches', cert_old['determinant'] == 998770)
    schur = []
    for (i, j), expected in {(0, 1): (174190, 559830), (2, 0): (967603, 284986)}.items():
        bordered = [row + [w[k][j]] for k, row in enumerate(u)] + [v[i] + [a_matrix[i][j]]]
        cert = determinant_certificate(bordered)
        entry = cert['determinant'] * pow(cert_u['determinant'], -1, PRIME) % PRIME
        require(record, f'border_and_Schur_entry_{i}_{j}_match', (cert['determinant'], entry) == expected)
        require(record, f'Schur_entry_{i}_{j}_nonzero', entry != 0)
        schur.append(dict(row=i, column=j, border_certificate=cert, entry_mod_prime=entry,
                          old_D2_entry=qstr(old_matrix[i][j]), raw_A_entry=qstr(a_matrix[i][j])))
    record.update(parameters=dict(weights={str(t): json_q(x) for t, x in WEIGHTS.items()},
                                  selected_rows=SELECTED, prime=PRIME),
        actual_matrices={str(t): json_q(matrix) for t, matrix in matrices.items()},
        triple_point=json_q(point), coordinate_directions=json_q(directions),
        alpha=qstr(alpha), beta=qstr(beta),
        triple_line_values={str(t): json_q(x) for t, x in line_values.items()},
        scaled_kernel_values={str(t): json_q(x) for t, x in scaled.items()},
        scaled_kernel_derivatives={str(t): json_q(x) for t, x in derivatives.items()},
        source_order=[list(x) for x in columns], pair_order=[list(x) for x in pairs],
        triple_full_source_values_and_derivatives=json_q(triple),
        pair_evaluations=pair_records, row_definitions=row_kinds,
        full_54_by_54_jet_matrix=json_q(rows), old_18_by_18_pair_matrix=json_q(old_matrix),
        block_partition=dict(U='D[18:54,0:36]', V='D[0:18,0:36]',
                             W='D[18:54,36:54]', A='D[0:18,36:54]', H='A-V U^-1 W'),
        boundary_U_certificate=cert_u, old_D2_certificate=cert_old, Schur_entries=schur,
        all_prescribed_checks_passed=True)


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started, phase = time.monotonic(), 'calculation'
    def guard(_signum, _frame):
        if time.monotonic() - started >= (26 if phase == 'calculation' else 28):
            raise TimeoutError('Single-run time budget exhausted; no automatic retry.')
        if maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise MemoryError('Prescribed 95 MiB RSS budget exhausted; no automatic retry.')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    root = Path(__file__).resolve().parents[1]
    source_reference = root / 'research/SOURCE24_COMPLETION_QUOTIENT.md'
    record = dict(scope='One rational three-block collision fixture. A counterexample to pairwise triangular transport, not an all-length theorem, not full Eq. (24), and not a Lean proof.',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        reviewed_Pro60_source=dict(name='verify_source_collision.py', chat_url=REFERENCE_CHAT_URL,
                                  sha256=REFERENCE_SHA256, required_at_runtime=False, executed=False),
        actual_source_reference=dict(path=str(source_reference.relative_to(root)), sha256=hashlib.sha256(source_reference.read_bytes()).hexdigest()),
        actual_source_formula='X_a K_t[a,b] (e_b - e_b K_s product_{k not in {t,s}, ascending} K_k); K_t=diag(A_t X)^-1 A_t diag(X), A_t=(I+11^T)diag(weights_t).',
        jet_method='M_t=l_t K_t, where l_t is the selected row line. M_t and both coordinate derivatives are reconstructed by exact quotient differentiation; source jets use the product rule. The actual one-pole head is explicitly checked to vanish after pair clearing, and through first order after triple clearing.',
        arithmetic='Python Fraction for every source value and derivative; exact fixed-prime Gaussian elimination with row-operation replay and denominator-unit checks for determinant nonvanishing.',
        scalar_field='Q, followed only for determinant certificates by F_1000003',
        software_dependencies='Python standard library only', python_version=sys.version,
        resource_limits=dict(process_seconds=28, calculation_seconds=26, maximum_rss_bytes=95 * 1024 ** 2),
        checks=[], nonzero_rational_divisors=[], errors=[])
    failure = None
    try:
        calculate(record)
        record['status'] = 'PASS: actual-source jets and two nonzero off-diagonal Schur entries.'
    except Exception as error:
        failure = error
        record.update(status='FAILED or incomplete single prescribed calculation; no automatic retry.',
                      error=str(error), traceback=traceback.format_exc())
        record['errors'].append(dict(type=type(error).__name__, message=str(error)))
    phase = 'serialization'
    denominator_units = [dict(denominator=str(d), residue=d % PRIME, inverse=pow(d % PRIME, -1, PRIME))
                         for d in sorted(DENOMINATORS)]
    record.update(exact_check_count=len(record['checks']), rational_denominator_units=denominator_units,
        elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=maximum_rss_bytes(),
        resource_measurement_scope='Before serialization; the resource guard remains active during saving.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(dict(status=record['status'], checks=record['exact_check_count'],
        elapsed_seconds=record['elapsed_seconds'], maximum_rss_bytes=record['maximum_rss_bytes'],
        determinant_U=record.get('boundary_U_certificate', {}).get('determinant'),
        determinant_old=record.get('old_D2_certificate', {}).get('determinant'),
        Schur_entries=[x['entry_mod_prime'] for x in record.get('Schur_entries', [])])), flush=True)
    if failure is not None:
        print(record['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
