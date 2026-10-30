#!/usr/bin/env python3
"""One exact actual two-block boundary certificate for the confluent quotient.

The sole prescribed fixture is z=-2/3, a=(1,3/2), b=(1,1). Reconstruct
the completed binary words and their first weak coefficients, check the
three supplied kernel combinations, and verify the NH71/NH72 quotient
targets and the displayed six-by-six determinant over Q. No sweeps,
numerical approximations, Lean claims, or all-length conclusions.

Only arithmetic primitives are imported from the existing invariant-tail
certificate. Its source, parameters, and main calculation are unchanged.
One guarded execution: 26 calculation seconds, 28 total seconds, 95 MiB RSS.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

import source24_invariant_tail_base as arithmetic
from source24_invariant_tail_base import (
    R, Rat, d_function, kernel, matmul, padd, pmul, pscale, rowmul,
)


Z = F(-2, 3)
AS = (F(1), F(3, 2))
BS = (F(1), F(1))
GAMMA = (
    (-14, -114, -33, 36, 27, -27, 36, 81, 0, 0, 0, 0),
    (-20, -24, -24, 0, 0, 0, 36, 0, 0, 27, 0, 0),
    (20, 24, 24, -36, -27, 27, -36, 0, 0, 0, 81, 0),
)
HEAD_SCALES = (-33, -24, 24)
EXPECTED_MATRIX = [
    [-144, -54, 144, 4, 20, -4],
    [1108, 244, -472, -53, -139, 21],
    [-2159, -143, 446, 146, 298, -16],
    [-699, -375, 798, -127, -221, -35],
    [1980, 198, -711, 30, 42, 6],
    [-486, 0, 0, 0, 0, 0],
]
EXPECTED_DETERMINANT = -2 ** 6 * 3 ** 12 * 20161
DENOMINATORS = set()


def qstr(value):
    value = F(value)
    DENOMINATORS.add(value.denominator)
    return str(value)


def poly_json(poly):
    return [qstr(value) for value in poly]


def matrix_json(matrix):
    return [poly_json(row) for row in matrix]


def rat_json(value):
    value = Rat.of(value)
    return dict(numerator_coefficients_ascending=poly_json(value.n),
                monic_linear_denominator=[
                    dict(root=qstr(root), exponent=value.d[root])
                    for root in sorted(value.d)])


def verify(record, name, left, right=0):
    left, right = Rat.of(left), Rat.of(right)
    difference = padd(pmul(left.n, right.denominator_poly()),
                      pscale(pmul(right.n, left.denominator_poly()), -1))
    record['identities'].append(dict(
        name=name, cross_multiplied_difference=poly_json(difference), passed=not difference))
    assert not difference, 'Exact Q(r) identity failed: ' + name


def linear_combination(coefficients, functions):
    return sum((F(c) * f for c, f in zip(coefficients, functions)), Rat.of(0))


def rref_certificate(matrix):
    original = [[F(value) for value in row] for row in matrix]
    work = [row[:] for row in original]
    pivots, operations, pivot_row = [], [], 0
    for col in range(len(work[0])):
        chosen = next((i for i in range(pivot_row, len(work)) if work[i][col]), None)
        if chosen is None:
            continue
        if chosen != pivot_row:
            work[pivot_row], work[chosen] = work[chosen], work[pivot_row]
            operations.append(dict(kind='swap', row=pivot_row, other=chosen))
        pivot = work[pivot_row][col]
        pivots.append(dict(row=pivot_row, column=col, value=qstr(pivot)))
        work[pivot_row] = [value / pivot for value in work[pivot_row]]
        operations.append(dict(kind='scale', row=pivot_row, factor=qstr(1 / pivot)))
        for i in range(len(work)):
            if i == pivot_row or not work[i][col]:
                continue
            factor = -work[i][col]
            work[i] = [x + factor * y for x, y in zip(work[i], work[pivot_row])]
            operations.append(dict(kind='add', row=i, other=pivot_row, factor=qstr(factor)))
        pivot_row += 1
        if pivot_row == len(work):
            break
    replay = [row[:] for row in original]
    for item in operations:
        i = item['row']
        if item['kind'] == 'swap':
            j = item['other']
            replay[i], replay[j] = replay[j], replay[i]
        elif item['kind'] == 'scale':
            replay[i] = [F(item['factor']) * x for x in replay[i]]
        else:
            replay[i] = [x + F(item['factor']) * y
                         for x, y in zip(replay[i], replay[item['other']])]
    assert replay == work
    pivot_columns = [item['column'] for item in pivots]
    free_columns = [j for j in range(len(work[0])) if j not in pivot_columns]
    basis = []
    for free in free_columns:
        vector = [F(0)] * len(work[0])
        vector[free] = F(1)
        for item in pivots:
            vector[item['column']] = -work[item['row']][free]
        assert all(sum(x * y for x, y in zip(row, vector)) == 0 for row in original)
        basis.append(vector)
    return dict(rank=len(pivots), pivot_records=pivots, operations=operations,
                reduced_matrix=matrix_json(work), nullspace_basis=matrix_json(basis),
                free_columns=free_columns, exact_operation_replay_passed=True), basis


def determinant_certificate(matrix):
    cert, basis = rref_certificate(matrix)
    assert not basis and cert['rank'] == len(matrix), 'Singular quotient coefficient matrix.'
    det = F(1)
    for pivot in cert['pivot_records']:
        det *= F(pivot['value'])
    for operation in cert['operations']:
        if operation['kind'] == 'swap':
            det = -det
    cert['determinant'] = qstr(det)
    assert [[F(x) for x in row] for row in cert['reduced_matrix']] == [
        [F(i == j) for j in range(len(matrix))] for i in range(len(matrix))]
    cert['reduced_matrix_is_identity'] = True
    return cert


def clear_column(record, name, function, denominator):
    cleared = function * denominator
    assert not cleared.d and len(cleared.n) <= 6
    verify(record, name + '_denominator_clearing', function * denominator, Rat(cleared.n))
    return list(cleared.n) + [F(0)] * (6 - len(cleared.n))


def calculate(record):
    kernels = [kernel(a) for a in AS]
    X, v = [Rat.of(1), -R, R - Z], [Rat.of(Z), -R, R - Z]
    binary, weak, heads, labels = [], [], [], []
    for s in range(2):
        other = 1 - s
        forms = [2 - AS[s] * R, 1 - 2 * AS[s] * R, 1 - AS[s] * R]
        other_forms = [2 - AS[other] * R, 1 - 2 * AS[other] * R, 1 - AS[other] * R]
        u_other = [1 / other_forms[0], 1 / other_forms[1], 2 / other_forms[2]]
        mus = [2 / forms[0], -R / forms[1], (R - Z) / forms[2]]
        product = matmul(kernels[s], kernels[other])
        for kind in ('H', 'J'):
            for c in range(3):
                labels.append(f'{kind}{s + 1}{c}')
                if kind == 'H':
                    binary.append([X[c] * entry for entry in product[c]])
                    weak.append(BS[other] * X[c] * sum(
                        (kernels[s][c][i] * u_other[i] for i in range(3)), Rat.of(0)))
                    heads.append([X[c] if i == c else Rat.of(0) for i in range(3)])
                else:
                    binary.append([mus[c] * entry for entry in rowmul(v, kernels[other])])
                    weak.append(BS[other] * mus[c] * sum(
                        (v[i] * u_other[i] for i in range(3)), Rat.of(0)))
                    heads.append([Rat.of(0)] * 3)
    row_sums = [sum(row, Rat.of(0)) for row in heads]
    for j, label in enumerate(labels):
        verify(record, label + '_binary_row_sum_equals_exact_head_sum',
               sum(binary[j], Rat.of(0)), row_sums[j])
    cs, combined_heads = [], []
    for j, gamma in enumerate(GAMMA):
        for output in range(3):
            verify(record, f'gamma{j + 1}_binary_output{output}',
                   linear_combination(gamma, [row[output] for row in binary]))
        verify(record, f'gamma{j + 1}_exact_row_sum', linear_combination(gamma, row_sums))
        head = [linear_combination(gamma, [row[output] for row in heads]) for output in range(3)]
        for output in range(3):
            verify(record, f'gamma{j + 1}_retained_head{output}', head[output], HEAD_SCALES[j] * v[output])
        combined_heads.append(head)
        cs.append(linear_combination(gamma, weak))
    nodes = [node for a in AS for node in (2 / a, 1 / (2 * a), 1 / a)]
    removed_node = 1 / AS[1]
    allowed_nodes = set(nodes) - {removed_node}
    assert len(set(nodes)) == 6 and Z not in nodes and Z != 0
    constraints = [[row_sums[j].n[i] if i < len(row_sums[j].n) else F(0)
                    for j in range(12)] for i in range(2)]
    constraints += [[binary[j][1].residue(node) for j in range(12)] for node in nodes]
    kernel_cert, kernel_basis = rref_certificate(constraints)
    assert kernel_cert['rank'] == 8 and len(kernel_basis) == 4
    kernel_weak, removed_residues = [], []
    for j, vector in enumerate(kernel_basis):
        for output in range(3):
            verify(record, f'full_kernel_basis{j}_actual_binary_output{output}',
                   linear_combination(vector, [row[output] for row in binary]))
        verify(record, f'full_kernel_basis{j}_exact_row_sum', linear_combination(vector, row_sums))
        function = linear_combination(vector, weak)
        kernel_weak.append(function)
        removed_residues.append(function.residue(removed_node))
    assert any(removed_residues), 'Removal of the second state-two pole must impose one condition.'
    for j, function in enumerate(cs):
        verify(record, f'c{j + 1}_removed_pole_residue', function.residue(removed_node))
        assert removed_node not in function.d
        assert set(function.d).issubset(allowed_nodes) and all(e == 1 for e in function.d.values())
        function.infinity()
    prefix = matmul(kernels[0], kernels[1])
    p = prefix[0][1]
    Dprod = d_function(AS[0]) * d_function(AS[1])
    P = Dprod / (1 - AS[0] * R)
    def J(function):
        return (function - function.at(Z)) / (R - Z)
    psi = ((1 - 2 * AS[0] * Z) * R + Z) / (1 - AS[0] * R)
    u, v_target = J(p / R), J(p)
    w = J(Dprod * (1 + Z / (2 * R)) * psi)
    verify(record, 'NH72_u_identity', u, (J(p) - p / R) / Z)
    verify(record, 'NH72_w_identity', w,
           (1 - 2 * AS[0] * Z) * P - Z * P / (2 * R) + 3 * Z * (1 - AS[0] * Z) * J(P))
    denominator = (R - 2) * (R - 1) * (2 * R - 1) * (3 * R - 4) * (3 * R - 1)
    functions = [cs[0], cs[1] / 4, cs[2], F(8, 3) * u, 4 * v_target, F(14, 9) * w]
    names = ['c1', 'c2/4', 'c3', '(8/3)u', '4v', '(14/9)w']
    columns = [clear_column(record, name, function, denominator)
               for name, function in zip(names, functions)]
    matrix = [list(row) for row in zip(*columns)]
    for j, name in enumerate(names):
        expected = [F(row[j]) for row in EXPECTED_MATRIX]
        verify(record, name + '_claimed_numerator', functions[j] * denominator, Rat(expected))
    assert matrix == [[F(x) for x in row] for row in EXPECTED_MATRIX]
    determinant = determinant_certificate(matrix)
    assert F(determinant['determinant']) == EXPECTED_DETERMINANT
    star = 2 * cs[1] + 3 * cs[2]
    claimed_star_numerator = -R * (549 * R * R * R + 606 * R * R - 194 * R - 536)
    verify(record, 'c_star_claimed_numerator', star * denominator, claimed_star_numerator)
    verify(record, 'c_star_at_zero', star.at(0))
    verify(record, 'c_star_at_infinity', star.infinity())
    verify(record, 'c_star_at_second_state_two_node', star.at(removed_node), -525)
    for j, function in enumerate([u, v_target, w]):
        assert set(function.d).issubset(allowed_nodes) and all(e == 1 for e in function.d.values())
        assert Z not in function.d and F(0) not in function.d
        verify(record, f'NH_target{j}_at_infinity', function.infinity())
    endpoint_matrix = [[c.at(0) for c in cs], [c.infinity() for c in cs]]
    endpoint_cert, endpoint_kernel = rref_certificate(endpoint_matrix)
    assert endpoint_cert['rank'] == 2 and len(endpoint_kernel) == 1
    assert all(sum(F(x) * y for x, y in zip(row, (0, 2, 3))) == 0 for row in endpoint_matrix)
    record.update(
        actual_binary_kernels=[[[rat_json(value) for value in row] for row in k] for k in kernels],
        actual_columns=dict(source_order=labels,
            completed_binary_rows=[[rat_json(value) for value in row] for row in binary],
            weak_functions=[rat_json(value) for value in weak],
            source_heads=[[rat_json(value) for value in row] for row in heads]),
        gamma=dict(coefficients_by_combination=matrix_json(GAMMA),
            retained_heads=[[rat_json(value) for value in row] for row in combined_heads],
            retained_head_scales=poly_json(HEAD_SCALES), actual_weak_functions=[rat_json(c) for c in cs]),
        actual_kernel=dict(constraint_row_order=['head_sum_r0', 'head_sum_r1'] +
                ['binary_output1_residue_at_' + qstr(node) for node in nodes],
            constraint_matrix=matrix_json(constraints), certificate=kernel_cert,
            full_kernel_weak_functions=[rat_json(c) for c in kernel_weak],
            removed_pole=qstr(removed_node), residue_functional_on_kernel_basis=poly_json(removed_residues),
            removed_pole_functional_rank=1, restricted_kernel_dimension=3,
            three_actual_weak_functions_independent=True,
            restricted_A2_basis_status='Exact at this fixture: binary kernel dimension four; removal of the second state-two pole has rank one; the displayed three weak images are independent.'),
        NH_targets=dict(p=rat_json(p), Dprod=rat_json(Dprod), P=rat_json(P), psi=rat_json(psi),
            u=rat_json(u), v=rat_json(v_target), w=rat_json(w),
            divided_difference_point=qstr(Z), definitions='NH71 directly; NH72 separately cross-multiplied.'),
        coefficient_certificate=dict(column_order=names, row_order=[f'r^{i}' for i in range(6)],
            common_denominator=rat_json(denominator), exact_matrix=matrix_json(matrix),
            claimed_matrix=EXPECTED_MATRIX, determinant=determinant,
            claimed_determinant=qstr(EXPECTED_DETERMINANT), claimed_factorization='-2^6 * 3^12 * 20161',
            implied_nonzero_quotient_determinant=True),
        endpoint_adjuster=dict(function=rat_json(star), coefficient_vector=['0', '2', '3'],
            endpoint_matrix=matrix_json(endpoint_matrix), endpoint_rank_certificate=endpoint_cert,
            R2_dimension=1, at_zero=qstr(star.at(0)), at_infinity=qstr(star.infinity()),
            at_second_state_two_node=qstr(star.at(removed_node))),
        parameter_guards=dict(all_six_nodes_distinct=True, nodes=poly_json(nodes),
            allowed_restricted_poles=poly_json(sorted(allowed_nodes)), z_avoids_all_poles=True,
            nonzero_scalar_divisors=poly_json([Z, *AS, F(4), F(3), F(9)]),
            common_D_at_z=qstr(denominator.at(Z)), common_D_at_zero=qstr(denominator.at(0)),
            common_D_at_second_state_two_node=qstr(denominator.at(removed_node)),
            note='The witness has z<0 and a1=1. It is an algebraic rational witness, not a positive-interior parameter assertion.'),
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
            raise TimeoutError('Prescribed single-run time budget exhausted; no automatic retry.')
        if maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise MemoryError('Prescribed 95 MiB RSS budget exhausted; no automatic retry.')
    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    root = Path(__file__).resolve().parents[1]
    dependencies = ['exploration/source24_invariant_tail_base.py',
                    'research/SOURCE24_INVARIANT_TAIL.md',
                    'research/SOURCE24_NONZERO_H_WEAK_TRANSFER.md']
    record = dict(
        scope='One exact two-block actual-source and quotient boundary certificate. External Q(r) verification; not Lean and not an all-length or full Eq. (24) theorem.',
        parameters=dict(z=qstr(Z), a=poly_json(AS), b=poly_json(BS)),
        scalar_field='Q(r) for functions and Q for all matrix computations; no modular determinant substitution.',
        source_conventions='G=I+11^T; X=(1,-r,r-z); v=(z,-r,r-z); completed H=X_c e_c K_s K_other; completed J=mu_sc v K_other. Actual source rows are head-H and -J; retained polynomial heads are recorded.',
        weak_conventions='IT13: c=[delta]C_2/(r-z); H weak=b_other X_c e_c K_s^0 u_other, J weak=b_other mu_sc v u_other, u=(1/l0,1/l1,2/l2).',
        source_order='H10,H11,H12,J10,J11,J12,H20,H21,H22,J20,J21,J22',
        derivation='Actual binary words and final-kernel weak derivatives are reconstructed. The full binary kernel is independently certified; no supplied weak function or determinant is treated as an input fact.',
        arithmetic='Imported Fraction polynomial/Rat primitives only. Every rational cancellation is multiplied back. Final identities use polynomial cross multiplication; Gaussian row operations are recorded and independently replayed.',
        resource_limits=dict(process_seconds=28, calculation_seconds=26, maximum_rss_bytes=95 * 1024 ** 2),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_dependencies={name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in dependencies},
        software_dependencies='Python standard library only', python_version=sys.version,
        identities=[], errors=[])
    failure = None
    try:
        calculate(record)
        record['status'] = 'PASS: actual binary kernel, restricted A2 basis, endpoint adjuster, and exact nonzero quotient determinant.'
    except Exception as error:
        failure = error
        record.update(status='FAILED or incomplete single prescribed calculation; no automatic retry.',
                      error=str(error), traceback=traceback.format_exc())
        record['errors'].append(dict(type=type(error).__name__, message=str(error)))
    phase = 'serialization'
    record.update(arithmetic_counts=arithmetic.COUNTS,
        exact_identity_count=len(record['identities']),
        positive_rational_coefficient_denominators=[str(d) for d in sorted(DENOMINATORS)],
        all_recorded_rational_coefficient_denominators_nonzero=all(d > 0 for d in DENOMINATORS),
        elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=maximum_rss_bytes(),
        resource_measurement_scope='Before serialization; the resource guard remains active during saving.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(dict(status=record['status'], identities=record['exact_identity_count'],
        elapsed_seconds=record['elapsed_seconds'], maximum_rss_bytes=record['maximum_rss_bytes'],
        determinant=record.get('coefficient_certificate', {}).get('determinant', {}).get('determinant'),
        endpoint_adjuster_value=record.get('endpoint_adjuster', {}).get('at_second_state_two_node'))), flush=True)
    if failure is not None:
        print(record['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
