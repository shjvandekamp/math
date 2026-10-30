#!/usr/bin/env python3
"""One targeted m=6 actual paired small-time fixture, not a parameter sweep.

Fix p=1000003, a=(5/4,3/2,7/4,15/8,31/16,63/32),
b=(1,2,3,4,5,6), h=epsilon, delta=epsilon^2, and absolute entry precision
73 (known coefficients 0,...,72). No precision increase or other fixture
is permitted. The known determinant valuation lower bound is 68. The
proposed multiplicities {0:23,2:3,4:3,6:3,8:4} are compared only afterward.

Use process-local configuration of the reviewed four-block helper module
for the actual ordered H/J residue construction, Taylor arithmetic, and
minimum-valuation unit Schur elimination. No old script or certificate is
edited, and neither of its fixture-specific calculate/main functions runs.
The direct rational epsilon=2 control compares all 1296 entries with the
existing actual paired evaluator and its polynomial-clearing calculation.
Every matrix series and unit inverse is retained with source hashes.

Only one Python process is used. Its calculation guard reserves two of
the 28 seconds for saving an incomplete certificate if needed.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import time
import traceback

import source24_small_time_four_blocks as helpers


P = 1000003
PRECISION = 73
A_RATIONAL = ['5/4', '3/2', '7/4', '15/8', '31/16', '63/32']
A = [numerator * pow(denominator, -1, P) % P for numerator, denominator in
     [(5, 4), (3, 2), (7, 4), (15, 8), (31, 16), (63, 32)]]
B = [1, 2, 3, 4, 5, 6]
BLOCKS = 6
SIZE = 6 * BLOCKS
LABELS = [[kind, t + 1, c] for kind in ('H', 'J')
          for t in range(BLOCKS) for c in range(3)]
LOWER_BOUND = 68
LEADING_RANK_BOUND = 23
PROPOSED_PATTERN = {'0': 23, '2': 3, '4': 3, '6': 3, '8': 4}
CONFIGURATION = dict(PRECISION=PRECISION, A=A, B=B, BLOCKS=BLOCKS,
                     SIZE=SIZE, LABELS=LABELS)
ORIGINAL_CONFIGURATION = {name: getattr(helpers, name) for name in CONFIGURATION}
assert helpers.P == helpers.arithmetic.P == P
for name, value in CONFIGURATION.items():
    setattr(helpers, name, value)


def determinant_certificate(matrix):
    """Reuse the dimension-aware algorithm and replace fixture-specific prose."""
    result = helpers.determinant_certificate(matrix)
    if result['complete']:
        result['precision_argument'] = (
            'At a minimum-valuation pivot v the whole residual block is divisible '
            'by epsilon^v. Its unit Schur update is computed at precision 73-v, '
            'then multiplied by epsilon^v. Absolute entry precision remains 73.')
        result['coefficient_argument'] = (
            'All thirty-six pivots have valuation below 73, so their valuations '
            'and leading coefficients are exact. Multiply these leading terms '
            'and both permutation signs. This certifies the leading determinant '
            'term even if its exponent exceeds the entry coefficient range.')
    else:
        result['reason'] = (
            'Residual block is zero modulo epsilon^73; no higher precision '
            'or replacement fixture was attempted.')
    for pivot in result['pivots']:
        assert pivot['absolute_entry_precision'] == PRECISION
        assert pivot['unit_inverse_precision'] == PRECISION - pivot['valuation']
    return result


def calculate(record):
    record['stage'] = 'independent rational control at epsilon=2'
    record['scalar_control'] = helpers.scalar_control()
    assert record['scalar_control']['comparisons'] == SIZE * SIZE
    assert record['scalar_control']['all_matched']
    record['stage'] = 'actual matrix Taylor construction at fixed precision 73'
    field = helpers.Taylor()
    matrix, nodes = helpers.normalized_residues(field, field.epsilon())
    assert len(matrix) == SIZE and all(len(row) == SIZE for row in matrix)
    assert all(len(entry) == PRECISION for row in matrix for entry in row)
    leading_nodes = [node['leading_r'] for node in nodes]
    assert len(set(leading_nodes)) == 3 * BLOCKS and all(leading_nodes)
    record.update(
        moving_nodes=nodes, leading_nodes_distinct=True, leading_node_count=3 * BLOCKS,
        matrix_series=matrix, matrix_series_sha256=helpers.digest(matrix),
        matrix_series_layout='[observation row][actual column][epsilon exponent 0,...,72]',
        coefficient_matrix_sha256=[
            helpers.residue.matrix_hash([[entry[k] for entry in row] for row in matrix])
            for k in range(PRECISION)],
        series_arithmetic_operations=field.operations,
        series_unit_inverses=field.unit_inverses)
    record['stage'] = 'leading matrix rank and complete-pivot unit Schur elimination'
    record['leading_matrix_certificate'] = helpers.paired.certificate(
        [[entry[0] for entry in row] for row in matrix])
    record['determinant'] = determinant_certificate(matrix)
    determinant = record['determinant']
    leading_rank = record['leading_matrix_certificate']['rank_certificate']['rank']
    assert leading_rank <= LEADING_RANK_BOUND, 'The prescribed leading-rank bound failed.'
    assert leading_rank == sum(p['valuation'] == 0 for p in determinant['pivots'])
    if determinant['complete']:
        assert determinant['determinant_order'] >= LOWER_BOUND, 'The prescribed valuation lower bound failed.'
    else:
        assert determinant['determinant_order_lower_bound'] >= LOWER_BOUND
    record['paper_bounds_verified_at_fixture'] = dict(
        leading_rank_at_most=LEADING_RANK_BOUND, determinant_order_at_least=LOWER_BOUND)
    record['comparison_to_conjecture_only'] = dict(
        proposed_pivot_valuation_multiplicities=PROPOSED_PATTERN,
        matches=(determinant.get('pivot_valuation_multiplicities') == PROPOSED_PATTERN),
        scope='Comparison at one prescribed finite fixture; no uniform assertion.')
    record['stage'] = 'complete at the prescribed entry precision'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    phase = 'calculation'

    def guard(_signal, _frame):
        seconds_limit = 26 if phase == 'calculation' else 28
        if time.monotonic() - started >= seconds_limit:
            raise TimeoutError('Calculation stopped within the 28-second process budget; no retry.')
        if helpers.paired.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise MemoryError('95 MiB resource guard; no retry.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    source = Path(__file__)
    result = dict(
        scope='One targeted m=6 small-time fixture; no sweep, changed precision, or all-length claim.',
        prime=P, old_blocks=BLOCKS, matrix_shape=[SIZE, SIZE],
        common_matrix=helpers.G, sector_normal=[2, 1, 1],
        a_rational=A_RATIONAL, a_mod_prime=A, b=B, h='epsilon', delta='epsilon^2',
        time_factors='(1,a_t*epsilon,b_t*epsilon^3)',
        moving_chart='X=(1,-r/epsilon,r/epsilon-2)', column_labels=LABELS,
        column_normalization=dict(
            H=[0, 1, 1], J=[1, 2, 2],
            convention='Powers of epsilon multiplying actual columns.'),
        row_labels=[[t+1, c, j] for t in range(BLOCKS) for c in range(3) for j in (1, 2)],
        row_convention='Ordinary-r residues of output 1 and output 2/epsilon^2, interleaved at eighteen moving poles.',
        coefficient_orders=list(range(PRECISION)), absolute_precision=PRECISION,
        prescribed_bounds=dict(
            leading_rank_at_most=LEADING_RANK_BOUND, determinant_order_at_least=LOWER_BOUND),
        process_local_helper_configuration=dict(
            module='source24_small_time_four_blocks', original=ORIGINAL_CONFIGURATION,
            applied=CONFIGURATION,
            called_functions=['scalar_control', 'Taylor', 'normalized_residues',
                              'determinant_certificate'],
            old_fixture_calculate_and_main_not_called=True,
            inherited_determinant_explanation_replaced_with_actual_precision=True),
        resource_limits=dict(
            process_seconds=28, calculation_seconds=26,
            save_reserve_seconds=2, maximum_rss_bytes=95 * 1024 ** 2),
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        dependency_sha256={
            name: hashlib.sha256(source.with_name(name).read_bytes()).hexdigest()
            for name in ('source24_small_time_four_blocks.py',
                         'source24_small_time_series.py', 'source24_residue.py',
                         'source24_equal_weight_boundary.py', 'general_source24.py')},
        errors=[], case={})
    failure = None
    try:
        calculate(result['case'])
        result['status'] = (
            'PASS: actual normalized residue series, independent rational control, leading rank and determinant leading term certified.'
            if result['case']['determinant']['complete'] else
            'INCOMPLETE at entry precision 73; prescribed calculation saved without further precision or fixtures.')
    except Exception as error:
        failure = error
        result.update(
            status='FAILED or incomplete prescribed calculation; no replacement fixture or higher precision.',
            error=str(error), traceback=traceback.format_exc())
        result['errors'].append(dict(type=type(error).__name__, message=str(error)))
    phase = 'serialization'
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = helpers.paired.maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; total wall-time guard remains active during saving.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in
                      ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)
    determinant = result['case']['determinant']
    print(json.dumps(dict(
        leading_rank=result['case']['leading_matrix_certificate']['rank_certificate']['rank'],
        determinant_complete=determinant['complete'],
        determinant_order=determinant.get('determinant_order'),
        determinant_leading_coefficient_mod_prime=determinant.get('determinant_leading_coefficient_mod_prime'),
        pivot_valuation_multiplicities=determinant.get('pivot_valuation_multiplicities'),
        matches_conjectured_pattern=result['case']['comparison_to_conjecture_only']['matches'])),
        flush=True)


if __name__ == '__main__':
    main()
