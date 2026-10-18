#!/usr/bin/env python3
"""Independently check Pro40's two new finite weighted source bases.

Only q=5,6, r=(2,3,5), and the published fixed positive time list are
used. Reuse the independently polynomial-cleared controls of the existing
base checker. Also assemble the unnormalized table matrix directly and
compare its first-two-component determinant with the external claim.
No downloaded code, parameter search, or all-length conclusion is used.
"""

import argparse
import json
from pathlib import Path
import signal
import time
import traceback

import source24_weighted_source_base as base


TIMES = ((2, 3), (5, 7), (11, 13), (17, 29), (31, 47), (53, 73))
EXPECTED_RAW_DETERMINANTS = {5: 226299, 6: 160943}
PROPOSAL = 'https://chatgpt.com/c/6ad1abf4-9d9c-83eb-a330-66a5d8ae19f5'


def check_raw_convention(case):
    q, p = case['q'], base.P
    common = case['fixture']['unnormalized_common_matrix']
    tables = base.sparse.coefficient_tables(common, TIMES[:q])
    tables = [[[x % p for x in row] for row in table] for table in tables]
    padded = [[row[:] for row in common] for _ in range(2)] + tables
    pair_matrix, pair_geometry = base.residue.residue_matrix(q + 2, padded, p)
    raw_matrix, checks = [], 0
    records = case['polynomial_clearing_control']['cross_pair_records']
    for node, record in enumerate(records):
        (u, c), (v, d) = record['lines']
        X = base.residue.cross(tables[u][c], tables[v][d], p)
        U = [tables[u][c][j] * X[j] % p for j in range(3)]
        V = [tables[v][d][j] * X[j] % p for j in range(3)]
        cu, cv = common[c][0], common[d][0]
        scale = cu * cv % p
        assert X == [scale * x % p for x in record['point']]
        for offset, divisor in ((0, cu), (1, cv)):
            expected = [pow(scale, 3, p) * pow(divisor, -1, p) * x % p
                        for x in case['matrix'][2 * node + offset]]
            assert pair_matrix[2 * node + offset] == expected
            checks += len(expected)
        for j in (0, 1):
            raw_matrix.append([(alpha * U[j] + beta * V[j]) % p
                               for alpha, beta in zip(pair_matrix[2 * node],
                                                       pair_matrix[2 * node + 1])])
    certificate = base.residue.modular_rank(raw_matrix, p)
    assert certificate['determinant_mod_prime'] == EXPECTED_RAW_DETERMINANTS[q]
    return dict(convention='Unnormalized G; canonical cross product; actual vector residue components 0,1.',
                source=PROPOSAL, claimed_determinant_mod_prime=EXPECTED_RAW_DETERMINANTS[q],
                rank_certificate=certificate, matrix_sha256=base.residue.matrix_hash(raw_matrix),
                row_normalization_coefficient_checks=checks, pair_geometry=pair_geometry,
                all_external_determinant_claims_reproduced=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or base.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='Only q=5,6 at the fixed Pro40 time list and r=(2,3,5); no search.',
                  interpretation='Finite actual-source residue bases; no arbitrary-length independence theorem.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for q in (5, 6):
            case = base.calculate(q, TIMES[:q])
            assert case['full_column_rank']
            case['independent_raw_convention_control'] = check_raw_convention(case)
            result['cases'].append(case)
        result['status'] = 'PASS: both full residue bases and external raw determinants independently reproduced.'
    except Exception as error:
        failure = error
        result['status'] = 'FAILED or incomplete prescribed-fixture check; no replacement fixture used.'
        result['error'] = str(error)
        result['traceback'] = traceback.format_exc()
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = base.maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active during writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
