#!/usr/bin/env python3
"""Actual equation-(24) source matrices with constant time coefficients.

External exact modular exploration only; not a Lean proof or an all-T
claim. The canonical section3.4 index restriction and footnote7 orders are
imported from general_source24.py. Numerators here are computed directly
from a supplied coefficient table, with no hardcoded covariate powers.

All displayed constant-time tables are economic specializations with
gamma[q,r]=log(G[q][r]), beta=(0,1,2), and x_t=0 for every t. The baseline
outcome row and baseline lag column of G are normalized to one.

Reproduce from the project directory:
  nice -n 19 python3 exploration/constant_time_source24.py --output exploration/constant-time-results.json
"""

import argparse
import importlib.util
import itertools as it
import json
from pathlib import Path


Q = 3
PRIME = 1000003
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('general_source24', ROOT / 'exploration/general_source24.py')
general = importlib.util.module_from_spec(spec)
spec.loader.exec_module(general)


def coefficient_table(T, G, time_factors=None):
    factors = [1] * T if time_factors is None else time_factors
    assert len(factors) == T
    assert all(factor > 0 for factor in factors)
    assert all(x > 0 for row in G for x in row)
    return [[[G[q][r] * factors[t] ** q for r in range(Q)] for q in range(Q)]
            for t in range(T)]


def source_row(table, paths, idx, initial=0):
    T = len(table)
    sigma1 = dict(zip([T - 1] + idx['tau1'][:-1], idx['tau1']))
    sigma2 = dict(zip([T - 1] + idx['tau2'][:-1], idx['tau2']))
    q = idx['values'][0]
    row = []
    for y in paths:
        if any(y[t] != a for t, a in zip(idx['shared'], idx['values'][1:])):
            row.append(0)
            continue
        first = second = 0
        if y[idx['s1']] == q:
            first = table[0][y[sigma1[T - 1]]][initial]
            for t in range(1, T):
                first *= table[t][y[sigma1[t - 1]]][y[t - 1]]
        if y[idx['s2']] == q:
            second = table[0][y[sigma2[T - 1]]][initial]
            for t in range(1, T):
                second *= table[t][y[sigma2[t - 1]]][y[t - 1]]
        row.append(first - second)
    return row


def verify_timevarying_t4():
    location = ROOT / 'exploration/exact_q3t4.py'
    old_spec = importlib.util.spec_from_file_location('old_exact_q3t4', location)
    old = importlib.util.module_from_spec(old_spec)
    old_spec.loader.exec_module(old)
    table = coefficient_table(4, old.G, [2 ** (3 * (t + 1)) for t in range(4)])
    assert table == old.PI
    indices = general.source_indices(4)
    assert indices == old.source_indices()
    for initial in range(Q):
        rows = [source_row(table, old.PATHS, idx, initial) for idx in indices]
        assert rows == old.moment_numerators(old.PI, initial)
    return dict(table_equal=True, canonical_indices_equal=True,
                every_integer_entry_equal_for_initial_states=[0, 1, 2],
                comparison='Unchanged exploration/exact_q3t4.py, original time-varying power-of-two witness.')


def run_case(T, name, G):
    table = coefficient_table(T, G)
    paths = list(it.product(range(Q), repeat=T))
    indices = general.source_indices(T)
    assert len(indices) == general.dimension(T)
    rows = [source_row(table, paths, idx) for idx in indices]
    assert all(G[q][0] == 1 for q in range(Q))
    for initial in (1, 2):
        for idx, row in zip(indices, rows):
            first_outcome = idx['values'][1 if idx['j'] else 0]
            multiplier = G[first_outcome][initial]
            assert source_row(table, paths, idx, initial) == [multiplier * x for x in row]
            assert multiplier % PRIME
    check = general.check_prime(T, indices, rows, PRIME)
    check.pop('expected_lifted_rank')
    check.pop('expected_extension_rank')
    check['full_lifted_row_count'] = 3 * general.dimension(T - 1)
    check['full_extension_row_count'] = 3 * (T - 2) * (3 * T - 8)
    result = dict(T=T, name=name, G=G, time_factors=[1] * T,
                  path_count=len(paths), source_row_count=len(indices),
                  counts_by_j={str(j): sum(idx['j'] == j for idx in indices)
                               for j in range(T - 2)},
                  integer_source_matrix_sha256=general.matrix_hash(rows),
                  exact_initial_row_rescaling_checked=True,
                  modular_check=check)
    print(json.dumps(dict(name=name, T=T, rows=len(indices),
                          ranks_by_initial_state=check['ranks_by_initial_state'],
                          lifted_rank=check['lifted_rank'],
                          extension_rank=check['extension_quotient_rank'],
                          full_row_rank=check['full_row_rank'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    witnesses = [('perturbed_previous_witness', ((1, 1, 1), (1, 2, 4), (1, 4, 17))),
                 ('integer_witness_2', ((1, 1, 1), (1, 2, 5), (1, 7, 11))),
                 ('integer_witness_3', ((1, 1, 1), (1, 3, 7), (1, 5, 19)))]
    regression = verify_timevarying_t4()
    cases = [run_case(T, name, G) for name, G in witnesses for T in (4, 5, 6)]
    result = dict(status='Exact external modular exploration; not Lean-verified.',
                  matrix_interpretation='K=M diag(A_y), where M is the actual prescribed source family and A_y is the positive ordinary path numerator.',
                  canonical_source='DHW equation(24), section3.4 restriction and footnote7 generation orders; identical index constructor to general_source24.py.',
                  witness_interpretation='Constant covariates x_t=0, beta=(0,1,2), gamma[q,r]=log(G[q][r]); alltime multipliers equal1.',
                  important_scope='Rank deficiencies reported here are modular only. They are not real-rank upper bounds or generic counterexamples. Residue-geometry and structural-dimension assumptions are not used for these direct source-matrix ranks.',
                  timevarying_T4_regression=regression,
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
