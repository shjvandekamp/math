#!/usr/bin/env python3
"""Direct finite-field evaluations of normalized sparse quotient columns.

No residue geometry or path enumeration is used. In row-vector notation,
  E[t,a] = X_a e_a (I-K_t),
  Fbar[t,s,a,b] = (X_a X_b/L[t,a]) e_b (I-P_s^(B\\{t})).
The latter divides F by the nonzero scalar A_t(a,b) before specializing
the common coefficient matrix G to a matrix with zero entries.

Full evaluation rank is an exact finite-field nonzero-minor certificate
for this finite rational specialization, external to Lean. A deficient
evaluation rank is only a lower bound for rational-function rank.

Reproduce:
  nice -n 19 python3 exploration/normalized_sparse_source24.py --output exploration/normalized-sparse-results.json
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import signal


P = 1000003
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('general_source24', ROOT / 'exploration/general_source24.py')
general = importlib.util.module_from_spec(spec)
spec.loader.exec_module(general)


def identity():
    return [[int(i == j) for j in range(3)] for i in range(3)]


def mmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) % P for j in range(3)]
            for i in range(3)]


def factors(n, mode):
    if mode == 'economic':
        return [(2 ** (3 * (i + 1)), 2 ** (6 * (i + 1))) for i in range(n)]
    rng = random.Random(240015)
    return [(rng.randrange(2, 10000), rng.randrange(2, 10000)) for _ in range(n)]


def coefficient_tables(G, time_factors):
    return [[[G[a][0], G[a][1] * u, G[a][2] * v] for a in range(3)]
            for u, v in time_factors]


def column_labels(n):
    return [('E', t, a) for t in range(n) for a in range(3)] + [
        ('Fbar', t, s, a, b) for t in range(n) for s in range(n) if t != s
        for a in range(3) for b in range(3)]


def evaluated_columns(tables, X):
    n = len(tables)
    denominators = [[sum(tables[t][a][i] * X[i] for i in range(3)) % P
                     for a in range(3)] for t in range(n)]
    if any(value == 0 for row in denominators for value in row):
        return None
    inverses = [[pow(value, -1, P) for value in row] for row in denominators]
    kernels = [[[tables[t][a][i] * X[i] * inverses[t][a] % P for i in range(3)]
                for a in range(3)] for t in range(n)]
    assert all(sum(row) % P == 1 for kernel in kernels for row in kernel)
    values = []
    for t in range(n):
        for a in range(3):
            values.append([X[a] * (int(i == a) - kernels[t][a][i]) % P for i in range(3)])
    for t in range(n):
        for s in range(n):
            if t == s:
                continue
            product = identity()
            for block in [s] + [i for i in range(n) if i not in (s, t)]:
                product = mmul(product, kernels[block])
            for a in range(3):
                for b in range(3):
                    scalar = X[a] * X[b] * inverses[t][a] % P
                    values.append([scalar * (int(i == b) - product[b][i]) % P
                                   for i in range(3)])
    assert all(sum(vector) % P == 0 for vector in values)
    return values


def check_case(name, G, mode, n):
    times = factors(n, mode)
    tables = coefficient_tables(G, times)
    labels = column_labels(n)
    target = 3 * n * (3 * n - 2)
    assert len(labels) == target
    echelon = general.Echelon(target, P)
    rng = random.Random(740024 + n)
    points = []
    skipped = 0
    matrix_digest = hashlib.sha256()
    while len(points) < target + 16 and echelon.rank < target:
        X = (1, rng.randrange(1, P), rng.randrange(1, P))
        values = evaluated_columns(tables, X)
        if values is None:
            skipped += 1
            continue
        point_id = len(points)
        points.append(X)
        for component in (0, 1):
            row = [value[component] for value in values]
            matrix_digest.update((','.join(map(str, row)) + '\n').encode())
            echelon.add(row, 2 * point_id + component)
    result = dict(name=name, G=G, mode=mode, n=n, source_panel_T=n + 2,
                  time_factors=times, prime=P, column_count=target,
                  evaluated_rank=echelon.rank, full_column_rank=echelon.rank == target,
                  evaluated_effect_points=len(points), denominator_zero_points_skipped=skipped,
                  effect_point_seed=740024 + n, effect_points=points,
                  evaluation_matrix_sha256=matrix_digest.hexdigest(),
                  nonzero_evaluation_minor=dict(size=echelon.rank,
                      rows=echelon.rows, columns=echelon.columns,
                      determinant_mod_prime=echelon.determinant,
                      row_labels='Row2j is component0 at effect_points[j]; row2j+1 is component1.',
                      column_labels='E(t,a) lexicographic, then Fbar(t,s,a,b) lexicographic with t!=s.',
                      ordering='Use rows and columns in the listed order.'),
                  rank_scope='A full nonzero minor proves this finite rational specialization independent; deficiency of these sampled evaluations is not a real-rank upper bound.')
    print(json.dumps({key: result[key] for key in
                      ('name', 'mode', 'n', 'column_count', 'evaluated_rank', 'full_column_rank', 'evaluated_effect_points')}), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Sparse normalized-column scan exceeded43 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(43)
    positive = ((1, 1, 1), (1, 2, 4), (1, 4, 17))
    sparse = [('primary_boundary', ((1, 1, 1), (1, 1, 0), (1, 0, 1))),
              ('one_zero', ((1, 1, 1), (1, 2, 0), (1, 4, 17))),
              ('cyclic_two_entries', ((1, 1, 0), (0, 1, 1), (1, 0, 1)))]
    cases = [check_case('positive_control', positive, 'economic', n) for n in range(2, 6)]
    assert all(case['full_column_rank'] for case in cases)
    for name, G in sparse:
        for mode in ('independent', 'economic'):
            for n in range(2, 6):
                cases.append(check_case(name, G, mode, n))
    extension = None
    for name, G in sparse:
        for mode in ('economic', 'independent'):
            prior = [case for case in cases if case['name'] == name and case['mode'] == mode]
            if all(case['full_column_rank'] for case in prior):
                extension = check_case(name, G, mode, 6)
                break
        if extension is not None:
            break
    signal.alarm(0)
    result = dict(status='External exact finite-field evaluation certificates; no Lean or all-n theorem.',
                  matrix_convention='G[lag][outcome]; A_t=G diag(1,u_t,v_t); row vectors.',
                  normalized_columns='E_t,a=X_a e_a(I-K_t); Fbar_t,s,a,b=(X_a X_b/L_ta)e_b(I-P_s^(B\\{t})).',
                  normalization_order='Divide F by the nonzero scalar A_t(a,b) before setting entries of G to zero; evaluating unnormalized F at zero entries would be a different family.',
                  effect_coordinates='X=(1,x,y), two zero-sum vector components per point; every evaluated denominator is checked nonzero modulo the prime.',
                  economic_mode='u_t=2^(3t),v_t=u_t^2, with one-based t=1,...,n.',
                  independent_mode='Deterministic independent positive integer time factors; not claimed to lie on a fixed two-slope scalar-covariate curve.',
                  positive_control_matches_known_full_rank=True,
                  cases=cases, useful_full_rank_case_extended_to_n6=extension,
                  limitation='Finite full-rank certificates do not prove arbitrary-n independence. Sparse G is a boundary specialization of the normalized functions; zero entries are not themselves a positive economic table.')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
