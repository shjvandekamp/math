#!/usr/bin/env python3
"""Test whether all three coordinate-axis divided residues determine J.

For each axis X_i=0, each old denominator line L_uc, and output d,
observe Res_(L_uc)(F_d/X_d)/(A_u(c,d)*X_c). A stripped final kernel
removes the output-coordinate division. If c=i, exact dual arithmetic
along the old line divides by the vanishing X_c coordinate.

The three output rows at each point have a verified weighted zero-sum
constraint, so the stacked observation rank is at most18m. Comparing
rank(Tstack) with rank([Tstack;J]) tests finite-field row-span inclusion.
An explicit Tstack-kernel vector with nonzero J image certifies failure.

Run:
  nice -n 19 python3 exploration/source24_three_axis_incidence.py --output exploration/source24-three-axis-incidence-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming


P, G = incoming.P, incoming.G
dual, regular = incoming.dual, incoming.regular


def axis_observations(m, A, axis):
    old = list(range(2, m + 2))
    _, columns = incoming.schur.canonical_labels(m + 2)
    observation, constraints = [], []
    for u in old:
        for c in range(3):
            line = (u, c)
            X = regular.edge_point(A, line, axis)
            kernels = {k: regular.kernel_or_residue(A, k, line, X, False) for k in old}
            stripped = {k: regular.kernel_or_residue(A, k, line, X, True) for k in old}
            words = {}
            for t in old:
                for first in old:
                    if t == first:
                        continue
                    word = [first] + [k for k in old if k not in (t, first)]
                    product = dual.identity()
                    for position, k in enumerate(word):
                        product = dual.mmul(product, stripped[k] if position == len(word) - 1 else kernels[k])
                    words[t, first] = product
            rows = [[], [], []]
            for t, first, a, b in columns:
                if t == u and a != c:
                    values = [dual.ZERO] * 3
                elif t == u:
                    scalar = dual.scale(A[t][a][b], X[a])
                    values = [dual.mul(scalar, dual.sub(dual.ONE if b == d else dual.ZERO,
                                                        dual.mul(X[b], words[t, first][b][d]))) for d in range(3)]
                else:
                    scalar = dual.scale(-A[t][a][b], dual.mul(dual.mul(X[a], X[b]),
                                                           dual.inverse(regular.dot(A[t][a], X))))
                    values = [dual.mul(scalar, value) for value in words[t, first][b]]
                for d in range(3):
                    if c == axis:
                        assert values[d][0] == 0
                        value = values[d][1] * pow(A[u][c][d], -1, P) % P
                    else:
                        value = values[d][0] * pow(A[u][c][d] * X[c][0] % P, -1, P) % P
                    rows[d].append(value)
            coefficients = [A[u][c][d] * X[d][0] % P for d in range(3)]
            assert sum(x != 0 for x in coefficients) == 2
            assert all(sum(coefficients[d] * rows[d][j] for d in range(3)) % P == 0
                       for j in range(len(columns)))
            constraints.append(dict(axis=axis, block=u, old_state=c,
                                    point_mod_prime=[x[0] for x in X], output_row_coefficients=coefficients))
            observation.extend(rows)
    return observation, constraints


def image(matrix, vector):
    return [sum(x * y for x, y in zip(row, vector)) % P for row in matrix]


def check_case(m):
    started = time.monotonic()
    times = incoming.sparse.factors(m, 'economic')
    A = [[list(row) for row in G] for _ in range(2)] + incoming.sparse.coefficient_tables(G, times)
    _, J, reference_axis0 = incoming.feedback_limit(m, A)
    observations, constraints, axis_certificates = [], [], []
    for axis in range(3):
        matrix, axis_constraints = axis_observations(m, A, axis)
        if axis == 0:
            assert matrix == reference_axis0
        observations.extend(matrix)
        constraints.extend(axis_constraints)
        axis_certificates.append(dict(axis=axis, **incoming.matrix_certificate(matrix)))
    observation_certificate = incoming.matrix_certificate(observations)
    stacked_certificate = incoming.matrix_certificate(observations + J)
    factors = observation_certificate['rank_certificate']['rank'] == stacked_certificate['rank_certificate']['rank']
    _, _, kernel = dual.rref_kernel(observations)
    witness = next((vector for vector in kernel if any(image(J, vector))), None)
    assert factors == (witness is None)
    counterexample = None
    if witness is not None:
        Jimage = image(J, witness)
        assert not any(image(observations, witness)) and any(Jimage)
        counterexample = dict(source_coefficients=[(j, x) for j, x in enumerate(witness) if x],
                              incidence_image=[(i, x) for i, x in enumerate(Jimage) if x],
                              observation_image_exactly_zero=True, incidence_image_nonzero=True)
    rows = [(u, c, d) for u in range(2, m + 2) for c in range(3) for d in range(3)]
    _, columns = incoming.schur.canonical_labels(m + 2)
    result = dict(m=m, prime=P, G=G, time_fixture='economic', old_time_factors=times,
                  source_column_labels=columns, per_axis_and_incidence_row_labels=rows,
                  observation_row_order='Axis0 rows, then axis1 rows, then axis2 rows; each uses per_axis_and_incidence_row_labels.',
                  axis_certificates=axis_certificates, observation_certificate=observation_certificate,
                  incidence_certificate=incoming.matrix_certificate(J), stacked_observation_incidence_certificate=stacked_certificate,
                  incidence_factors_at_fixture=factors, observation_kernel_dimension=len(kernel),
                  verified_counterexample=counterexample,
                  axis0_matches_existing_feedback_limit=True,
                  weighted_zero_sum_constraints_verified=True, row_constraints=constraints,
                  universal_observation_rank_bound=18*m,
                  stacked_minor_exceeds_observation_rank_bound=stacked_certificate['rank_certificate']['rank'] > 18*m,
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(m=m, source_columns=len(columns), observation_rank=observation_certificate['rank_certificate']['rank'],
                          J_rank=result['incidence_certificate']['rank_certificate']['rank'],
                          stacked_rank=stacked_certificate['rank_certificate']['rank'],
                          factors=factors, observation_rank_bound=18*m,
                          exceeds_bound=result['stacked_minor_exceeds_observation_rank_bound'],
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28:
            raise TimeoutError('28-second three-axis cutoff.')
        if incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('95MiB three-axis RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for m in (3, 4):
            cases.append(check_case(m))
        if time.monotonic()-started < 5 and cases[-1]['elapsed_seconds'] < 2:
            cases.append(check_case(5))
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='External exact modular row-span diagnostic, with verified witnesses when incidence factorization fails.',
                  observations='All three coordinate-axis limits of Res_(L_uc)(F_d/X_d)/(A_u(c,d)*X_c), using the regular extension at c=axis.',
                  rank_bound_reason='Each axis has3m disjoint output-row groups, each with one nonzero verified zero-sum constraint; the symbolic constraint gives rank<=6m per axis and<=18m in total.',
                  scope='Equal ranks show row-span inclusion at the displayed fixture only. A stacked nonzero minor larger than18m contradicts generic factorization because the structural observation-rank bound holds on the regular-geometry locus. No source-independence theorem follows.',
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=incoming.maximum_rss_bytes(), cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
