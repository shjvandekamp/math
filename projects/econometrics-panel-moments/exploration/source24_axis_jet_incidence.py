#!/usr/bin/env python3
"""Test whether axis-normal restrictions and matching normal jets determine J.

The domain is the old source-pair family F_(t,s,a,b), with m old blocks.
J sums coefficients over s at each fixed (t,a,b). Observations consist of
2m+1 generic values of F_i/X_i on each coordinate axis and the 3m normal
derivatives of g_i=D_old*F_i/X_i at R_(t,i)={L_(t,i)=X_i=0}.
For these jets only X_i varies; the other two coordinates stay fixed.

All calculations are exact modulo 1000003. Cleared numerators are computed
polynomially with dual numbers, so no pole is evaluated or divided by.
Negative cases include a verified observation-kernel vector with nonzero
J image, and a nonzero stacked minor exceeding the observation row count.

Reproduce:
  nice -n 19 python3 exploration/source24_axis_jet_incidence.py --output exploration/source24-axis-jet-incidence-results.json
"""

import argparse
import json
from pathlib import Path
import signal

import absorbing_firstjet as dual
import normalized_sparse_source24 as sparse
import source24_residue as residue


P = residue.PRIME
G = ((1, 1, 1), (1, 30, 10), (1, 3, 2))
ZERO, ONE = (0, 0), (1, 0)


def product(values):
    answer = ONE
    for value in values:
        answer = dual.mul(answer, value)
    return answer


def summed(values):
    answer = ZERO
    for value in values:
        answer = dual.add(answer, value)
    return answer


def cleared_numerators(A, labels, X, component, check_direct=False):
    """Return g_i, retaining the coefficient of the chosen normal direction."""
    m = len(A)
    L = [[summed(dual.scale(a, x) for a, x in zip(row, X)) for row in table] for table in A]
    omitted = [[product(L[t][j] for j in range(3) if j != a) for a in range(3)] for t in range(m)]
    D = [product(row) for row in L]
    D_all = product(D)
    M = [[[
        dual.scale(A[t][a][i], dual.mul(omitted[t][a], X[i])) for i in range(3)]
        for a in range(3)] for t in range(m)]
    stripped = [[[
        dual.scale(A[t][a][i], omitted[t][a]) for i in range(3)]
        for a in range(3)] for t in range(m)]
    words, direct = {}, {}
    if check_direct:
        K = [[[
            dual.scale(A[t][a][i], dual.mul(dual.inverse(L[t][a]), X[i])) for i in range(3)]
            for a in range(3)] for t in range(m)]
        S = [[[
            dual.scale(A[t][a][i], dual.inverse(L[t][a])) for i in range(3)]
            for a in range(3)] for t in range(m)]
    for t in range(m):
        for first in range(m):
            if t == first:
                continue
            word = [first] + [k for k in range(m) if k not in (t, first)]
            value, rational = dual.identity(), dual.identity()
            for position, k in enumerate(word):
                last = position == len(word) - 1
                value = dual.mmul(value, stripped[k] if last else M[k])
                if check_direct:
                    rational = dual.mmul(rational, S[k] if last else K[k])
            words[t, first] = value
            if check_direct:
                direct[t, first] = rational
    result = []
    for t, first, a, b in labels:
        bracket = dual.sub(product(D[k] for k in range(m) if k != t) if b == component else ZERO,
                           dual.mul(X[b], words[t, first][b][component]))
        value = dual.scale(A[t][a][b], dual.mul(dual.mul(X[a], omitted[t][a]), bracket))
        if check_direct:
            rational = dual.scale(A[t][a][b], dual.mul(dual.mul(X[a], dual.inverse(L[t][a])),
                dual.sub(ONE if b == component else ZERO, dual.mul(X[b], direct[t, first][b][component]))))
            assert value == dual.mul(D_all, rational)
        result.append(value)
    return result, L


def image(matrix, vector):
    return [sum(x * y for x, y in zip(row, vector)) % P for row in matrix]


def check_case(m):
    times = sparse.factors(m, 'economic')
    A = sparse.coefficient_tables(G, times)
    labels = [(t, s, a, b) for t in range(m) for s in range(m) if t != s
              for a in range(3) for b in range(3)]
    incidence_labels = [(t, a, b) for t in range(m) for a in range(3) for b in range(3)]
    observations, observation_labels = [], []
    for i in range(3):
        j, k = [x for x in range(3) if x != i]
        count = 0
        for parameter in range(1, 500):
            X = [ZERO] * 3
            X[j], X[k] = ONE, (parameter, 0)
            L0 = [[sum(row[q] * X[q][0] for q in range(3)) % P for row in table] for table in A]
            if any(value == 0 for row in L0 for value in row):
                continue
            values, _ = cleared_numerators(A, labels, X, i, check_direct=True)
            denominator = 1
            for row in L0:
                for value in row:
                    denominator = denominator * value % P
            inverse = pow(denominator, -1, P)
            observations.append([value[0] * inverse % P for value in values])
            observation_labels.append(dict(kind='axis_value', component=i,
                                           point_mod_prime=[x[0] for x in X], parameter=parameter))
            count += 1
            if count == 2 * m + 1:
                break
        assert count == 2 * m + 1
    axis_count = len(observations)
    axis_rank = residue.modular_rank(observations, P)
    basepoint_coordinates = [[] for _ in range(3)]
    for t in range(m):
        for i in range(3):
            j, k = [x for x in range(3) if x != i]
            X = [ZERO] * 3
            X[i], X[j] = (0, 1), ONE
            X[k] = (-A[t][i][j] * pow(A[t][i][k], -1, P) % P, 0)
            values, L = cleared_numerators(A, labels, X, i)
            assert L[t][i][0] == 0 and L[t][i][1]
            assert all(L[u][a][0] for u in range(m) for a in range(3) if (u, a) != (t, i))
            assert all(value[0] == 0 for value in values)
            observations.append([value[1] for value in values])
            observation_labels.append(dict(kind='matching_normal_jet', old_block=t, component=i,
                                           point_mod_prime=[x[0] for x in X], direction='Only X_i varies; the other coordinates are fixed.'))
            basepoint_coordinates[i].append(X[k][0])
    assert all(len(set(points)) == m for points in basepoint_coordinates)
    J = [[int((u, c, d) == (t, a, b)) for u, first, c, d in labels] for t, a, b in incidence_labels]
    observed_rank = residue.modular_rank(observations, P)
    J_rank = residue.modular_rank(J, P)
    stacked_rank = residue.modular_rank(observations + J, P)
    assert J_rank['rank'] == 9 * m
    _, _, kernel = dual.rref_kernel(observations)
    vector = next((v for v in kernel if any(image(J, v))), None)
    factors = observed_rank['rank'] == stacked_rank['rank']
    assert factors == (vector is None)
    certificate = None
    if vector is not None:
        assert not any(image(observations, vector))
        J_image = image(J, vector)
        assert any(J_image)
        certificate = dict(source_coefficients=[dict(column=i, source_label=labels[i], coefficient=x)
                                               for i, x in enumerate(vector) if x],
                           J_image=[dict(row=i, incidence_label=incidence_labels[i], value=x)
                                    for i, x in enumerate(J_image) if x],
                           observation_image_verified_zero=True, incidence_image_verified_nonzero=True)
    result = dict(m=m, prime=P, G=G, time_factors=times,
                  block_numbering='Zero based in this script; block t corresponds to source24_residue block t+2.',
                  source_column_count=len(labels), source_column_order='(t,s,a,b) lexicographic with t != s.',
                  incidence_row_order='(t,a,b) lexicographic; J sums coefficients over s.',
                  axis_observation_count=axis_count, total_observation_count=len(observations),
                  observation_labels=observation_labels,
                  axis_rank_certificate=axis_rank, observation_rank_certificate=observed_rank,
                  incidence_rank_certificate=J_rank, stacked_rank_certificate=stacked_rank,
                  stacked_row_order='All observation rows above, then J rows in incidence_row_order.',
                  incidence_factors_through_observations_at_fixture=factors,
                  stacked_rank_exceeds_total_observation_count=stacked_rank['rank'] > len(observations),
                  row_space_intersection_dimension=observed_rank['rank'] + J_rank['rank'] - stacked_rank['rank'],
                  observation_sha256=residue.matrix_hash(observations), incidence_sha256=residue.matrix_hash(J),
                  stacked_sha256=residue.matrix_hash(observations + J), kernel_counterexample=certificate,
                  cleared_polynomial_vs_stripped_rational_axis_values_verified=True,
                  every_g_i_vanishes_at_each_matching_basepoint=True,
                  matching_basepoints_distinct_on_each_axis=True,
                  axis_sampling_justification='g_i has degree 3m and vanishes at the m distinct matching basepoints on X_i=0. Dividing their known linear factors leaves degree at most 2m. The 2m+1 distinct nonpole samples determine the entire axis-normal restriction over this field.')
    print(json.dumps(dict(m=m, columns=len(labels), axis_rank=axis_rank['rank'],
                          observations=len(observations), observation_rank=observed_rank['rank'],
                          J_rank=J_rank['rank'], stacked_rank=stacked_rank['rank'],
                          factors_at_fixture=factors)), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Axis/jet incidence check exceeded 28 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(28)
    cases = [check_case(m) for m in (2, 3, 4)]
    signal.alarm(0)
    result = dict(status='External exact finite-field obstruction to the proposed incidence factorization; not a Lean theorem.',
                  cleared_numerator='g_i=A_t(a,b)*X_a*(D_t/L_ta)*[delta_bi*product_(k!=t)D_k-X_b*e_b*product_word(M_k, last stripped)_i].',
                  polynomial_kernels='M_k=diag(product_(r!=lag)L_kr)*A_k*diag(X); the last factor omits diag(X).',
                  normal_jet='Partial derivative with respect to X_i of g_i, at L_ti=X_i=0, holding both other coordinates fixed.',
                  generic_obstruction='At m=3,4 the stacked nonzero-minor size exceeds the total number of observation rows. After denominator clearing this excludes a generic factorization through this proposed finite observation system; it is not solely a rank drop at the displayed observation matrix.',
                  limitations='This rejects the axis-plus-3m-matching-normal-jets candidate. It neither rules out richer observations nor determines source-family independence.',
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
