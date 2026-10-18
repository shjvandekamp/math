#!/usr/bin/env python3
"""Exact finite-field jets of the shared-new polar half.

For each fixed new-line state a this constructs the 3m-square matrix with
rows (old block t, old-line state c) and columns (first old block s, b).
The normalized row vector is -Y_a Y_b e_b P_s^res W, where
Y=(X0/epsilon,1,z), W=epsilon^(B-1) K_N^(-1), and B is 2 or 3.
All moving-intersection, old-kernel, prefactor, and inverse derivatives
are retained. The legitimate first-jet test is [M0_piv,M1*N], where
the constant kernel basis N is verified by M0*N=0.

This is a finite modular experiment on one polar half, not an all-length
theorem or a determinant certificate for the full source family.

Reproduce:
  nice -n 19 python3 exploration/shared_new_polar_firstjet.py --output exploration/shared-new-polar-firstjet-results.json
"""

import argparse
from contextlib import contextmanager
import json
from pathlib import Path
import signal

import absorbing_firstjet as dual
import source24_residue as residue


P = dual.P
ZERO, ONE, EPSILON = (0, 0), (1, 0), (0, 1)
G = ((1, 1, 1), (1, 2, 4), (1, 4, 17))
ALPHA, BETA = tuple(row[1] for row in G), tuple(row[2] for row in G)
GINV = [[x * pow(7, -1, P) % P for x in row]
        for row in ((18, -13, 2), (-13, 16, -3), (2, -3, 1))]
assert residue.matmul(G, GINV, P) == residue.identity()


@contextmanager
def transition_fixture(matrix):
    """Temporarily use another validated common matrix in the same formulas."""
    global G, ALPHA, BETA, GINV
    saved = G, ALPHA, BETA, GINV
    G = tuple(tuple(row) for row in matrix)
    assert all(row[0] == 1 and all(x > 0 for x in row) for row in G)
    ALPHA, BETA = tuple(row[1] for row in G), tuple(row[2] for row in G)
    assert len(set(ALPHA)) == 3
    adjugate = []
    for i in range(3):
        row = []
        for j in range(3):
            remaining_rows = [r for r in range(3) if r != j]
            remaining_columns = [c for c in range(3) if c != i]
            minor = (G[remaining_rows[0]][remaining_columns[0]] * G[remaining_rows[1]][remaining_columns[1]]
                     - G[remaining_rows[0]][remaining_columns[1]] * G[remaining_rows[1]][remaining_columns[0]])
            row.append((-1) ** (i + j) * minor)
        adjugate.append(row)
    determinant = sum(G[0][i] * adjugate[i][0] for i in range(3))
    assert determinant % P
    GINV = [[x * pow(determinant, -1, P) % P for x in row] for row in adjugate]
    assert residue.matmul(G, GINV, P) == residue.identity()
    try:
        yield
    finally:
        G, ALPHA, BETA, GINV = saved


def power(value, exponent):
    answer = ONE
    for _ in range(exponent):
        answer = dual.mul(answer, value)
    return answer


def summed(values):
    answer = ZERO
    for value in values:
        answer = dual.add(answer, value)
    return answer


def word_product(matrices, first):
    product = dual.identity()
    for t in [first] + [i for i in range(len(matrices)) if i != first]:
        product = dual.mmul(product, matrices[t])
    return product


def moving_point_and_inverse(tables, a, t, c, B):
    old0, old1, old2 = tables[t][c]
    z = dual.mul(dual.sub(dual.scale(old0 * ALPHA[a], EPSILON), (old1 % P, 0)),
                 dual.inverse(dual.sub((old2 % P, 0),
                                       dual.scale(old0 * BETA[a], power(EPSILON, B)))))
    Y0 = dual.sub((-ALPHA[a] % P, 0),
                  dual.scale(BETA[a], dual.mul(power(EPSILON, B - 1), z)))
    Y = (Y0, ONE, z)
    X = (dual.mul(EPSILON, Y0), ONE, z)
    assert z == (-old1 * pow(old2, -1, P) % P,
                 old0 * ALPHA[a] * pow(old2, -1, P) % P)
    assert summed(dual.scale(tables[t][c][i], X[i]) for i in range(3)) == ZERO
    assert summed((X[0], dual.scale(ALPHA[a], EPSILON),
                   dual.scale(BETA[a], dual.mul(power(EPSILON, B), z)))) == ZERO
    # L_Nj = epsilon*D_j, and K_N^-1=diag(X)^-1 A_N^-1 diag(L_N).
    # Hence W=diag(epsilon^(B-1)/Y0,epsilon^(B-1),1/z) G^-1 diag(D).
    D = [dual.add((ALPHA[j] - ALPHA[a], 0),
                  dual.scale(BETA[j] - BETA[a], dual.mul(power(EPSILON, B - 1), z)))
         for j in range(3)]
    row_factors = (dual.mul(power(EPSILON, B - 1), dual.inverse(Y0)),
                   power(EPSILON, B - 1), dual.inverse(z))
    W = [[dual.scale(GINV[i][j], dual.mul(row_factors[i], D[j]))
          for j in range(3)] for i in range(3)]
    assert all(W[i][a] == ZERO for i in range(3))
    assert all(summed(row) == power(EPSILON, B - 1) for row in W)
    return X, Y, W


def matrices_at_pole(tables, X, t, c):
    matrices = []
    for block, table in enumerate(tables):
        numerators = [[dual.scale(table[state][i], X[i]) for i in range(3)]
                      for state in range(3)]
        denominators = [summed(row) for row in numerators]
        if block == t:
            assert denominators[c] == ZERO
            assert all(denominators[state][0] for state in range(3) if state != c)
            matrix = [row if state == c else [ZERO] * 3
                      for state, row in enumerate(numerators)]
            assert all(summed(row) == ZERO for row in matrix)
        else:
            assert all(value[0] for value in denominators), 'A third old line passes through the limiting point.'
            matrix = [[dual.mul(value, dual.inverse(denominators[state])) for value in row]
                      for state, row in enumerate(numerators)]
            assert all(summed(row) == ONE for row in matrix)
        matrices.append(matrix)
    return matrices


def first_jet_matrix(times, a, B, tables=None):
    m = len(times)
    tables = dual.sparse.coefficient_tables(G, times) if tables is None else tables
    output_component = next(j for j in range(3) if j != a)
    M0, M1 = [], []
    for t in range(m):
        for c in range(3):
            X, Y, W = moving_point_and_inverse(tables, a, t, c, B)
            assert W[2][output_component][0]
            matrices = matrices_at_pole(tables, X, t, c)
            values = []
            for s in range(m):
                transformed = dual.mmul(word_product(matrices, s), W)
                for b in range(3):
                    prefactor = dual.scale(-1, dual.mul(Y[a], Y[b]))
                    vector = [dual.mul(prefactor, value) for value in transformed[b]]
                    assert vector[a] == ZERO and summed(vector) == ZERO
                    values.append(vector[output_component])
            M0.append([value[0] for value in values])
            M1.append([value[1] for value in values])
    return M0, M1, output_component


def finite_epsilon_controls(times, a, B):
    """Check the inverse and epsilon normalization without dual arithmetic.

    The inverse formula is the algebraic continuation of K_N^-1 to its
    pole line. K_N itself is not evaluated on that line.
    """
    tables = dual.sparse.coefficient_tables(G, times)
    count = 0
    for epsilon in (pow(7, -1, P), 2 * pow(11, -1, P) % P):
        epsB = pow(epsilon, B, P)
        AN = [[1, ALPHA[j] * epsilon % P, BETA[j] * epsB % P] for j in range(3)]
        ANinv = [[GINV[i][j] * pow((1, epsilon, epsB)[i], -1, P) % P
                  for j in range(3)] for i in range(3)]
        assert residue.matmul(AN, ANinv, P) == residue.identity()
        for t, (u, v) in enumerate(times):
            for c in range(3):
                z = ((epsilon * ALPHA[a] - ALPHA[c] * u)
                     * pow(BETA[c] * v - epsB * BETA[a], -1, P)) % P
                X = ((-epsilon * ALPHA[a] - epsB * BETA[a] * z) % P, 1, z)
                Y = (X[0] * pow(epsilon, -1, P) % P, 1, z)
                assert all(X) and residue.dot(tables[t][c], X, P) == 0
                L = [residue.dot(row, X, P) for row in AN]
                assert L[a] == 0 and all(L[j] for j in range(3) if j != a)
                eps_scale = pow(epsilon, B - 1, P)
                W_direct = [[eps_scale * pow(X[i], -1, P) * ANinv[i][j] * L[j] % P
                             for j in range(3)] for i in range(3)]
                D = [(ALPHA[j] - ALPHA[a] + eps_scale * (BETA[j] - BETA[a]) * z) % P
                     for j in range(3)]
                factors = (eps_scale * pow(Y[0], -1, P) % P, eps_scale, pow(z, -1, P))
                W_closed = [[factors[i] * GINV[i][j] * D[j] % P for j in range(3)]
                            for i in range(3)]
                assert W_closed == W_direct
                inverse_scale = pow(eps_scale, -1, P)
                for b in range(3):
                    # Apply the original epsilon^(B-1-kappa_a-kappa_b)
                    # scaling before replacing X0/epsilon by Y0.
                    kappa = int(a == 0) + int(b == 0)
                    scalar = (-X[a] * X[b] * pow(epsilon, B - 1 - kappa, P) * inverse_scale) % P
                    assert scalar == -Y[a] * Y[b] % P
                count += 1
    return count


def check_case(m, mode, a, B):
    times = dual.sparse.factors(m, mode)
    M0, M1, component = first_jet_matrix(times, a, B)
    pivots, free, vectors = dual.rref_kernel(M0)
    expected_rank = 3 * m - (2 if m % 2 == 0 else 0)
    assert len(pivots) == expected_rank, (m, mode, a, B, len(pivots), expected_rank)
    jet = [[row0[c] for c in pivots]
           + [sum(x * y for x, y in zip(row1, vector)) % P for vector in vectors]
           for row0, row1 in zip(M0, M1)]
    ranked = residue.modular_rank(jet, P)
    controls = finite_epsilon_controls(times, a, B)
    result = dict(m=m, time_mode=mode, new_line_state=a, exponent_B=B, prime=P,
                  G=G, old_time_factors=times, output_component=component,
                  all_blocks_satisfy_v_equals_u_squared=(mode == 'economic' and B == 2),
                  rows=3 * m, columns=3 * m, M0_rank=len(pivots), M0_nullity=len(free),
                  binary_parity_prediction=expected_rank,
                  kernel_complement_first_jet_rank=ranked['rank'],
                  full_first_jet_rank=ranked['rank'] == 3 * m,
                  M0_pivot_columns=pivots, M0_free_columns=free,
                  kernel_vectors=vectors, M0_kernel_verified=True,
                  row_order='(old block t,old-line state c), lexicographic, zero based.',
                  column_order='(first old block s,outcome b), lexicographic, zero based.',
                  first_jet_column_order='Original M0 pivot columns, then M1 times each listed kernel vector.',
                  first_jet_rank_certificate=ranked,
                  M0_sha256=residue.matrix_hash(M0), M1_sha256=residue.matrix_hash(M1),
                  first_jet_sha256=residue.matrix_hash(jet),
                  finite_epsilon_inverse_and_normalization_checks=controls,
                  finite_epsilon_points=['1/7', '2/11'],
                  first_jet_determinant_coefficient_mod_prime=ranked['determinant_mod_prime'],
                  determinant_exponent_in_transformed_basis=len(free) if ranked['full_rank'] else None,
                  scope='This is one fixed-new-line shared-new polar half. Full first-jet rank would prove a nonzero finite rational determinant after denominator clearing. A deficient first jet does not exclude higher orders.')
    print(json.dumps({key: result[key] for key in ('m', 'time_mode', 'new_line_state', 'exponent_B',
          'M0_rank', 'M0_nullity', 'kernel_complement_first_jet_rank', 'full_first_jet_rank')}), flush=True)
    return result


def derivative_coefficients(m, mode, a, positions=None, times_override=None):
    """Keep old ratios fixed and isolate every linear w_t coefficient."""
    times = dual.sparse.factors(m, mode) if times_override is None else times_override
    assert len(times) == m
    ratios = [v * pow(u, -1, P) % P for u, v in times]

    def evaluate(weights):
        tables = [[[weights[t], ALPHA[c], BETA[c] * ratios[t] % P] for c in range(3)]
                  for t in range(m)]
        return first_jet_matrix(times, a, 3, tables=tables)

    zero0, zero1, component = evaluate([0] * m)
    assert not any(value for row in zero1 for value in row)
    pivots, free, vectors = dual.rref_kernel(zero0)
    assert len(free) == 2
    summed_derivative = [[0] * (3 * m) for _ in range(3 * m)]
    all_derivative = None
    probes = []
    positions = list(range(m)) if positions is None else list(positions)
    choices = [('all_one', [1] * m)] + [
        (f'single_{t}', [int(i == t) for i in range(m)]) for t in positions]
    for label, weights in choices:
        M0, M1, _ = evaluate(weights)
        assert M0 == zero0
        if label == 'all_one':
            all_derivative = M1
        else:
            summed_derivative = [[(x + y) % P for x, y in zip(rowx, rowy)]
                                  for rowx, rowy in zip(summed_derivative, M1)]
        jet = [[row0[c] for c in pivots]
               + [sum(x * y for x, y in zip(row1, vector)) % P for vector in vectors]
               for row0, row1 in zip(M0, M1)]
        ranked = residue.modular_rank(jet, P)
        probes.append(dict(label=label, weights=weights, first_jet_rank=ranked['rank'],
                           first_jet_determinant_mod_prime=ranked['determinant_mod_prime'],
                           nonzero_minor=ranked['nonzero_minor'],
                           M1_sha256=residue.matrix_hash(M1)))
    if positions == list(range(m)):
        assert summed_derivative == all_derivative
    result = dict(m=m, ratio_family=mode, new_line_state=a, exponent_B=3, prime=P, G=G,
                  ratios_mod_prime=ratios, original_old_time_factors=times,
                  old_table_definition='Abar_t=G*diag(w_t,1,r_t); its pole residue uses this normalized coefficient table.',
                  output_component=component, M0_rank=len(pivots), M0_nullity=len(free),
                  M0_pivot_columns=pivots, M0_free_columns=free, kernel_vectors=vectors,
                  M0_sha256=residue.matrix_hash(zero0), M0_independent_of_weights_verified=True,
                  M1_at_zero_weights_is_zero=True,
                  sum_of_single_weight_derivatives_equals_all_one=True if positions == list(range(m)) else None,
                  probes=probes,
                  scope='Zero weights are algebraic boundary diagnostics, not positive economic parameters. The ratio-family label describes only r_t; varying w_t does not preserve v_t=u_t^2.')
    print(json.dumps(dict(derivative_coefficients=True, m=m, ratio_family=mode, a=a,
                          M0_rank=len(pivots), probe_ranks={x['label']: x['first_jet_rank'] for x in probes})), flush=True)
    return result


def asymmetric_checks():
    """Three positive common matrices, with unchanged old economic fixtures."""
    fixtures = (
        ('asymmetric_A30', ((1, 1, 1), (1, 30, 10), (1, 3, 2))),
        ('asymmetric_A300', ((1, 1, 1), (1, 300, 100), (1, 3, 2))),
        ('asymmetric_generic', ((1, 1, 1), (1, 2, 5), (1, 7, 11))),
    )
    results = []
    for name, matrix in fixtures:
        with transition_fixture(matrix):
            for m in (2, 4, 6):
                for a in range(3):
                    ordinary = check_case(m, 'economic', a, 3)
                    isolated = derivative_coefficients(m, 'economic', a, positions=[m - 1])
                    results.append(dict(fixture=name, ordinary_old_time_case=ordinary,
                                        fixed_ratio_last_block_derivative=isolated))
    return results


def finite_polar_matrix(times, a, B, epsilon):
    """Actual normalized shared-new residue matrix at nonzero epsilon."""
    m = len(times)
    tables = dual.sparse.coefficient_tables(G, times)
    epsB, eps_scale = pow(epsilon, B, P), pow(epsilon, B - 1, P)
    AN = [[1, ALPHA[j] * epsilon % P, BETA[j] * epsB % P] for j in range(3)]
    ANinv = [[GINV[i][j] * pow((1, epsilon, epsB)[i], -1, P) % P
              for j in range(3)] for i in range(3)]
    component = next(j for j in range(3) if j != a)
    matrix = []
    for t, (u, v) in enumerate(times):
        for c in range(3):
            z = ((epsilon * ALPHA[a] - ALPHA[c] * u)
                 * pow(BETA[c] * v - epsB * BETA[a], -1, P)) % P
            X = ((-epsilon * ALPHA[a] - epsB * BETA[a] * z) % P, 1, z)
            Y = (X[0] * pow(epsilon, -1, P) % P, 1, z)
            L = [residue.dot(row, X, P) for row in AN]
            assert L[a] == 0 and all(L[j] for j in range(3) if j != a) and all(X)
            W = [[eps_scale * pow(X[i], -1, P) * ANinv[i][j] * L[j] % P
                  for j in range(3)] for i in range(3)]
            matrices = []
            for block in range(m):
                if block == t:
                    vector = [tables[t][c][i] * X[i] % P for i in range(3)]
                    assert sum(vector) % P == 0
                    matrices.append([vector[:] if state == c else [0, 0, 0] for state in range(3)])
                else:
                    matrices.append(residue.ordinary_kernel(tables, block, X, P))
            row = []
            for s in range(m):
                word = [s] + [i for i in range(m) if i != s]
                product = residue.matmul(residue.word_product(matrices, word, P), W, P)
                for b in range(3):
                    vector = [-Y[a] * Y[b] * value % P for value in product[b]]
                    assert vector[a] == 0 and sum(vector) % P == 0
                    row.append(vector[component])
            matrix.append(row)
    return matrix


def finite_m2_check(a, numerator, denominator):
    times = dual.sparse.factors(2, 'economic')
    epsilon = numerator * pow(denominator, -1, P) % P
    matrix = finite_polar_matrix(times, a, 3, epsilon)
    ranked = residue.modular_rank(matrix, P)
    result = dict(m=2, new_line_state=a, old_time_mode='economic', exponent_B=3,
                  epsilon=f'{numerator}/{denominator}', prime=P, old_time_factors=times,
                  rank_certificate=ranked, matrix_sha256=residue.matrix_hash(matrix),
                  scope='Exact modular rank at this nonzero epsilon only. Deficiency is not a real-rank upper bound; the B3 new block does not obey the old v=u^2 relation.')
    print(json.dumps(dict(finite_m2=True, a=a, epsilon=result['epsilon'], rank=ranked['rank'])), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Shared-new polar first-jet check exceeded 28 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(28)
    cases = [check_case(m, mode, a, B) for B in (3, 2)
             for mode in ('independent', 'economic')
             for m in ((2, 3, 4, 6) if B == 3 else (2, 3, 4)) for a in range(3)]
    coefficients = [derivative_coefficients(m, mode, a)
                    for mode in ('independent', 'economic') for m in (4, 6) for a in range(3)]
    finite_cases = [finite_m2_check(a, numerator, denominator)
                    for a in range(3) for numerator, denominator in ((1, 7), (2, 11))]
    asymmetric_cases = asymmetric_checks()
    signal.alarm(0)
    result = dict(status='External finite-field exact first-jet calculations; no Lean or all-length theorem.',
                  normalized_row='-Y_a*Y_b*e_b*P_s_old_residue*W',
                  moving_intersection='X1=1; z=(epsilon*alpha_a-alpha_c*u_t)/(beta_c*v_t-epsilon^B*beta_a); X0=-epsilon*alpha_a-epsilon^B*beta_a*z.',
                  inverse_identity='W=epsilon^(B-1)*K_N^-1=diag(epsilon^(B-1)/Y0,epsilon^(B-1),1/z)*G^-1*diag(alpha_j-alpha_a+epsilon^(B-1)*(beta_j-beta_a)*z).',
                  derivative_method='Exact arithmetic in F_p[epsilon]/(epsilon^2), including moving intersections and all normalized prefactors.',
                  first_jet_method='[M0[:,pivots],M1*N], with a verified constant kernel basis and invertible constant change of columns; no stacking of jets.',
                  limitations='Only m=2,3,4,6, the displayed time families, three new-line states, and B=2,3. Only B2 with economic old times obeys v=u^2 in every block. This does not establish the full residue determinant, full source-family independence, or an all-m result.',
                  cases=cases, derivative_coefficient_cases=coefficients,
                  finite_epsilon_m2_cases=finite_cases,
                  asymmetric_transition_cases=asymmetric_cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
