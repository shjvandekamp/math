#!/usr/bin/env python3
"""Exact finite-field checks of residue differences and marked seed splitting.

Construct D directly from R3/R5 of SOURCE24_RESIDUE_DIFFERENCES.md on the
full alpha/beta pair space, independently of the actual old source matrix O.
Check D O = T_output0 - T_output1 and the seed identity D S = I - e gamma^T.
The single-block E gauge has zero pair residue and T(E)=J(E)=-1 in all three
outputs of its line. It is retained when evaluating the seed rows.

The optional incoming calculation uses the actual solution O Y=Z and checks
the decomposition before recording its ranks. Every result is finite modular
evidence; no uniform rank or source-independence theorem is asserted.

Reproduce:
  nice -n 19 python3 exploration/source24_residue_differences.py --output exploration/source24-residue-differences-results.json
"""

import argparse
import itertools as it
import json
from pathlib import Path
import signal
import time

import source24_auxiliary_feedback as auxiliary
import source24_odd_incoming as incoming


P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matrix_sum(a, b):
    assert len(a) == len(b) and len(a[0]) == len(b[0])
    return [[(x + y) % P for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def outer(a, b):
    return [[x * y % P for y in b] for x in a]


def require_equal(name, actual, expected):
    assert len(actual) == len(expected)
    for i, (actual_row, expected_row) in enumerate(zip(actual, expected)):
        assert len(actual_row) == len(expected_row)
        for j, (x, y) in enumerate(zip(actual_row, expected_row)):
            if (x - y) % P:
                raise AssertionError(f'{name}: entry ({i},{j}) is {x % P}, expected {y % P}.')


def check_geometry(m, A):
    """Check every denominator used in R3/R5, including same-block geometry."""
    lines = [(t, a) for t in range(2, m + 2) for a in range(3)]
    assert all(A[t][a][0] % P == 1 for t, a in lines)
    assert all(x % P for t, a in lines for x in A[t][a])
    assert len({tuple(x % P for x in A[t][a]) for t, a in lines}) == len(lines)
    for line, other in it.combinations(lines, 2):
        X = residue.cross(A[line[0]][line[1]], A[other[0]][other[1]], P)
        assert all(X), ('Zero pair coordinate.', line, other, X)
        zeros = {label for label in lines if residue.dot(A[label[0]][label[1]], X, P) == 0}
        assert zeros == {line, other}, ('Unintended triple point.', line, other, zeros)
    for line in lines:
        coefficients = A[line[0]][line[1]]
        for edge in range(3):
            axis = [int(i == edge) for i in range(3)]
            X = residue.cross(coefficients, axis, P)
            assert X[edge] == 0 and all(X[i] for i in range(3) if i != edge)
            assert all(residue.dot(A[t][a], X, P) for t, a in lines if (t, a) != line)
    return dict(normalized_first_coefficients_equal_one=True,
                all_line_coefficients_nonzero=True, distinct_old_lines=True,
                all_pair_coordinates_nonzero_including_same_block=True,
                no_unintended_three_line_points=True,
                every_coordinate_edge_point_is_on_only_its_matching_line=True)


def difference_operator(m, A, cross_scale=1, axis_scale=1):
    """R3/R5 in exactly the pair representatives and basis used by O.

    A pair coordinate alpha/beta multiplies v_u(P)/v_v(P). With P rescaled
    by k these coordinates scale by k^2; the entries of D scale by k^-2.
    The axis representative Q has no such coordinate dependence.
    """
    pair_labels, _ = schur.canonical_labels(m + 2)
    lines = [(t, a) for t in range(2, m + 2) for a in range(3)]
    line_index = {line: i for i, line in enumerate(lines)}
    D = [[0] * len(pair_labels) for _ in lines]
    for j in range(0, len(pair_labels), 2):
        u, v, cu, cv, coordinate = pair_labels[j]
        assert coordinate == 'alpha' and pair_labels[j + 1] == (u, v, cu, cv, 'beta')
        X = [cross_scale * x % P for x in residue.cross(A[u][cu], A[v][cv], P)]
        U = [A[u][cu][d] * X[d] % P for d in range(3)]
        V = [A[v][cv][d] * X[d] % P for d in range(3)]
        for line, other in (((u, cu), (v, cv)), ((v, cv), (u, cu))):
            t, c = line
            a1, a2 = A[t][c][1:]
            Q = [0, axis_scale % P, -axis_scale * a1 * pow(a2, -1, P) % P]
            assert residue.dot(A[t][c], Q, P) == 0
            axis_factor = a2 * Q[2] * pow(residue.dot(A[other[0]][other[1]], Q, P), -1, P) % P
            denominator_inverse = pow(a2 * X[c] * X[2] % P, -1, P)
            for offset, basis_vector in enumerate((U, V)):
                kappa = (basis_vector[0] * pow(X[0], -1, P)
                         - basis_vector[1] * pow(a1 * X[1] % P, -1, P)) * denominator_inverse % P
                D[line_index[line]][j + offset] = axis_factor * kappa % P
    return D, lines, pair_labels


def seed_coefficients(m, A):
    """The actual auxiliary U coefficients; E is kept in a separate matrix."""
    old = list(range(2, m + 2))
    _, pair_columns = schur.canonical_labels(m + 2)
    pair_index = {label: i for i, label in enumerate(pair_columns)}
    labels = [(t, a) for t in old for a in range(3)]
    index = {label: i for i, label in enumerate(labels)}
    C = [[0] * len(labels) for _ in pair_columns]
    E = [[0] * len(labels) for _ in labels]
    constants = []
    for j, (t, a) in enumerate(labels):
        r = min(u for u in old if u != t)
        s = min(u for u in old if u != r)
        X = [0, A[r][0][2] % P, -A[r][0][1] % P]
        K = residue.ordinary_kernel(A, t, X, P)
        determinant = (K[1][1] * K[2][2] - K[1][2] * K[2][1]) % P
        assert determinant
        c = X[a] * pow(residue.dot(A[t][a], X, P) * determinant % P, -1, P) % P if a else 0
        C[pair_index[t, r, a, 0]][j] = pow(A[t][a][0], -1, P)
        for b in range(3):
            row = pair_index[r, s, 0, b]
            C[row][j] = (C[row][j] - c) % P
        E[index[r, 0]][j] = -c % P
        constants.append(dict(t=t, A=a, r=r, s=s, c_tA=c))
    return C, E, labels, constants


def check_incoming(m, A, O, D, S, C, gamma, inverse_DS, B, output_labels, record):
    Z, _, _ = incoming.incoming_coefficients(m, A)
    DZ = schur.matrix_product(D, Z)
    eta = schur.matrix_product(inverse_DS, DZ)
    z0 = schur.matrix_difference(Z, schur.matrix_product(S, eta))
    require_equal('D z0 = 0', schur.matrix_product(D, z0), [[0] * len(Z[0]) for _ in D])
    Y, solve = incoming.solve_old_source(O, Z)
    record['actual_old_source_solve'] = solve
    if Y is None:
        record['incoming_limitation'] = 'Actual O is singular at this fixture; no Y was substituted.'
        return
    Y0 = schur.matrix_difference(Y, schur.matrix_product(C, eta))
    require_equal('O Y0 = z0', schur.matrix_product(O, Y0), z0)
    BY, BY0 = schur.matrix_product(B, Y), schur.matrix_product(B, Y0)
    gamma_DZ = schur.matrix_product([gamma], DZ)[0]
    e_output = [int(label == (2, 0, 0)) for label in output_labels]
    correction = outer(e_output, gamma_DZ)
    require_equal('B Y = B Y0 + e_output gamma^T D Z', BY, matrix_sum(BY0, correction))
    binary = [i for i, (_, _, d) in enumerate(output_labels) if d in (1, 2)]
    binary_BY, binary_BY0 = [BY[i] for i in binary], [BY0[i] for i in binary]
    require_equal('Binary feedback unchanged', binary_BY, binary_BY0)
    matrices = dict(Z=Z, D_Z=DZ, eta=eta, z0=z0, Y=Y, Y0=Y0,
                    B_Y=BY, B_Y0=BY0, seed_feedback_correction=correction,
                    binary_B_Y=binary_BY, binary_B_Y0=binary_BY0)
    record['incoming'] = dict(
        certificates={name: incoming.matrix_certificate(matrix) for name, matrix in matrices.items()},
        gamma_transpose_D_Z=gamma_DZ,
        eta_equals_inverse_DS_times_DZ_verified=True, D_z0_zero_verified=True,
        actual_O_Y0_equals_z0_verified=True, feedback_decomposition_verified=True,
        binary_feedback_equal_entrywise=True,
        normalization='Z is incoming_coefficients H5 with its actual A_t(A,B) column factors and X0 factor; no column rescaling.')


def check_case(m, record, started):
    case_started = time.monotonic()
    times = sparse.factors(m, 'economic')
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    record.update(m=m, time_fixture='economic', prime=P, G=G, old_time_factors=times,
                  geometry=check_geometry(m, A))
    D, lines, pair_labels = difference_operator(m, A)
    D_axis, _, _ = difference_operator(m, A, axis_scale=11)
    D_cross, _, _ = difference_operator(m, A, cross_scale=7)
    require_equal('Axis representative invariance', D_axis, D)
    require_equal('Pair representative covariance', [[49 * x % P for x in row] for row in D_cross], D)
    O, old_geometry = residue.residue_matrix(m + 2, A, P)
    B, J, T = incoming.feedback_limit(m, A)
    output_labels = [(t, a, d) for t, a in lines for d in range(3)]
    T0, T1, T2 = ([T[3 * i + d] for i in range(len(lines))] for d in range(3))
    require_equal('T_output1 = T_output2', T1, T2)
    DO = schur.matrix_product(D, O)
    require_equal('D O = T_output0 - T_output1', DO, schur.matrix_difference(T0, T1))

    C, E_coefficients, seed_labels, constants = seed_coefficients(m, A)
    assert seed_labels == lines
    S = schur.matrix_product(O, C)
    # E has rho(E)=0, but J(E)=T(E)=-1 at every output of its own line.
    gauge_T = [[-int((t, a) == line) % P for line in lines] for t, a, _ in output_labels]
    gauge_correction = schur.matrix_product(gauge_T, E_coefficients)
    JU = matrix_sum(schur.matrix_product(J, C), gauge_correction)
    TU = matrix_sum(schur.matrix_product(T, C), gauge_correction)
    BU = schur.matrix_product(B, C)
    require_equal('B U = J U - T U', BU, schur.matrix_difference(JU, TU))
    expected_JU = [[int((t, a) == line and d == 0) for line in lines] for t, a, d in output_labels]
    require_equal('Extended seed incidence', JU, expected_JU)
    assert all(TU[i] == [0] * len(lines) for i, (_, _, d) in enumerate(output_labels) if d in (1, 2))
    e = [int(line == (2, 0)) for line in lines]
    gamma = BU[output_labels.index((2, 0, 0))]
    assert all(value == 0 for (t, a), value in zip(lines, gamma) if t != m + 1 or a == 0)
    require_equal('Seed feedback support', BU, outer([int(label == (2, 0, 0)) for label in output_labels], gamma))
    assert residue.dot(gamma, e, P) == 0
    egamma = outer(e, gamma)
    DS = schur.matrix_product(D, S)
    require_equal('D S = I - e gamma^T', DS, schur.matrix_difference(identity(len(lines)), egamma))
    inverse_DS = matrix_sum(identity(len(lines)), egamma)
    require_equal('Right inverse of D S', schur.matrix_product(DS, inverse_DS), identity(len(lines)))
    require_equal('Left inverse of D S', schur.matrix_product(inverse_DS, DS), identity(len(lines)))
    full_T = [row + gauge for row, gauge in zip(T, gauge_T)]
    certificates = {name: incoming.matrix_certificate(matrix) for name, matrix in dict(
        D=D, D_O=DO, seed_coefficients=C, seed_pair_vectors=S, D_S=DS,
        extended_seed_J=JU, extended_seed_T=TU, seed_B=BU,
        old_pair_source_T=T, local_E_gauge_T=gauge_T, full_old_moment_T=full_T).items()}
    assert certificates['D']['rank_certificate']['rank'] == 3 * m
    assert certificates['seed_pair_vectors']['rank_certificate']['rank'] == 3 * m
    assert certificates['full_old_moment_T']['rank_certificate']['rank'] == 6 * m
    actual_surviving = [gamma[lines.index((m + 1, a))] for a in range(3)]
    closed_check = auxiliary.surviving_entry_formula(m, times, A, actual_surviving)
    record.update(old_cross_geometry=old_geometry, line_and_seed_labels=lines,
                  pair_coordinate_labels=pair_labels, axis_output_labels=output_labels,
                  H4_seed_constants=constants, certificates=certificates,
                  old_source_matrix_sha256=residue.matrix_hash(O),
                  D_S_matrix=DS, inverse_D_S_matrix=inverse_DS, e=e, gamma=gamma,
                  exact_nonzero_gamma=[dict(seed=label, value=value) for label, value in zip(lines, gamma) if value],
                  U4_U5_gamma_check=closed_check,
                  identities_verified=dict(D_O_equals_T0_minus_T1=True, T1_equals_T2=True,
                      extended_seed_J_is_output0_incidence=True, extended_seed_binary_T_zero=True,
                      seed_B_equals_e_output_gamma_transpose=True,
                      D_S_equals_I_minus_e_gamma_transpose=True, gamma_transpose_e_zero=True,
                      inverse_D_S_equals_I_plus_e_gamma_transpose=True,
                      axis_projective_representative_invariant=True,
                      pair_coordinate_projective_covariance=True),
                  E_convention='rho(E)=0; J(E)=T(E)=-1 in all three outputs of its matching line; B(E)=0.',
                  seed_core_seconds=time.monotonic() - case_started)
    print(json.dumps(dict(m=m, stage='seed', D_rank=3*m, seed_rank=3*m, full_old_moment_T_rank=6*m,
                          nonzero_gamma=record['exact_nonzero_gamma'], seconds=record['seed_core_seconds'])), flush=True)
    if time.monotonic() - started < 21:
        check_incoming(m, A, O, D, S, C, gamma, inverse_DS, B, output_labels, record)
        if 'incoming' in record:
            ranks = {name: cert['rank_certificate']['rank'] for name, cert in record['incoming']['certificates'].items()}
            print(json.dumps(dict(m=m, stage='incoming', ranks=ranks)), flush=True)
    else:
        record['incoming_limitation'] = 'Skipped optional incoming solve to preserve the 28-second process bound.'
    record['elapsed_seconds'] = time.monotonic() - case_started


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second residue-differences cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024**2:
            raise TimeoutError('95MiB residue-differences RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for m in (3, 5):
            cases.append(dict(m=m))
            check_case(m, cases[-1], started)
    except TimeoutError as error:
        cases[-1]['bounded_limitation'] = str(error)
        print(json.dumps(dict(m=cases[-1]['m'], limitation=str(error))), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='External exact finite-field residue-difference and seed-decomposition diagnostic; no uniform theorem.',
                  prime=P, formulas='R3/R5 construct D directly; actual O and T check R6; auxiliary U gives R10/R11; actual OY=Z gives R12/R16.',
                  limitations='These two economic fixtures do not prove generic or all-length independence. Modular deficiencies are not real rank upper bounds; the recorded nonzero minors lift after denominator clearing.',
                  elapsed_seconds=time.monotonic() - started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(), cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
