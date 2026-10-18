#!/usr/bin/env python3
"""Bounded exact checks of the candidate even-length polar correction E1--E15.

The candidate pencil is constructed with first-order dual arithmetic in
delta. Its binary kernel and cokernel determine Gamma, theta, ell, kappa.
The corrected incoming matrix is evaluated on actual old pair residues,
then mapped through the verified actual solve OY=Z.

An independent calculation constructs the physical shared/incoming polar
source blocks at the actual old--new intersections, using the existing
precision-tracked Laurent arithmetic. It solves those blocks without the
candidate pencil and compares every physical lambda0 entry. This is an
independent check of E8, not an independent computation of all of E14.

Reproduce:
  nice -n 19 python3 exploration/source24_even_correction.py --output exploration/source24-even-correction-results.json
"""

import argparse
from contextlib import contextmanager
import itertools as it
import json
from pathlib import Path
import signal
import time

import absorbing_firstjet as dual
import shared_new_polar_firstjet as polar
import source24_odd_incoming as incoming
import source24_regular_laurent as laurent


P = incoming.P
G = ((1, 2, 3), (1, 5, 7), (1, 11, 13))
TIMES = ((1, 2), (3, 5), (7, 17), (13, 43))
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
multiply, subtract = schur.matrix_product, schur.matrix_difference
ZERO, ONE = dual.ZERO, dual.ONE


@contextmanager
def fixture_context():
    """Restore module globals and inverse caches even if a guard interrupts."""
    old_incoming_G, old_laurent_G = incoming.G, laurent.G
    old_precision = laurent.RELATIVE_PRECISION
    incoming.G = laurent.G = G
    laurent.RELATIVE_PRECISION = 6
    laurent.inverse_series.cache_clear()
    try:
        with polar.transition_fixture(G):
            yield
    finally:
        incoming.G, laurent.G = old_incoming_G, old_laurent_G
        laurent.RELATIVE_PRECISION = old_precision
        laurent.inverse_series.cache_clear()


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def zero_matrix(rows, columns):
    return [[0] * columns for _ in range(rows)]


def require_equal(name, actual, expected):
    assert len(actual) == len(expected)
    for i, (row, target) in enumerate(zip(actual, expected)):
        assert len(row) == len(target)
        for j, (x, y) in enumerate(zip(row, target)):
            if (x - y) % P:
                raise AssertionError(f'{name}: entry({i},{j}) is {x % P}, expected {y % P}.')


def comparison(actual, expected):
    assert len(actual) == len(expected) and len(actual[0]) == len(expected[0])
    mismatches = [(i, j, x, y) for i, (row, target) in enumerate(zip(actual, expected))
                  for j, (x, y) in enumerate(zip(row, target)) if x != y]
    return dict(equal_entrywise=not mismatches, mismatched_entries=len(mismatches),
                first_mismatch=None if not mismatches else dict(
                    row=mismatches[0][0], column=mismatches[0][1],
                    actual=mismatches[0][2], candidate=mismatches[0][3]))


def dual_word(matrices, word):
    answer = dual.identity()
    for block in word:
        answer = dual.mmul(answer, matrices[block])
    return answer


def candidate_pencil(tables):
    """E1--E5, including the exact moving point and all kernel derivatives."""
    m = len(tables)
    labels = [(u, 0) for u in range(m)] + [(u, c) for u in range(m) for c in (1, 2)]
    M0, Mdot, constant_formula_checks, diagonal = [], [], 0, []
    for u, c in labels:
        a, b = tables[u][c][1:]
        z = -a * pow(b, -1, P) % P
        X = ((0, -1 % P), ONE, (z, pow(b, -1, P)))
        kernels = polar.matrices_at_pole(tables, X, u, c)
        sigma = ((-1 % P, 0), ONE, X[2])
        values = []
        for s, state in labels:
            word = [s] + [j for j in range(m) if j != s]
            product = dual_word(kernels, word)
            values.append(dual.mul(sigma[state], product[state][2]))
            position = word.index(u)
            prefix = dual_word(kernels, word[:position])
            suffix_determinant = 1
            for j in word[position + 1:]:
                K = kernels[j]
                suffix_determinant = suffix_determinant * (K[1][1][0] * K[2][2][0]
                                                          - K[1][2][0] * K[2][1][0]) % P
            assert product[state][2][0] == -a * suffix_determinant * prefix[state][c][0] % P
            constant_formula_checks += 1
        M0.append([value[0] for value in values])
        Mdot.append([value[1] for value in values])
        if c == 0:
            value = a % P
            for j in range(m):
                if j != u:
                    K = kernels[j]
                    value = value * (K[1][1][0] * K[2][2][0] - K[1][2][0] * K[2][1][0]) % P
            diagonal.append(value)
    D = [row[:m] for row in M0[:m]]
    C = [row[:m] for row in M0[m:]]
    M = [row[m:] for row in M0[m:]]
    E = [row[m:] for row in Mdot[:m]]
    M1 = [row[m:] for row in Mdot[m:]]
    assert all(diagonal)
    require_equal('E4 top-right zero', [row[m:] for row in M0[:m]], zero_matrix(m, 2*m))
    require_equal('E5 diagonal D', D, [[diagonal[i] * int(i == j) % P for j in range(m)] for i in range(m)])
    Dinv = [[pow(diagonal[i], -1, P) * int(i == j) % P for j in range(m)] for i in range(m)]
    pivots, free, right_vectors = dual.rref_kernel(M)
    left_pivots, left_free, left_vectors = dual.rref_kernel(transpose(M))
    assert len(pivots) == len(left_pivots) == 2*m - 2 and len(free) == len(left_free) == 2
    R, L = transpose(right_vectors), left_vectors
    require_equal('M R = 0', multiply(M, R), zero_matrix(2*m, 2))
    require_equal('L M = 0', multiply(L, M), zero_matrix(2, 2*m))
    Omega = subtract(M1, multiply(C, multiply(Dinv, E)))
    Gamma = multiply(L, multiply(Omega, R))
    inverse_result = schur.invert(Gamma)
    assert inverse_result is not None, 'Candidate Gamma is singular at this fixture.'
    Gamma_inverse, Gamma_inverse_certificate = inverse_result
    return dict(labels=labels, M0=M0, Mdot=Mdot, D=D, Dinv=Dinv, C=C, M=M, E=E, M1=M1,
                R=R, L=L, Omega=Omega, Gamma=Gamma, Gamma_inverse=Gamma_inverse,
                Gamma_inverse_certificate=Gamma_inverse_certificate,
                right_free_columns=free, left_free_columns=left_free,
                E5_entries_verified=constant_formula_checks)


def candidate_rhs_and_coefficients(tables, pencil):
    """E6/E7; compute the RHS separately from the H4 constants."""
    m = len(tables)
    columns = [(t, a) for t in range(m) for a in range(3)]
    q = []
    for u, c in pencil['labels']:
        z = -tables[u][c][1] * pow(tables[u][c][2], -1, P) % P
        X = (0, 1, z)
        residue_row = [tables[u][c][d] * X[d] % P for d in range(3)]
        kernels = {j: ([residue_row[:] if a == c else [0]*3 for a in range(3)] if j == u
                       else residue.ordinary_kernel(tables, j, X, P)) for j in range(m)}
        omitted = {t: residue.word_product(kernels, [j for j in range(m) if j != t], P)
                   for t in range(m)}
        row = []
        for t, a in columns:
            if a == 0 or (t == u and a != c):
                row.append(0)
                continue
            value = X[a] * (omitted[t][1][2] - omitted[t][0][2]) % P
            if t != u:
                value = value * pow(residue.dot(tables[t][a], X, P), -1, P) % P
            row.append(value)
        q.append(row)
    cvec = zero_matrix(m, 3*m)
    constants = []
    for j, (t, a) in enumerate(columns):
        r = min(s for s in range(m) if s != t)
        X = (0, 1, -tables[r][0][1] * pow(tables[r][0][2], -1, P) % P)
        K = residue.ordinary_kernel(tables, t, X, P)
        determinant = (K[1][1]*K[2][2] - K[1][2]*K[2][1]) % P
        assert determinant
        c = X[a] * pow(residue.dot(tables[t][a], X, P) * determinant % P, -1, P) % P if a else 0
        cvec[r][j] = c
        constants.append(dict(t=t+2, A=a, first_old_block=r+2, c_tA=c))
    q0, qbin = q[:m], q[m:]
    require_equal('E7 q0 = D cvec', q0, multiply(pencil['D'], cvec))
    theta = multiply(pencil['Gamma_inverse'], multiply(pencil['L'], subtract(qbin, multiply(pencil['C'], cvec))))
    kappa = multiply(pencil['R'], theta)
    J = multiply(pencil['Dinv'], multiply(pencil['E'], pencil['R']))
    ell = subtract(cvec, multiply(J, theta))
    require_equal('M kappa = 0', multiply(pencil['M'], kappa), zero_matrix(2*m, 3*m))
    require_equal('D ell + E kappa = q0', subtract(q0, multiply(pencil['D'], ell)), multiply(pencil['E'], kappa))
    residual = subtract(subtract(qbin, multiply(pencil['C'], ell)), multiply(pencil['M1'], kappa))
    require_equal('Projected first-order equation', multiply(pencil['L'], residual), zero_matrix(2, 3*m))
    assert all(ell[i][3*t] == 0 for i in range(m) for t in range(m))
    assert all(kappa[i][3*t] == 0 for i in range(2*m) for t in range(m))
    return dict(columns=columns, q=q, cvec=cvec, constants=constants, theta=theta,
                kappa=kappa, ell=ell, J=J)


def physical_lambda_prediction(A, coefficients, m):
    shared = [(s, h, b) for s in range(m) for h in range(3) for b in range(3)]
    incoming_labels = [(t, a, B) for t in range(m) for a in range(3) for B in range(3)]
    values = []
    for s, h, b in shared:
        row = []
        for t, a, B in incoming_labels:
            scalar = coefficients['ell'][s][3*t+a] if b == 0 else coefficients['kappa'][2*s+b-1][3*t+a]
            row.append(A[t+2][a][B] * scalar % P if h == B else 0)
        values.append(row)
    return values, shared, incoming_labels


def direct_even_residues(m, A, pencil, coefficients):
    """E14/E15 on the actual pair points and their actual two-vector coordinates."""
    old = list(range(2, m+2))
    G_inverse, _ = schur.invert([list(row) for row in G])
    w = G_inverse[2]
    Z, correction_basis = [], []
    for u, v in it.combinations(old, 2):
        for cu, cv in it.product(range(3), repeat=2):
            X = residue.cross(A[u][cu], A[v][cv], P)
            assert all(X)
            assert {(t,a) for t in old for a in range(3) if residue.dot(A[t][a],X,P)==0} == {(u,cu),(v,cv)}
            U = [A[u][cu][i]*X[i] % P for i in range(3)]
            V = [A[v][cv][i]*X[i] % P for i in range(3)]
            wa, wb = residue.coordinates(w, U, V, P)
            kernels = {t: ([U[:] if a==cu else [0]*3 for a in range(3)] if t==u else
                           [V[:] if a==cv else [0]*3 for a in range(3)] if t==v else
                           residue.ordinary_kernel(A,t,X,P)) for t in old}
            omitted = {t: residue.word_product(kernels,[j for j in old if j!=t],P)[0][2] for t in old}
            moved = {s: residue.word_product(kernels,residue.ordered_word(old,s),P) for s in old}
            phi = [(sum(pencil['R'][2*(s-2)+b-1][j]*X[b]*moved[s][b][2]
                         for s in old for b in (1,2))
                    - X[0]*sum(coefficients['J'][s-2][j]*moved[s][0][2] for s in old)) % P for j in range(2)]
            phi_scalars = [X[B] * pow(X[2],-1,P) * phi[j] % P for B in range(3) for j in range(2)]
            correction_basis.extend(([value*wa % P for value in phi_scalars],
                                     [value*wb % P for value in phi_scalars]))
            values = []
            for t in old:
                for a in range(3):
                    col = 3*(t-2)+a
                    if (t==u and a!=cu) or (t==v and a!=cv):
                        first = 0
                    else:
                        first = -X[a]*X[0]*omitted[t] % P
                        if t not in (u,v):
                            first = first*pow(residue.dot(A[t][a],X,P),-1,P) % P
                    ell_part = X[0]*sum(coefficients['ell'][s-2][col]*moved[s][0][2] for s in old)
                    kappa_part = sum(coefficients['kappa'][2*(s-2)+b-1][col]*X[b]*moved[s][b][2]
                                     for s in old for b in (1,2))
                    for B in range(3):
                        values.append(A[t][a][B]*X[B]*pow(X[2],-1,P)*(first+ell_part+kappa_part) % P)
            Z.extend(([value*wa % P for value in values], [value*wb % P for value in values]))
    correction_coefficients = []
    for B in range(3):
        for j in range(2):
            correction_coefficients.append([A[t+2][a][b]*coefficients['theta'][j][3*t+a] % P if b==B else 0
                                            for t in range(m) for a in range(3) for b in range(3)])
    return Z, correction_basis, correction_coefficients


def physical_polar_check(m, A, candidate, shared_labels, record):
    """Independent original-source polar solve, without E1--E9 or candidate q.

    Only the small sectors of the actual polar block are evaluated. Their
    construction uses full old--new cross points, both vector residues,
    original shared/incoming source formulas, and Laurent normalization.
    """
    started = time.monotonic()
    old, epsilon = list(range(2,m+2)), laurent.monomial(1)
    AN = [[laurent.Laurent.cast(1), row[1]*epsilon, row[2]*laurent.monomial(3)] for row in G]
    physical = zero_matrix(9*m, 9*m)
    sector_records = []
    row_index = {label:i for i,label in enumerate(shared_labels)}
    for h in range(3):
        Pnorm, Q = [], []
        for u in old:
            for c in range(3):
                X = residue.cross(A[u][c], AN[h], P)
                U = [A[u][c][i]*X[i] for i in range(3)]
                V = [AN[h][i]*X[i] for i in range(3)]
                kernels = {t: ([U[:] if a==c else [0]*3 for a in range(3)] if t==u
                               else residue.ordinary_kernel(A,t,X,P)) for t in old}
                moved = {s:residue.word_product(kernels,residue.ordered_word(old,s),P) for s in old}
                omitted = {t:residue.word_product(kernels,[j for j in old if j!=t],P) for t in old}
                shared_row, incoming_row = [], []
                for s in old:
                    for b in range(3):
                        vector = [-X[h]*X[b]*value for value in moved[s][b]]
                        alpha, _ = residue.coordinates(vector,U,V,P)
                        shared_row.append(alpha*laurent.monomial(-int(h==0)-int(b==0)))
                for t in old:
                    new_then_omitted = residue.matmul([V],omitted[t],P)[0]
                    for a in range(3):
                        if t==u and a!=c:
                            incoming_row.append(laurent.Laurent())
                            continue
                        scalar = -X[a]*A[t][a][h]*X[h]
                        if t!=u:
                            scalar = scalar*pow(residue.dot(A[t][a],X,P),-1,P)
                        alpha, _ = residue.coordinates([scalar*x for x in new_then_omitted],U,V,P)
                        incoming_row.append(alpha)
                Pnorm.append(shared_row)
                Q.append(incoming_row)
        Pinverse, inverse_certificate = laurent.polar_inverse(Pnorm)
        solved = multiply(Pinverse,Q)
        residual = subtract(multiply(Pnorm,solved),Q)
        assert all(not laurent.Laurent.cast(x).terms for row in residual for x in row)
        assert laurent.minimum_precision(residual)>0
        physical_sector = [[x*laurent.monomial(-int(h==0)-int(b==0)) for x in solved[3*s+b]]
                           for s in range(m) for b in range(3)]
        assert all(x.valuation>=0 and x.precision>0 for row in physical_sector for x in row)
        for s in range(m):
            for b in range(3):
                target = physical[row_index[s,h,b]]
                for t in range(m):
                    for a in range(3):
                        target[9*t+3*a+h] = physical_sector[3*s+b][3*t+a].coefficient(0)
        sector_records.append(dict(new_line_state=h, polar_inverse=inverse_certificate,
                                   physical_lambda_minimum_precision=laurent.minimum_precision(physical_sector),
                                   original_polar_equation_verified_through_known_cutoff=True))
    record.update(independent_physical_lambda=comparison(physical,candidate),
                  physical_lambda0=incoming.matrix_certificate(physical), physical_sectors=sector_records,
                  physical_check_seconds=time.monotonic()-started,
                  independent_check_scope='Original source polar residues at full old-new intersections, separate Laurent solve and physical normalization; all lambda0 entries compared. E14 Z is not independently reconstructed by a full regular Laurent solve.')


def check_case(m, record, process_started):
    started = time.monotonic()
    times = TIMES[:m]
    tables = sparse.coefficient_tables(G,times)
    A = [[list(row) for row in G] for _ in range(2)] + tables
    pencil = candidate_pencil(tables)
    coefficients = candidate_rhs_and_coefficients(tables,pencil)
    candidate_lambda, shared_labels, incoming_labels = physical_lambda_prediction(A,coefficients,m)
    Z, correction_basis, correction_coefficients = direct_even_residues(m,A,pencil,coefficients)
    sparse_Z, _, _ = incoming.incoming_coefficients(m,A)
    correction = subtract(Z,sparse_Z)
    require_equal('E15 six-column correction',correction,multiply(correction_basis,correction_coefficients))
    O, geometry = residue.residue_matrix(m+2,A,P)
    B, _, _ = incoming.feedback_limit(m,A)
    Y, solve = incoming.solve_old_source(O,Z)
    assert Y is not None, 'Actual old source is singular at this fixture.'
    mapped = multiply(B,Y)
    matrices = dict(O=O,B=B,M=pencil['M'],Gamma=pencil['Gamma'],q=coefficients['q'],
                    theta=coefficients['theta'],ell=coefficients['ell'],kappa=coefficients['kappa'],
                    lambda0=candidate_lambda,Z_even=Z,Z_sparse=sparse_Z,correction=correction,
                    correction_basis=correction_basis,correction_coefficients=correction_coefficients,
                    actual_OinvZ=Y,mapped_B_OinvZ=mapped)
    certificates = {name:incoming.matrix_certificate(matrix) for name,matrix in matrices.items()}
    expected = dict(O=18 if m==2 else 108,B=14 if m==2 else 36,
                    Z_even=7 if m==2 else 36,mapped_B_OinvZ=6 if m==2 else 36,correction=6,Gamma=2)
    observed = {name:certificates[name]['rank_certificate']['rank'] for name in expected}
    record.update(m=m,prime=P,G=G,old_time_factors=times,geometry=geometry,
                  expected_external_ranks=expected,observed_ranks=observed,external_ranks_reproduced=(expected==observed),
                  certificates=certificates,actual_old_source_solve=solve,
                  pencil_row_column_labels=[(t+2,a) for t,a in pencil['labels']],
                  incoming_labels=[(t+2,a,b) for t,a,b in incoming_labels],
                  shared_lambda_labels=[(s+2,h,b) for s,h,b in shared_labels],
                  right_kernel=pencil['R'],left_kernel=pencil['L'],Gamma=pencil['Gamma'],
                  Gamma_inverse=pencil['Gamma_inverse'],Gamma_inverse_certificate=pencil['Gamma_inverse_certificate'],
                  right_kernel_free_columns=pencil['right_free_columns'],left_kernel_free_columns=pencil['left_free_columns'],
                  H4_constants=coefficients['constants'],theta=coefficients['theta'],ell=coefficients['ell'],kappa=coefficients['kappa'],
                  identities_verified=dict(E4_constant_block_form=True,E5_constant_residue_entries=pencil['E5_entries_verified'],
                      binary_right_and_left_kernel_equations=True,q0_equals_D_cvec=True,
                      M_kappa_zero=True,D_ell_plus_E_kappa_equals_q0=True,
                      projected_first_order_equation=True,physical_constant_for_A0_is_zero=True,
                      E15_exact_six_column_correction=True,actual_O_Y_equals_Z=True),
                  core_seconds=time.monotonic()-started)
    print(json.dumps(dict(m=m,stage='candidate',ranks=observed,external_ranks_reproduced=expected==observed,
                          seconds=record['core_seconds'])),flush=True)
    if time.monotonic()-process_started<17:
        try:
            physical_polar_check(m,A,candidate_lambda,shared_labels,record)
        except laurent.PrecisionFailure as error:
            record['physical_check_limitation']=str(error)
        print(json.dumps(dict(m=m,stage='physical',comparison=record.get('independent_physical_lambda'),
                              limitation=record.get('physical_check_limitation'),
                              seconds=record.get('physical_check_seconds'))),flush=True)
    else:
        record['physical_check_limitation']='Skipped to preserve the 28-second process bound.'
    record['elapsed_seconds']=time.monotonic()-started


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    started,cases=time.monotonic(),[]

    def guard(_signal,_frame):
        if time.monotonic()-started>=28:
            raise TimeoutError('28-second even-correction cutoff.')
        if incoming.maximum_rss_bytes()>=95*1024**2:
            raise TimeoutError('95MiB even-correction RSS guard.')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        with fixture_context():
            for m in (2,4):
                cases.append(dict(m=m))
                check_case(m,cases[-1],started)
    except TimeoutError as error:
        cases[-1]['bounded_limitation']=str(error)
        print(json.dumps(dict(m=cases[-1]['m'],limitation=str(error))),flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result=dict(status='Locally implemented exact finite-field checks of the even-correction candidate; no general theorem.',
                formulas='E1-E7 dual pencil; E8 physical lambda0; E14 actual pair-coordinate incoming; E15 six-column difference; actual OY=Z and B mapping.',
                independent_check='Physical polar sectors are built from the original source residues at actual old-new points and solved with separate precision-tracked Laurent arithmetic. No downloaded code is used.',
                limitations='Only two finite fixtures. No all-even-m independence or transversality statement. Modular rank deficiencies are not real rank upper bounds; nonzero minors lift after denominator clearing. E16 is not tested.',
                elapsed_seconds=time.monotonic()-started,maximum_rss_bytes=incoming.maximum_rss_bytes(),cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
