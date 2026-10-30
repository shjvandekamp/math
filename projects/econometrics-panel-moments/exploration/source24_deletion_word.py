#!/usr/bin/env python3
"""Bounded exact modular exploration of the H17 deletion-word family.

R=ell(X)*P[0,2]-sum_(t,A) q_tA(X)*X_A/L_tA*P_omit_t[0,2],
where all words are ascending and ell and each q are arbitrary linear
forms. Observations are scalar cross-block double residues. Kernel
vectors therefore give relations modulo these observations, not
automatically rational-function zero identities.

Run:
  nice -n 19 python3 exploration/source24_deletion_word.py --output exploration/source24-deletion-word-results.json
"""

import argparse
import json
from pathlib import Path
import resource
import signal
import sys
import time

import absorbing_firstjet as dual
import normalized_sparse_source24 as sparse
import source24_residue as residue
import source24_schur as schur


P, G = residue.PRIME, schur.G


def labels(k):
    return [('ell', j) for j in range(3)] + [
        ('q', t, a, j) for t in range(2, k + 2) for a in range(3) for j in range(3)]


def coefficient_values(k, A, X, poles=None):
    """Ordinary values or residues after replacing each pole kernel row."""
    old = list(range(2, k + 2))
    poles = {} if poles is None else poles
    kernels = {}
    for t in old:
        if t in poles:
            a = poles[t]
            row = [A[t][a][i] * X[i] % P for i in range(3)]
            kernels[t] = [row[:] if b == a else [0, 0, 0] for b in range(3)]
        else:
            kernels[t] = residue.ordinary_kernel(A, t, X, P)
    common = residue.word_product(kernels, old, P)[0][2]
    omitted = {t: residue.word_product(kernels, [s for s in old if s != t], P)[0][2] for t in old}
    answer = [X[j] * common % P for j in range(3)]
    for t in old:
        for a in range(3):
            if t in poles and a != poles[t]:
                scalar = 0
            else:
                scalar = -X[a] * omitted[t] % P
                if t not in poles:
                    scalar = scalar * pow(residue.dot(A[t][a], X, P), -1, P) % P
            answer.extend(scalar * X[j] % P for j in range(3))
    return answer


def deletion_matrix(k, A):
    old = list(range(2, k + 2))
    matrix, row_labels = [], []
    for u in old:
        for v in old:
            if u >= v:
                continue
            for c in range(3):
                for d in range(3):
                    X = residue.cross(A[u][c], A[v][d], P)
                    assert all(X)
                    actual_poles = {(t, a) for t in old for a in range(3) if residue.dot(A[t][a], X, P) == 0}
                    assert actual_poles == {(u, c), (v, d)}
                    matrix.append(coefficient_values(k, A, X, {u: c, v: d}))
                    row_labels.append((u, v, c, d))
    assert len(matrix) == 9 * k * (k - 1) // 2
    assert all(len(row) == 9 * k + 3 for row in matrix)
    return matrix, row_labels


def evaluate_kernel_functions(k, A, kernel):
    points = [(1, 2, 3), (2, 3, 5), (3, 5, 7)]
    values = []
    for X in points:
        assert all(residue.dot(A[t][a], X, P) for t in range(2, k + 2) for a in range(3))
        row = coefficient_values(k, A, X)
        values.append([sum(x * y for x, y in zip(row, vector)) % P for vector in kernel])
    return points, values


def proportional_linear_form(form, denominator):
    factor = form[0] * pow(denominator[0], -1, P) % P
    return all((x - factor * y) % P == 0 for x, y in zip(form, denominator))


def collapse_derivative_diagnostic():
    """Fixed-tail residue first jets after the supplied four-pivot reduction."""
    k, ustar, vstar = 4, 2, 3
    times = sparse.factors(5, 'economic')[1:]
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    leading, row_labels = deletion_matrix(k, A)
    jets = []
    for u, v, c, d in row_labels:
        X = residue.cross(A[u][c], A[v][d], P)
        kernels = {}
        for t in range(2, k + 2):
            if t in (u, v):
                state = c if t == u else d
                vector = [A[t][state][j] * X[j] % P for j in range(3)]
                kernels[t] = [vector[:] if a == state else [0, 0, 0] for a in range(3)]
            else:
                kernels[t] = residue.ordinary_kernel(A, t, X, P)
        product = residue.word_product(kernels, list(range(2, k + 2)), P)
        h = [0, G[0][1] * ustar * X[1] % P, G[0][2] * vstar * X[2] % P]
        linear = sum(h) % P
        hP = sum(h[j] * product[j][2] for j in range(3)) % P
        P02 = product[0][2]
        inverse_X0 = pow(X[0], -1, P)
        row = []
        for q10, alpha in ((X[0], 0), (X[1], 0), (X[2], 0), (0, X[1]), (0, X[2])):
            expected = ((q10 + alpha) * hP - alpha * linear * P02) * inverse_X0 % P
            # Exact dual form of the reduced original five-block family:
            # ell*e0*K_first*Ptail - q10*X0/L10*Ptail02 - alpha*Ptail02.
            inverse_L10 = dual.inverse((X[0], linear))
            common = dual.mul((X[0] * P02 % P, hP), inverse_L10)
            deleted_first = dual.mul((q10 * X[0] * P02 % P, 0), inverse_L10)
            actual = dual.sub(dual.sub(dual.scale(q10 + alpha, common), deleted_first),
                              (alpha * P02 % P, 0))
            assert actual == (0, expected)
            row.append(expected)
        assert row[0] == hP
        jets.append(row)
    single = [row + [extra[0]] for row, extra in zip(leading, jets)]
    full = [row + extra for row, extra in zip(leading, jets)]
    return dict(original_block_count=5, tail_block_count=k, prime=P, G=G,
                tail_time_factors=times, collapsed_first_block_direction=[ustar, vstar],
                tail_reindexing='Original five-block positions 2,...,5 (residue IDs 3,...,6) are reindexed as residue IDs 2,...,5.',
                leading_tail_columns=labels(k), tail_residue_rows=row_labels,
                kernel_column_order=['q10=X0', 'q10=X1', 'q10=X2', 'a=1', 'b=1'],
                kernel_definition='q_tail=0; ell=q10+a*X1+b*X2; q11=a*L11; q12=b*L12.',
                derivative_formula='[(q10+a*X1+b*X2)*h-(a*X1+b*X2)*l*e0]*Ptail/X0, h=(0,G01*ustar*X1,G02*vstar*X2), l=h1+h2.',
                leading_tail_rank_certificate=residue.modular_rank(leading, P),
                leading_plus_hP_rank_certificate=residue.modular_rank(single, P),
                leading_plus_five_jets_rank_certificate=residue.modular_rank(full, P),
                leading_tail_sha256=residue.matrix_hash(leading),
                leading_plus_hP_sha256=residue.matrix_hash(single),
                leading_plus_five_jets_sha256=residue.matrix_hash(full),
                derivative_columns_sha256=residue.matrix_hash(jets),
                exact_dual_derivative_and_zero_constant_terms_verified=True,
                priority_q10_X0_column_equals_hP_verified=True,
                scope='Finite first-jet test on fixed old-tail residue rows after the stated four-pivot reduction. Moving first-block pole rows and the full reduction are not certified by this diagnostic.')


def check_case(k, mode):
    started = time.monotonic()
    times = sparse.factors(k, mode)
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    matrix, row_labels = deletion_matrix(k, A)
    certificate = residue.modular_rank(matrix, P)
    pivots, free, kernel = dual.rref_kernel(matrix)
    assert len(pivots) == certificate['rank']
    points, evaluations = evaluate_kernel_functions(k, A, kernel)
    descriptions = []
    for index, vector in enumerate(kernel):
        proportional, nonzero_forms, active_blocks = [], [], []
        for t in range(2, k + 2):
            active = False
            for a in range(3):
                offset = 3 + 9 * (t - 2) + 3 * a
                form = vector[offset:offset + 3]
                if any(form):
                    active = True
                    nonzero_forms.append((t, a))
                    if proportional_linear_form(form, A[t][a]):
                        proportional.append((t, a))
            if active:
                active_blocks.append(t)
        descriptions.append(dict(free_column=free[index],
                                 nonzero_coefficients=[(j, x) for j, x in enumerate(vector) if x],
                                 ell_coefficients=vector[:3], active_q_blocks=active_blocks,
                                 nonzero_q_forms=nonzero_forms,
                                 q_forms_proportional_to_their_denominator=proportional,
                                 known_nonzero_as_rational_function=any(row[index] for row in evaluations)))
    # Restrict to q_tA proportional to L_tA, the shared-pole-removal
    # subspace explicitly mentioned after H17. Its embedding is injective.
    removed = []
    for row in matrix:
        target = row[:3]
        for t in range(2, k + 2):
            for a in range(3):
                offset = 3 + 9 * (t - 2) + 3 * a
                target.append(sum(row[offset + j] * A[t][a][j] for j in range(3)) % P)
        removed.append(target)
    removed_rank = residue.modular_rank(removed, P)
    _, removed_free, removed_kernel = dual.rref_kernel(removed)
    result = dict(k=k, time_fixture=mode, prime=P, G=G, old_time_factors=times,
                  column_labels=labels(k), residue_row_labels=row_labels,
                  geometry_nonzero_coordinates_and_no_third_old_line_verified=True,
                  rank_certificate=certificate, matrix_sha256=residue.matrix_hash(matrix),
                  kernel_dimension=len(kernel), pivot_columns=pivots, free_columns=free,
                  exact_modular_kernel_verified=True, kernel_vectors=descriptions,
                  ordinary_evaluation_points=points, kernel_evaluations_by_point=evaluations,
                  evaluation_scope='A nonzero sample proves that kernel combination is a nonzero rational function. Zero at all sampled points is not an identity proof.',
                  shared_pole_removed_subspace=dict(column_order='ell basis X0,X1,X2, followed by q_tA=L_tA in (t,A) order.',
                                                    columns=3*k+3, rank_certificate=removed_rank,
                                                    kernel_dimension=len(removed_kernel), free_columns=removed_free,
                                                    kernel_vectors=removed_kernel, exact_modular_kernel_verified=True),
                  elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(k=k, time_fixture=mode, rows=len(matrix), columns=9*k+3,
                          rank=certificate['rank'], nullity=len(kernel),
                          pole_removed_rank=removed_rank['rank'], pole_removed_nullity=len(removed_kernel),
                          kernel_vectors_proved_nonzero_as_functions=sum(item['known_nonzero_as_rational_function'] for item in descriptions),
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else value * 1024


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second deletion-word cutoff reached.')
        if maximum_rss_bytes() >= 95 * 1024**2:
            raise TimeoutError('95MiB deletion-word RSS guard reached.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for k in (3, 4, 5):
            cases.append(check_case(k, 'economic'))
        deficient = [case['k'] for case in cases if case['kernel_dimension']]
        for k in deficient:
            cases.append(check_case(k, 'independent'))
        collapse = collapse_derivative_diagnostic()
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='External exact finite-field ranks and verified residue-kernel vectors; no universal rank or independence theorem.',
                  family='ell(X)*P02-sum_(t,A)q_tA(X)*X_A/L_tA*P_omit_t[0,2], with ascending words and all forms linear.',
                  observation='Scalar cross-block double residues, without an additional X0/X2 multiplier.',
                  limitations='A residue-kernel vector is a relation modulo these observations, not automatically a rational-function zero identity. Nonzero samples for every chosen kernel basis vector do not exclude a rational-zero linear combination of that basis. Modular deficiency alone is not a real upper bound.',
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=maximum_rss_bytes(), cases=cases,
                  collapse_derivative_diagnostics=[collapse])
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
