#!/usr/bin/env python3
"""Direct finite-field check of the audited odd-m incoming operator H5.

Reconstruct Z_-3 by its scalar double residues, B0 by H2, and the actual
old source residue matrix O. Solve O*Y=Z and check that equation before
forming B0*Y. No replacement of O by an unrelated basis is made.
The removable X0 factor in H2 uses a single exact dual coordinate along
an old denominator line; there is no Laurent expansion in the new time.

The m=3 control must reproduce saved Laurent-diagnostic hashes before
m=5 is attempted. An optional m=7 case runs only when the earlier cases
leave adequate time. Every process stops at 28 seconds or 95 MiB RSS.

Reproduce:
  nice -n 19 python3 exploration/source24_odd_incoming.py --max-m 7 --output exploration/source24-odd-incoming-results.json
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
import source24_regular_coordinates as regular
import source24_residue as residue
import source24_schur as schur
import shared_new_polar_firstjet as polar


P, G = residue.PRIME, schur.G
HERE = Path(__file__).resolve().parent


def incoming_coefficients(m, A, full_vector=False):
    old = list(range(2, m + 2))
    columns = [(t, a, b) for t in old for a in range(3) for b in range(3)]
    first = {t: min(s for s in old if s != t) for t in old}
    c = {}
    for t in old:
        r = first[t]
        point = [0, A[r][0][2], -A[r][0][1] % P]
        K = residue.ordinary_kernel(A, t, point, P)
        determinant = (K[1][1] * K[2][2] - K[1][2] * K[2][1]) % P
        for a in range(3):
            c[t, a] = point[a] * pow(residue.dot(A[t][a], point, P) * determinant % P, -1, P) % P if a else 0
    G_inverse, _ = schur.invert([list(row) for row in G])
    w = G_inverse[2]
    Z, vectors = [], []
    for u in old:
        for v in old:
            if u >= v:
                continue
            for cu in range(3):
                for cv in range(3):
                    X = residue.cross(A[u][cu], A[v][cv], P)
                    assert all(X)
                    poles = {(t, a) for t in old for a in range(3) if residue.dot(A[t][a], X, P) == 0}
                    assert poles == {(u, cu), (v, cv)}
                    U = [A[u][cu][i] * X[i] % P for i in range(3)]
                    V = [A[v][cv][i] * X[i] % P for i in range(3)]
                    wa, wb = residue.coordinates(w, U, V, P)
                    kernels = {}
                    for k in old:
                        if k == u:
                            kernels[k] = [U[:] if a == cu else [0, 0, 0] for a in range(3)]
                        elif k == v:
                            kernels[k] = [V[:] if a == cv else [0, 0, 0] for a in range(3)]
                        else:
                            kernels[k] = residue.ordinary_kernel(A, k, X, P)
                    omitted = {t: residue.word_product(kernels, [k for k in old if k != t], P)[0] for t in old}
                    first_words = {r: residue.word_product(kernels, residue.ordered_word(old, r), P)[0] for r in set(first.values())}
                    alpha, beta, vector_alpha, vector_beta = [], [], [], []
                    inverse_X2 = pow(X[2], -1, P)
                    for t, a, b in columns:
                        if (t == u and a != cu) or (t == v and a != cv):
                            scalar_first = 0
                        else:
                            scalar_first = -X[a] % P
                            if t not in (u, v):
                                scalar_first = scalar_first * pow(residue.dot(A[t][a], X, P), -1, P) % P
                        vector = [(scalar_first * x + c[t, a] * y) % P
                                  for x, y in zip(omitted[t], first_words[first[t]])]
                        assert sum(vector) % P == 0
                        scale = A[t][a][b] * X[b] * X[0] % P
                        psi = scale * vector[2] * inverse_X2 % P
                        alpha.append(psi * wa % P)
                        beta.append(psi * wb % P)
                        if full_vector:
                            va, vb = residue.coordinates([scale * x % P for x in vector], U, V, P)
                            vector_alpha.append(va)
                            vector_beta.append(vb)
                    Z.extend((alpha, beta))
                    if (u, v) == (2, 3) and cu in (1, 2) and cv in (1, 2):
                        assert not any(alpha) and not any(beta)
                    if full_vector:
                        vectors.extend((vector_alpha, vector_beta))
    return Z, vectors, c


def feedback_limit(m, A):
    """Compute B0=J_incidence-T0 using the single-old-line formula H2."""
    old = list(range(2, m + 2))
    _, columns = schur.canonical_labels(m + 2)
    J, T0 = [], []
    for u in old:
        for c in range(3):
            line = (u, c)
            X = regular.edge_point(A, line, 0)
            kernels = {k: regular.kernel_or_residue(A, k, line, X, False) for k in old}
            stripped = {k: regular.kernel_or_residue(A, k, line, X, True) for k in old}
            words = {}
            for t in old:
                for s in old:
                    if t == s:
                        continue
                    word = [s] + [k for k in old if k not in (t, s)]
                    product = dual.identity()
                    for position, k in enumerate(word):
                        product = dual.mmul(product, stripped[k] if position == len(word) - 1 else kernels[k])
                    words[t, s] = product
            rows = [[], [], []]
            for t, s, a, b in columns:
                if t == u and a != c:
                    values = [dual.ZERO] * 3
                elif t == u:
                    scalar = dual.scale(A[t][a][b], X[a])
                    values = [dual.mul(scalar, dual.sub(dual.ONE if b == d else dual.ZERO,
                                                        dual.mul(X[b], words[t, s][b][d]))) for d in range(3)]
                else:
                    scalar = dual.scale(-A[t][a][b], dual.mul(dual.mul(X[a], X[b]),
                                                           dual.inverse(regular.dot(A[t][a], X))))
                    values = [dual.mul(scalar, value) for value in words[t, s][b]]
                for d in range(3):
                    if c == 0:
                        assert values[d][0] == 0
                        value = values[d][1] * pow(A[u][c][d], -1, P) % P
                    else:
                        value = values[d][0] * pow(A[u][c][d] * X[c][0] % P, -1, P) % P
                    rows[d].append(value)
            assert all(sum(A[u][c][d] * X[d][0] * rows[d][j] for d in range(3)) % P == 0
                       for j in range(len(columns)))
            T0.extend(rows)
            J.extend([[int((u, c, d) == (t, a, b)) for t, s, a, b in columns] for d in range(3)])
    return schur.matrix_difference(J, T0), J, T0


def solve_old_source(O, Z):
    """Solve the actual O*Y=Z; certify its pivots and verify the full equation."""
    n = len(O)
    a = [row[:] + rhs[:] for row, rhs in zip(O, Z)]
    ids, pivots, determinant = list(range(n)), [], 1
    for c in range(n):
        found = next((i for i in range(c, n) if a[i][c]), None)
        if found is None:
            return None, dict(invertible=False, failed_pivot_column=c,
                              rank_certificate=residue.modular_rank(O, P))
        if found != c:
            a[c], a[found] = a[found], a[c]
            ids[c], ids[found] = ids[found], ids[c]
            determinant = -determinant
        pivots.append(ids[c])
        determinant = determinant * a[c][c] % P
        inverse = pow(a[c][c], -1, P)
        tail = [x * inverse % P for x in a[c][c + 1:]]
        a[c][c], a[c][c + 1:] = 1, tail
        for i in range(c + 1, n):
            factor = a[i][c]
            if factor:
                a[i][c] = 0
                a[i][c + 1:] = [(x - factor * y) % P for x, y in zip(a[i][c + 1:], tail)]
    Y = [None] * n
    for i in range(n - 1, -1, -1):
        row = a[i][n:]
        for j in range(i + 1, n):
            factor = a[i][j]
            if factor:
                row = [(x - factor * y) % P for x, y in zip(row, Y[j])]
        Y[i] = row
    assert schur.matrix_product(O, Y) == Z
    return Y, dict(invertible=True, size=n, determinant_mod_prime=determinant,
                   pivot_rows=pivots, old_source_equation_verified=True,
                   old_source_matrix_sha256=residue.matrix_hash(O))


def matrix_certificate(matrix):
    return dict(rows=len(matrix), columns=len(matrix[0]), sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def boundary_diagnostic(m, A, Z):
    """Test the proposed six scalar pivots at first/last old-block crossings."""
    rows, _ = schur.canonical_labels(m + 2)
    row_indices = {label: i for i, label in enumerate(rows)}
    columns = [(t, a, b) for t in range(2, m + 2) for a in range(3) for b in range(3)]
    selected = [i for i, (t, a, b) in enumerate(columns) if t == 2 and a in (1, 2)]
    others = [i for i in range(len(columns)) if i not in selected]
    inverse_G, _ = schur.invert([list(row) for row in G])
    w = inverse_G[2]
    scalar_rows, row_labels = [], []
    for c in (1, 2):
        for d in range(3):
            X = residue.cross(A[2][c], A[m + 1][d], P)
            U = [A[2][c][i] * X[i] % P for i in range(3)]
            V = [A[m + 1][d][i] * X[i] % P for i in range(3)]
            wa, wb = residue.coordinates(w, U, V, P)
            coordinate, factor = ('alpha', wa) if wa else ('beta', wb)
            assert factor
            index = row_indices[2, m + 1, c, d, coordinate]
            row = [value * pow(factor, -1, P) % P for value in Z[index]]
            for name, component in (('alpha', wa), ('beta', wb)):
                assert Z[row_indices[2, m + 1, c, d, name]] == [x * component % P for x in row]
            scalar_rows.append(row)
            row_labels.append(dict(first_block_state=c, last_block_state=d,
                                   selected_coordinate=coordinate, w_coordinate_factor=factor))
    boundary = [[row[i] for i in selected] for row in scalar_rows]
    outside = [(r, i, scalar_rows[r][i]) for r in range(6) for i in others if scalar_rows[r][i]]
    return dict(m=m, time_fixture='economic', prime=P,
                scalar_row_labels=row_labels,
                selected_column_labels=[columns[i] for i in selected],
                selected_column_indices=selected,
                scalar_boundary_matrix=boundary,
                boundary_minor_certificate=matrix_certificate(boundary),
                all_boundary_columns_certificate=matrix_certificate(scalar_rows),
                other_incoming_columns_vanish=(not outside),
                nonzero_entries_outside_selected_columns=len(outside),
                first_outside_counterexample=None if not outside else dict(
                    scalar_row=outside[0][0], column_label=columns[outside[0][1]],
                    column_index=outside[0][1], coefficient_mod_prime=outside[0][2]),
                two_residue_coordinates_proportional_to_w_verified=True,
                scope='Finite test of the proposed six-pivot boundary step; no induction conclusion.')


def leading_operator_hypotheses(m, times, A):
    """Check odd polar constant blocks and limiting-axis geometry at this fixture."""
    poles = [(t, a, -A[t][a][1] * pow(A[t][a][2], -1, P) % P)
             for t in range(2, m + 2) for a in range(3)]
    assert all(z for _, _, z in poles)
    assert len({z for _, _, z in poles}) == 3 * m
    binary_numerator = (G[1][1] * G[2][2] - G[1][2] * G[2][1]) % P
    assert binary_numerator
    certificates = []
    with polar.transition_fixture(G):
        for new_state in range(3):
            M0, _, component = polar.first_jet_matrix(times, new_state, 3)
            certificate = matrix_certificate(M0)
            assert certificate['rank_certificate']['rank'] == 3 * m
            certificates.append(dict(new_line_state=new_state, selected_output_component=component,
                                     **certificate))
    return dict(old_axis_points_nonzero_and_pairwise_distinct=True,
                old_axis_points=[dict(block=t, state=a, X2_when_X1_equals_one=z) for t, a, z in poles],
                binary_restriction_numerator_minor=binary_numerator,
                all_three_odd_polar_constant_blocks_invertible=True,
                polar_constant_block_certificates=certificates,
                polar_convention='Existing shared_new_polar_firstjet normalization with B=3; its invertible limiting row factors identify these scalar matrices with the normalized shared-new polar blocks.',
                interpretation='With the separately checked old cross geometry and actual invertible O, the audited conditional H3/H5 formulas identify the mapped matrix as -H_-3 at this finite-field fixture.')


def calculate(m, record, saved, time_mode='economic', boundary_records=None):
    started = time.monotonic()
    times = sparse.factors(m, time_mode)
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    Z, full_vector, c = incoming_coefficients(m, A, full_vector=(m == 3))
    if boundary_records is not None:
        assert time_mode == 'economic'
        boundary_records.append(boundary_diagnostic(m, A, Z))
    record.update(m=m, time_fixture=time_mode, prime=P, G=G, old_time_factors=times,
                  incoming_Z_minus3=matrix_certificate(Z),
                  incoming_seconds=time.monotonic() - started,
                  first_two_blocks_binary_crosspoint_support_zeros_verified=True,
                  c_tA=[dict(t=t, a=a, coefficient=value) for (t, a), value in sorted(c.items())])
    print(json.dumps(dict(m=m, stage='incoming', rank=record['incoming_Z_minus3']['rank_certificate']['rank'],
                          columns=9*m, seconds=record['incoming_seconds'])), flush=True)
    if full_vector:
        record['full_vector_before_output_projection'] = matrix_certificate(full_vector)
        record['full_vector_column_normalization'] = 'A_t(A,B)*X_B*X0*V_tA; nonzero A_t(A,B) column factors preserve rank.'
    if m == 3 and time_mode == 'economic':
        assert record['incoming_Z_minus3']['sha256'] == saved['coefficient_matrix_sha256']['Z_minus3']
        assert record['incoming_Z_minus3']['rank_certificate'] == saved['coefficient_rank_certificates']['Z_minus3']
    B0, J, T0 = feedback_limit(m, A)
    record.update(B0=matrix_certificate(B0), J_incidence=matrix_certificate(J), T0=matrix_certificate(T0))
    if m == 3 and time_mode == 'economic':
        for name, matrix in [('B0', B0), ('J_incidence', J), ('T0', T0)]:
            assert residue.matrix_hash(matrix) == saved['coefficient_matrix_sha256'][name]
    O, geometry = residue.residue_matrix(m + 2, A, P)
    Y, solve_certificate = solve_old_source(O, Z)
    record['old_source_solve'] = solve_certificate
    record['old_geometry'] = geometry
    if Y is None:
        record['mapped_limitation'] = 'The actual old source residue matrix is singular at this fixture.'
        return
    mapped = schur.matrix_product(B0, Y)
    record['OinvZ_minus3'] = matrix_certificate(Y)
    record['B0_OinvZ_minus3'] = matrix_certificate(mapped)
    if m == 3 and time_mode == 'economic':
        for name, matrix in [('OinvZ_minus3', Y), ('B0_OinvZ_minus3', mapped)]:
            assert residue.matrix_hash(matrix) == saved['coefficient_matrix_sha256'][name]
            assert residue.modular_rank(matrix, P) == saved['coefficient_rank_certificates'][name]
        record['saved_m3_Laurent_diagnostic_reproduced'] = True
    record['leading_operator_hypotheses'] = leading_operator_hypotheses(m, times, A)
    record['elapsed_seconds'] = time.monotonic() - started
    print(json.dumps(dict(m=m, stage='mapped', incoming_rank=record['incoming_Z_minus3']['rank_certificate']['rank'],
                          mapped_rank=record['B0_OinvZ_minus3']['rank_certificate']['rank'],
                          full_vector_rank=record.get('full_vector_before_output_projection', {}).get('rank_certificate', {}).get('rank'),
                          seconds=record['elapsed_seconds'])), flush=True)


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else value * 1024


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, choices=(5, 7), default=5)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    saved_results = json.loads((HERE / 'source24-regular-laurent-results.json').read_text())
    saved = next(case for case in saved_results['leading_operator_diagnostics'] if case['m'] == 3)
    started, cases, boundary_records = time.monotonic(), [], []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second process cutoff reached; completed certificates remain valid.')
        if maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB RSS guard reached; completed certificates remain valid.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for m in (3, 5):
            cases.append(dict(m=m))
            calculate(m, cases[-1], saved, boundary_records=boundary_records)
        if args.max_m == 7 and time.monotonic() - started < 8 and cases[-1].get('elapsed_seconds', 28) < 2.5:
            cases.append(dict(m=7))
            calculate(7, cases[-1], saved, boundary_records=boundary_records)
        elif args.max_m == 7:
            cases.append(dict(m=7, skipped=True, limitation='Earlier timings did not make m7 cheap within the shared 28-second bound.'))
        cases.append(dict(m=3, time_fixture='independent'))
        calculate(3, cases[-1], saved, time_mode='independent')
    except TimeoutError as error:
        cases[-1]['bounded_limitation'] = str(error)
        print(json.dumps(dict(m=cases[-1]['m'], limitation=str(error))), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='External exact finite-field incoming and mapped-rank certificates; no all-m or Lean theorem.',
                  formulas='H2 computes B0=J_incidence-T0; H5 computes Z_-3; the actual old source matrix solves O*Y=Z; H_-3=-B0*Y.',
                  column_order='(old block t, state A, state B), with old block IDs 2,...,m+1 and B fastest.',
                  residue_row_order='(u,v,old state c,old state d,alpha/beta) in source24_residue order.',
                  limitations='A modular rank deficiency is not a real rank upper bound. Nonzero minors lift after denominator clearing. These fixtures do not prove independence for all lengths.',
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=maximum_rss_bytes(), cases=cases,
                  boundary_diagnostics=boundary_records)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
