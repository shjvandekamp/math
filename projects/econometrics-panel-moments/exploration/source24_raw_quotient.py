#!/usr/bin/env python3
"""Direct exact evaluations of the raw append quotient on actual boundary rows.

The columns are the 18q actual Qhat_(t,s,a,b) with t=N or s=N, in the
existing source24_raw_boundary order. We evaluate three groups from
SOURCE24_RAW_QUOTIENT.md, without constructing the large old ambient frame:
  new-line residues of R=H K_N^-1;
  axis restrictions of C=H diag(X)^-1 A_N^-1;
  eta_(u,c)=[(Res_(L_uc) B/Xc) A_N^-1]_c at L_uc=Xc=0.

New-line residues use actual K products and a finite matrix K_N^-1 on
the line, and are checked against conjugated J=diag(X/L) A products.
Axes and analytically divided matching values use J, never a division by
a coordinate which is zero. At q=2, independent actual-kernel first jets
check eta, and every observation is checked on the appended explicit old
E/V/diagonal frame. The three row groups are combined before computing rank;
their separate ranks are never added as though they were independent.

All reported ranks are finite-field lower-bound certificates for the
rational observations at the recorded fixtures. No uniform rank theorem
or identification of all sampled restrictions is claimed.

Reproduce:
  nice -n 19 python3 exploration/source24_raw_quotient.py --output exploration/source24-raw-quotient-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_raw_boundary as raw


P, G = raw.P, raw.G
incoming, residue, schur, sparse = raw.incoming, raw.residue, raw.schur, raw.sparse
dual, regular = incoming.dual, incoming.regular
HERE = Path(__file__).resolve().parent
UNIT = [[int(i == j) for j in range(3)] for i in range(3)]


def inverse(x):
    assert x % P, 'Forbidden zero denominator.'
    return pow(x % P, -1, P)


def row_product(row, matrix):
    return residue.matmul([row], matrix, P)[0]


def order(blocks, t, s):
    return [s] + [u for u in blocks if u not in (t, s)]


def cached_product(kernels):
    cache = {(): residue.identity()}

    def product(word):
        key = tuple(word)
        if key not in cache:
            cache[key] = residue.word_product(kernels, word, P)
        return cache[key]
    return product


def conjugated_kernels(A, X, omit=None):
    return {t: [[X[a] * inverse(residue.dot(A[t][a], X, P)) * A[t][a][b] % P
                 for b in range(3)] for a in range(3)]
            for t in range(2, len(A)) if t != omit}


def boundary_C(A, ANinv, X, columns):
    blocks = list(range(2, len(A)))
    product = cached_product(conjugated_kernels(A, X))
    result = []
    for label in columns:
        t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
        scalar = X[a] * A[t][a][b] * inverse(residue.dot(A[t][a], X, P)) % P
        B = raw.row_scale(scalar, product(order(blocks, t, s))[b])
        result.append(row_product(B, ANinv))
    return result


def new_line_residue(A, ANinv, X, c, columns):
    """Actual rank-one K residue, then the finite inverse on the new line."""
    N, blocks = len(A) - 1, list(range(2, len(A)))
    LN = [residue.dot(row, X, P) for row in A[N]]
    assert LN[c] == 0 and all(LN[i] for i in range(3) if i != c) and all(X)
    kernels = {t: residue.ordinary_kernel(A, t, X, P) for t in blocks if t != N}
    kernels[N] = [[A[N][c][i] * X[i] % P for i in range(3)] if a == c else [0, 0, 0]
                  for a in range(3)]
    product = cached_product(kernels)
    KNinv = [[inverse(X[i]) * ANinv[i][j] * LN[j] % P for j in range(3)] for i in range(3)]
    result = []
    for label in columns:
        t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
        Hres = raw.row_scale(X[a] * kernels[t][a][b], product(order(blocks, t, s))[b])
        result.append(row_product(Hres, KNinv))
    assert all(value[c] == 0 for value in result)

    # A second implementation first cancels all final coordinate factors.
    Jproduct = cached_product(conjugated_kernels(A, X, omit=N))
    inverse_tail = [[ANinv[i][j] * LN[j] % P for j in range(3)] for i in range(3)]
    for label, actual in zip(columns, result):
        t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
        if t == N:
            B = raw.row_scale(X[c] * A[N][c][b], Jproduct(order(blocks, t, s))[b]) if a == c else [0, 0, 0]
        elif b == c:
            scalar = X[a] * A[t][a][b] * inverse(residue.dot(A[t][a], X, P)) * X[c]
            suffix = [u for u in blocks if u not in (t, N)]
            B = raw.row_scale(scalar, row_product(A[N][c], Jproduct(suffix)))
        else:
            B = [0, 0, 0]
        assert actual == row_product(B, inverse_tail), ('K/J new-pole mismatch.', c, label, X)
    return result, kernels[N], KNinv


def matching_values(A, ANinv, line, X, columns):
    """N10/RQ4: remove Xc from the residue before matching evaluation."""
    u, c = line
    assert X[c] == 0 and residue.dot(A[u][c], X, P) == 0
    blocks = list(range(2, len(A)))
    product = cached_product(conjugated_kernels(A, X, omit=u))
    result = []
    for label in columns:
        t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
        word = order(blocks, t, s)
        if t == u:
            divided = raw.row_scale(A[t][a][b], product(word)[b]) if a == c else [0, 0, 0]
        else:
            position = word.index(u)
            before, after = product(word[:position]), product(word[position + 1:])
            scalar = X[a] * A[t][a][b] * inverse(residue.dot(A[t][a], X, P)) * before[b][c]
            divided = raw.row_scale(scalar, row_product(A[u][c], after))
        result.append(sum(divided[j] * ANinv[j][c] for j in range(3)) % P)
    return result


def matching_jet_check(A, ANinv, line, Xjet, columns, expected):
    """Independent actual-K residue, stripped only at its final output, /Xc."""
    u, c = line
    assert Xjet[c] == regular.EPS
    blocks, cache = list(range(2, len(A))), {}
    for label, value in zip(columns, expected):
        t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
        if (t, s) not in cache:
            word = order(blocks, t, s)
            matrix = dual.identity()
            for position, v in enumerate(word):
                matrix = dual.mmul(matrix, regular.kernel_or_residue(A, v, line, Xjet,
                                                                   position == len(word) - 1))
            cache[t, s] = matrix
        if t == u and a != c:
            B = [dual.ZERO] * 3
        else:
            scalar = dual.scale(A[t][a][b], dual.mul(Xjet[a], Xjet[b]))
            if t != u:
                scalar = dual.mul(scalar, dual.inverse(regular.dot(A[t][a], Xjet)))
            B = [dual.mul(scalar, entry) for entry in cache[t, s][b]]
        assert all(entry[0] == 0 for entry in B)
        eta = sum(B[j][1] * ANinv[j][c] for j in range(3)) % P
        assert eta == value, ('Actual-K matching first jet mismatch.', line, label)
    return len(columns)


def old_frame_B(A, X, labels):
    """The actual old E/V/diagonal frame after final-coordinate division."""
    J = conjugated_kernels(A, X)
    result = []
    for label in labels:
        if label['kind'] == 'elementary_pair':
            u, c = label['start']
            v, d = label['end']
            scalar = X[c] * A[u][c][d] * inverse(residue.dot(A[u][c], X, P))
            result.append(raw.row_scale(scalar, raw.row_subtract(UNIT[d], J[v][d])))
        elif label['kind'] == 'V':
            u, c = label['line']
            b = label['output']
            scalar = X[c] * A[u][c][b] * inverse(residue.dot(A[u][c], X, P))
            result.append([(scalar * int(j == b) - int(c == b and j == c)) % P for j in range(3)])
        else:
            result.append(UNIT[label['state']][:])
    return result


def old_frame_divided_residue(A, line, X, labels):
    u, c = line
    J = conjugated_kernels(A, X, omit=u)
    result = []
    for label in labels:
        if label['kind'] == 'elementary_pair':
            t, a = label['start']
            v, b = label['end']
            if (t, a) == line:
                row = raw.row_scale(A[t][a][b], raw.row_subtract(UNIT[b], J[v][b]))
            elif (v, b) == line:
                scalar = -X[a] * A[t][a][b] * inverse(residue.dot(A[t][a], X, P))
                row = raw.row_scale(scalar, A[v][b])
            else:
                row = [0, 0, 0]
        elif label['kind'] == 'V' and tuple(label['line']) == line:
            row = raw.row_scale(A[u][c][label['output']], UNIT[label['output']])
        else:
            row = [0, 0, 0]
        result.append(row)
    return result


def line_points(A, c, count):
    N, result, rejected, parameter = len(A) - 1, [], 0, 0
    while len(result) < count:
        parameter += 1
        assert parameter < 10000
        X = (-inverse(A[N][c][0]) * (A[N][c][1] + A[N][c][2] * parameter) % P, 1, parameter)
        if not all(X) or any(residue.dot(A[t][a], X, P) == 0
                             for t in range(2, len(A)) for a in range(3) if (t, a) != (N, c)):
            rejected += 1
            continue
        result.append(X)
    return result, rejected


def axis_points(A, d, count):
    others = [i for i in range(3) if i != d]
    result, rejected, parameter = [], 0, 0
    while len(result) < count:
        parameter += 1
        assert parameter < 10000
        X = [0, 0, 0]
        X[others[0]], X[others[1]] = 1, parameter
        if any(residue.dot(row, X, P) == 0 for table in A[2:] for row in table):
            rejected += 1
            continue
        result.append(tuple(X))
    return result, rejected


def calculate(q, saved_cases):
    started, m, N = time.monotonic(), q + 1, q + 2
    times = sparse.factors(m, 'economic')
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    geometry = raw.differences.check_geometry(m, A)
    ANinv, inverse_certificate = schur.invert([[x % P for x in row] for row in A[N]])
    assert ANinv is not None
    frame, columns = raw.labels(q)
    new_rows, axes_rows, eta_rows = [], [], []
    new_labels, axes_labels, eta_labels = [], [], []
    new_samples, axes_samples, matching_samples = [], [], []
    frame_checks = dict(new_poles=0, axes=0, matching=0)
    jet_checks, ordinary_checks, new_formula_checks = 0, 0, 0

    if q == 2:
        X = (1, 2, 3)
        actual, _ = raw.evaluate(q, A, X, frame, columns)
        expected = boundary_C(A, ANinv, X, columns)
        for H, C in zip(actual[len(frame):], expected):
            assert row_product([H[d] * inverse(X[d]) % P for d in range(3)], ANinv) == C
            ordinary_checks += 3
        JN = conjugated_kernels(A, X)[N]
        for H, B in zip(actual[:len(frame)], old_frame_B(A, X, frame)):
            assert row_product([H[d] * inverse(X[d]) % P for d in range(3)], ANinv) == row_product(row_product(B, JN), ANinv)
            ordinary_checks += 3

    for c in range(3):
        points, rejected = line_points(A, c, 3*q + 3)
        new_samples.append(dict(state=c, points=points, rejected=rejected))
        for point_index, X in enumerate(points):
            values, KNres, KNinv = new_line_residue(A, ANinv, X, c, columns)
            new_formula_checks += 3 * len(columns)
            for d in range(3):
                if d != c:
                    new_rows.append([value[d] for value in values])
                    new_labels.append(dict(new_state=c, point_index=point_index, output=d))
            if q == 2:
                # Old B formulas are ordinary here; recover H_old by diag(X).
                # The appended new-line residue is H_old*Res(K_N).
                for B in old_frame_B(A[:-1], X, frame):
                    Hold = [B[d] * X[d] % P for d in range(3)]
                    stripped = row_product(row_product(Hold, KNres), KNinv)
                    assert not any(stripped)
                    frame_checks['new_poles'] += 3

    for d in range(3):
        points, rejected = axis_points(A, d, 2*q + 4)
        axes_samples.append(dict(axis=d, points=points, rejected=rejected))
        for point_index, X in enumerate(points):
            values = boundary_C(A, ANinv, X, columns)
            axes_rows.append([value[d] for value in values])
            axes_labels.append(dict(axis=d, point_index=point_index))
            if q == 2:
                JN = conjugated_kernels(A, X)[N]
                for B in old_frame_B(A, X, frame):
                    assert row_product(row_product(B, JN), ANinv)[d] == 0
                    frame_checks['axes'] += 1

    for u in range(2, N):
        for c in range(3):
            line = (u, c)
            Xjet = regular.edge_point(A, line, c)
            X = tuple(value[0] for value in Xjet)
            values = matching_values(A, ANinv, line, X, columns)
            eta_rows.append(values)
            eta_labels.append(line)
            matching_samples.append(dict(line=line, point=X))
            if q == 2:
                jet_checks += matching_jet_check(A, ANinv, line, Xjet, columns, values)
                JN = conjugated_kernels(A, X, omit=u)[N]
                for divided in old_frame_divided_residue(A, line, X, frame):
                    assert row_product(row_product(divided, JN), ANinv)[c] == 0
                    frame_checks['matching'] += 1

    column_index = {(label['t'], label['s'], label['a'], label['b']): j for j, label in enumerate(columns)}
    eta_index = {line: i for i, line in enumerate(eta_labels)}
    diagonal_checks = []
    for a in range(3):
        for b in range(3):
            if b == a:
                continue
            indices = [column_index[t, N, a, b] for t in range(2, N)]
            matrix = [[eta_rows[eta_index[u, a]][j] for j in indices] for u in range(2, N)]
            assert all(matrix[i][j] == 0 for i in range(q) for j in range(q) if i != j)
            diagonal = [matrix[i][i] for i in range(q)]
            det = 1
            for value in diagonal:
                det = det * value % P
            diagonal_checks.append(dict(a=a, b=b, columns=indices,
                                        rows=[eta_index[t, a] for t in range(2, N)],
                                        off_diagonal_zero=True, diagonal=diagonal,
                                        all_diagonal_entries_nonzero=all(diagonal), determinant_mod_prime=det))

    new_certificate = incoming.matrix_certificate(new_rows)
    axes_certificate = incoming.matrix_certificate(new_rows + axes_rows)
    all_certificate = incoming.matrix_certificate(new_rows + axes_rows + eta_rows)
    incoming_columns = [j for j, label in enumerate(columns) if label['kind'] == 'first_new']
    incoming_unequal_columns = [j for j in incoming_columns if columns[j]['a'] != columns[j]['b']]
    assert len(incoming_columns) == 9*q and len(incoming_unequal_columns) == 6*q
    matching_certificate = incoming.matrix_certificate(eta_rows)
    matching_incoming_certificate = incoming.matrix_certificate(
        [[row[j] for j in incoming_columns] for row in eta_rows])
    matching_incoming_unequal_certificate = incoming.matrix_certificate(
        [[row[j] for j in incoming_unequal_columns] for row in eta_rows])
    ranks = [certificate['rank_certificate']['rank'] for certificate in (new_certificate, axes_certificate, all_certificate)]
    assert ranks[0] <= ranks[1] <= ranks[2] <= 18*q
    # These dimension bounds are consequences of the audited ambient quotient,
    # not an assertion that our sampled row groups are mutually independent.
    assert ranks[0] <= 9*q + 6 and ranks[1] <= 15*q + 9
    comparison = None
    previous = [case for case in saved_cases if case['q'] == q and case['time_fixture'] == 'economic'
                and case['finite_independence_modulo_entire_appended_frame_certified']]
    if previous:
        prior = previous[-1]
        assert prior['G'] == [list(row) for row in G] and prior['time_factors'] == [list(pair) for pair in times]
        comparison = dict(file='source24-raw-boundary-results.json', case_label=prior.get('case_label'),
                          old_frame_and_boundary_rank=prior['combined_evaluation']['rank_certificate']['rank'],
                          combined_matrix_sha256=prior['combined_evaluation']['sha256'],
                          prior_full_modulo_appended_frame=True,
                          quotient_observation_full_column_rank=ranks[2] == 18*q,
                          previous_calculation_rerun=False)
    result = dict(q=q, m=m, prime=P, G=G, time_fixture='economic', time_factors=times,
                  geometry=geometry, terminal_inverse_certificate=inverse_certificate,
                  boundary_column_count=len(columns), boundary_column_labels=columns,
                  new_pole_observations=new_certificate, new_poles_and_axes=axes_certificate,
                  all_quotient_observations=all_certificate,
                  matching_on_all_boundary=matching_certificate,
                  matching_on_incoming=matching_incoming_certificate,
                  matching_on_incoming_unequal_states=matching_incoming_unequal_certificate,
                  matching_incoming_column_indices=incoming_columns,
                  matching_incoming_unequal_column_indices=incoming_unequal_columns,
                  nested_ranks=ranks, full_boundary_rank_over_Fp=ranks[2] == 18*q,
                  matching_rank_gain=ranks[2] - ranks[1], sampled_boundary_kernel_dimension=18*q-ranks[2],
                  new_pole_row_labels=new_labels, axis_row_labels=axes_labels, matching_row_labels=eta_labels,
                  combined_row_order='All new-pole rows, then all axis rows, then all matching rows, in the saved order.',
                  new_line_samples=new_samples, axis_samples=axes_samples, matching_samples=matching_samples,
                  new_line_point_count_per_state=3*q+3, axis_point_count_per_axis=2*q+4,
                  no_forbidden_denominator_evaluations=True,
                  actual_K_vs_J_new_residue_component_checks=new_formula_checks,
                  direct_ordinary_kernel_component_checks=ordinary_checks,
                  independent_actual_K_matching_first_jet_checks=jet_checks,
                  appended_old_frame_annihilation_checks=frame_checks,
                  frame_annihilation_scope='All sampled quotient observations on every old E/V/diagonal frame column at q=2.' if q == 2 else 'The separate q=2 control checks the implementation; no large old frame evaluated here.',
                  fixed_state_matching_diagonal_minors=diagonal_checks,
                  prior_full_frame_comparison=comparison,
                  limitation='Ranks are exact modular sampled-observation ranks. A full 18q minor certifies this finite boundary family modulo the appended ambient using the audited annihilation identities. A deficiency is not a rational-function upper bound.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q, columns=len(columns), new_poles=ranks[0], new_and_axes=ranks[1],
                          all=ranks[2], full=ranks[2] == 18*q, matching_gain=ranks[2]-ranks[1],
                          matching_ranks=[certificate['rank_certificate']['rank'] for certificate in
                              (matching_certificate, matching_incoming_certificate, matching_incoming_unequal_certificate)],
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE / 'source24-raw-boundary-results.json').read_text())
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second raw-quotient cutoff.')
        if incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('95 MiB raw-quotient RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation, current = None, None
    try:
        for current in (2, 3, 4, 5, 6):
            cases.append(calculate(current, saved['cases']))
    except TimeoutError as error:
        limitation = dict(q=current, reason=str(error))
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Direct finite exact raw-quotient observations on actual boundary columns; no all-length theorem.',
                  reference='research/SOURCE24_RAW_QUOTIENT.md, RQ2--RQ5; matching division is the actual conjugated-product N10 formula.',
                  independent_checks='New poles: actual K residue products versus J products. At q=2: actual ordinary K values, independently differentiated actual-K matching residues, and annihilation of every appended old E/V/diagonal frame column.',
                  limitations='Only finite lower-bound minors are certified. No assertion that separate observation groups are independent, no full source O construction, and no uniform source-independence claim.',
                  limits=dict(seconds=28, maximum_rss_bytes=95*1024**2),
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
