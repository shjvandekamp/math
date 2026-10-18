#!/usr/bin/env python3
"""Bounded actual-source checks of native terminal extraction, N6--N16.

The first implementation uses actual stripped-kernel source residues and
the terminal inverse. The second removes the matching factor analytically
in the conjugated ordered products, as in N10. Compare them at all three
coordinate edges of every pre-terminal line. Native seed components have
an additional X0 cancellation: independent second-order source jets check
the already-matching-divided first-jet formula even when c=d=0.

The boundary matrix contains exactly the four groups in N13, including the
full terminal long-empty rows. Its binary rank is a finite diagnostic, not
an incoming-independence or all-length theorem.

Reproduce:
  nice -n 19 python3 exploration/source24_terminal_extraction.py --output exploration/source24-terminal-extraction-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming
import source24_residue_differences as differences


P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
dual, regular = incoming.dual, incoming.regular
JZERO, JONE = (0, 0, 0), (1, 0, 0)


def dscale(scalar, row):
    return [dual.scale(scalar, value) for value in row]


def dsubtract(left, right):
    return [dual.sub(x, y) for x, y in zip(left, right)]


def matching_value(value, Xc, extra=dual.ONE):
    """Evaluate value/(Xc*extra) after cancelling a matching zero."""
    assert extra[0]
    if Xc[0]:
        return value[0] * pow(Xc[0] * extra[0] % P, -1, P) % P
    assert value[0] == 0 and Xc[1]
    return value[1] * pow(Xc[1] * extra[0] % P, -1, P) % P


def word(blocks, shared, first):
    return [first] + [u for u in blocks if u not in (shared, first)]


def analytic_g_rows(A, line, X, columns, empty_labels):
    """N10, before any coordinate-edge evaluation, using dual arithmetic."""
    u, c = line
    blocks = list(range(2, len(A)))
    tildes = {}
    for t in blocks:
        if t == u:
            continue
        tildes[t] = [dscale(1, [dual.scale(A[t][a][b], dual.mul(X[a], dual.inverse(regular.dot(A[t][a], X))))
                               for b in range(3)]) for a in range(3)]
    cache = {(): dual.identity()}

    def product(order):
        key = tuple(order)
        if key not in cache:
            value = dual.identity()
            for t in key:
                value = dual.mmul(value, tildes[t])
            cache[key] = value
        return cache[key]

    def split(order):
        position = order.index(u)
        before, after = product(order[:position]), product(order[position + 1:])
        row = regular.row_product([(a % P, 0) for a in A[u][c]], after)
        return before, row

    sources = []
    for t, s, a, b in columns:
        order = word(blocks, t, s)
        if t == u:
            value = dscale(A[t][a][b], product(order)[b]) if a == c else [dual.ZERO] * 3
        else:
            before, after_row = split(order)
            scalar = dual.scale(A[t][a][b], dual.mul(dual.mul(X[a], dual.inverse(regular.dot(A[t][a], X))),
                                                   before[b][c]))
            value = [dual.mul(scalar, x) for x in after_row]
        sources.append(value)
    empties = []
    for t, a in empty_labels:
        before, after_row = split(residue.ordered_word(blocks, t))
        empties.append([dual.mul(before[a][c], x) for x in after_row])
    return sources, empties


def actual_empty_transformed(A, M, line, X, empty_labels, LN):
    """Residue of the full actual long-empty row times K_terminal^-1."""
    blocks = list(range(2, len(A)))
    inverse_tail = regular.inverse_tail(M, LN)
    kernels = {t: regular.kernel_or_residue(A, t, line, X, False) for t in blocks}
    stripped = {t: regular.kernel_or_residue(A, t, line, X, True) for t in blocks}
    products = {}
    for t in blocks:
        order = residue.ordered_word(blocks, t)
        value = dual.identity()
        for position, k in enumerate(order):
            value = dual.mmul(value, stripped[k] if position == len(order) - 1 else kernels[k])
        products[t] = dual.mmul(value, inverse_tail)
    return [[dual.scale(-1, dual.mul(X[a], value)) for value in products[t][a]] for t, a in empty_labels]


def jadd(left, right):
    return tuple((a + b) % P for a, b in zip(left, right))


def jscale(scalar, value):
    return tuple(scalar * a % P for a in value)


def jmul(left, right):
    return tuple(sum(left[i] * right[d - i] for i in range(d + 1)) % P for d in range(3))


def jinverse(value):
    assert value[0]
    inverse = [pow(value[0], -1, P)]
    for d in range(1, 3):
        inverse.append(-inverse[0] * sum(value[i] * inverse[d - i] for i in range(1, d + 1)) % P)
    return tuple(inverse)


def jsum(values):
    result = JZERO
    for value in values:
        result = jadd(result, value)
    return result


def jdot(row, X):
    return jsum(jscale(a, x) for a, x in zip(row, X))


def jidentity():
    return [[JONE if a == b else JZERO for b in range(3)] for a in range(3)]


def jmatmul(left, right):
    return [[jsum(jmul(left[a][c], right[c][b]) for c in range(3)) for b in range(3)] for a in range(3)]


def quotient_value(value, factors):
    """Constant term after up to two exact affine-coordinate cancellations."""
    order, leading = 0, 1
    for factor in factors:
        if factor[0]:
            leading = leading * factor[0] % P
        else:
            assert factor[1]
            order += 1
            leading = leading * factor[1] % P
    assert order <= 2 and all(value[d] == 0 for d in range(order))
    return value[order] * pow(leading, -1, P) % P


def actual_native_jets(A, line, Xdual, seed_labels, constants):
    """Independent order-two Res(U diag(X)^-1), before dividing by Xc."""
    u, c = line
    blocks = list(range(2, len(A)))
    X = [tuple(value) + (0,) for value in Xdual]
    kernels, stripped = {}, {}
    for t in blocks:
        if t == u:
            kernels[t] = [[jscale(A[t][c][b], X[b]) for b in range(3)] if a == c else [JZERO] * 3 for a in range(3)]
            stripped[t] = [[(A[t][c][b] % P, 0, 0) for b in range(3)] if a == c else [JZERO] * 3 for a in range(3)]
        else:
            inverses = [jinverse(jdot(A[t][a], X)) for a in range(3)]
            kernels[t] = [[jscale(A[t][a][b], jmul(X[b], inverses[a])) for b in range(3)] for a in range(3)]
            stripped[t] = [[jscale(A[t][a][b], inverses[a]) for b in range(3)] for a in range(3)]
    cache = {}

    def product(order):
        key = tuple(order)
        if key not in cache:
            value = jidentity()
            for position, t in enumerate(order):
                value = jmatmul(value, stripped[t] if position == len(order) - 1 else kernels[t])
            cache[key] = value
        return cache[key]

    result = []
    for t, a in seed_labels:
        r = min(s for s in blocks if s != t)
        source_word = product(word(blocks, t, r))
        if t == u and a != c:
            source = [JZERO] * 3
        elif t == u:
            scalar = jscale(A[t][a][0], X[a])
            source = [jmul(scalar, jadd(JONE if d == 0 else JZERO, jscale(-1, jmul(X[0], source_word[0][d]))))
                      for d in range(3)]
        else:
            scalar = jscale(-A[t][a][0], jmul(jmul(X[a], X[0]), jinverse(jdot(A[t][a], X))))
            source = [jmul(scalar, value) for value in source_word[0]]
        empty_word = product(residue.ordered_word(blocks, r))
        empty = [jscale(-1, jmul(X[0], value)) for value in empty_word[0]]
        result.append([jadd(jscale(pow(A[t][a][0], -1, P), x), jscale(-constants[t, a], y))
                       for x, y in zip(source, empty)])
    return X, result


def extraction(q, A, M, columns, empty_labels, seed_labels, constants):
    terminal = q + 2
    lines = [(u, c) for u in range(2, terminal) for c in range(3)]
    source_index = {label: j for j, label in enumerate(columns)}
    empty_index = {label: j for j, label in enumerate(empty_labels)}
    Mdual = [[(x, 0) for x in row] for row in M]
    Jsource, Jempty, Hsource, native = [], [], [], [[], []]
    counts = dict(source_matching_divisions=0, empty_matching_divisions=0,
                  analytic_source_g_vectors_checked=0, analytic_empty_g_vectors_checked=0,
                  native_second_order_residue_checks=0, native_double_zero_cancellations=0,
                  native_E_formula_checks=0)
    for line in lines:
        u, c = line
        Esource, Eempty, Gsource, Enative = [], [], [], [[], []]
        for d in range(3):
            X = regular.edge_point(A, line, d)
            actual, _, LN = regular.source_and_aux_residues(A, M, line, X, columns, [])
            empty_actual = actual_empty_transformed(A, M, line, X, empty_labels, LN)
            gsource, gempty = analytic_g_rows(A, line, X, columns, empty_labels)
            Bsource = []
            for label, g in zip(columns, gsource):
                t, s, a, b = label
                prefix = [(A[t][a][b] % P, 0) if e == b and line == (t, a) else dual.ZERO for e in range(3)]
                Bsource.append(dsubtract(prefix, g))
            Bempty = [dscale(-1, g) for g in gempty]
            source_values, empty_values, g_values = [], [], []
            for values, analytic_B, g in zip(actual, Bsource, gsource):
                evaluated = [matching_value(values[e], X[c], LN[e]) for e in range(3)]
                independent_B = residue.matmul([evaluated], A[terminal], P)[0]
                assert independent_B == [value[0] for value in analytic_B], ('N10 source residue mismatch.', q, line, d)
                analytic_E = regular.row_product(analytic_B, Mdual)
                assert evaluated == [value[0] for value in analytic_E], ('N6 source extraction mismatch.', q, line, d)
                source_values.append(evaluated[d])
                g_values.append(regular.row_product(g, Mdual)[d][0])
                counts['analytic_source_g_vectors_checked'] += 1
                counts['source_matching_divisions'] += int(c == d)
            for values, analytic_B in zip(empty_actual, Bempty):
                evaluated = [matching_value(values[e], X[c], LN[e]) for e in range(3)]
                independent_B = residue.matmul([evaluated], A[terminal], P)[0]
                assert independent_B == [value[0] for value in analytic_B], ('Long-empty matching cancellation mismatch.', q, line, d)
                assert evaluated == [value[0] for value in regular.row_product(analytic_B, Mdual)]
                empty_values.append(evaluated[d])
                counts['analytic_empty_g_vectors_checked'] += 1
                counts['empty_matching_divisions'] += int(c == d)
            Esource.append(source_values)
            Eempty.append(empty_values)
            Gsource.append(g_values)

            Xjet, seed_jets = actual_native_jets(A, line, X, seed_labels, constants)
            native_values = [[], []]
            for (t, a), jet in zip(seed_labels, seed_jets):
                r = min(s for s in range(2, len(A)) if s != t)
                Bseed = dsubtract(dscale(pow(A[t][a][0], -1, P), Bsource[source_index[t, r, a, 0]]),
                                  dscale(constants[t, a], Bempty[empty_index[r, 0]]))
                for j in (1, 2):
                    actual_B = quotient_value(jet[j], [Xjet[c]])
                    actual_R = quotient_value(jet[j], [Xjet[c], Xjet[0]])
                    analytic_R = matching_value(Bseed[j], X[0])
                    assert actual_B == Bseed[j][0] and actual_R == analytic_R, ('Native divided-residue mismatch.', q, line, d, t, a, j)
                    actual_E = (actual_B * M[j][d] - X[j][0] * actual_R * M[0][d]) % P
                    formula_E = analytic_R * (X[0][0] * M[j][d] - X[j][0] * M[0][d]) % P
                    assert actual_E == formula_E, ('N14 failed.', q, line, d, t, a, j)
                    native_values[j - 1].append(actual_E)
                    counts['native_second_order_residue_checks'] += 1
                    counts['native_double_zero_cancellations'] += int(c == d == 0)
                    counts['native_E_formula_checks'] += 1
            for j in range(2):
                Enative[j].append(native_values[j])
        for b in range(3):
            inverse = pow(A[u][c][b], -1, P)

            def combine(matrix):
                return [inverse * sum(A[terminal][d][b] * matrix[d][k] for d in range(3)) % P
                        for k in range(len(matrix[0]))]

            Jsource.append(combine(Esource))
            Jempty.append(combine(Eempty))
            Hsource.append(combine(Gsource))
            for j in range(2):
                native[j].append(combine(Enative[j]))
    output_labels = [(u, c, b) for u, c in lines for b in range(3)]
    interior_checks = empty_checks = seed_checks = 0
    for row, (u, c, b) in enumerate(output_labels):
        for col, (t, s, a, divergent) in enumerate(columns):
            incidence = int((u, c, b) == (t, a, divergent))
            assert Jsource[row][col] == (incidence - Hsource[row][col]) % P, ('N12 failed.', q, row, col)
            if t < terminal and s < terminal:
                assert Jsource[row][col] == incidence and Hsource[row][col] == 0, ('Interior N7 failed.', q, row, col)
                interior_checks += 1
        for col, (t, a) in enumerate(empty_labels):
            if t < terminal:
                assert Jempty[row][col] == 0, ('Long-empty N7 failed.', q, row, col)
                empty_checks += 1
        for col, (t, a) in enumerate(seed_labels):
            r = min(s for s in range(2, terminal) if s != t)
            actual_seed_J = (Jsource[row][source_index[t, r, a, 0]]
                             - constants[t, a] * Jempty[row][empty_index[r, 0]]) % P
            assert actual_seed_J == int((u, c, b) == (t, a, 0))
            assert (native[0][row][col] + native[1][row][col]) % P == actual_seed_J, ('N15/N16 native sum failed.', q, row, col)
            seed_checks += 1
    counts.update(interior_N7_entries=interior_checks, long_empty_N7_entries=empty_checks,
                  native_J_sum_entries=seed_checks, all_source_N12_entries=len(output_labels) * len(columns))
    return Jsource, Jempty, Hsource, native, output_labels, counts


def boundary_matrices(q, columns, empty_labels, Jsource, Jempty, Hsource):
    terminal, first = q + 2, 2
    old = list(range(2, terminal))
    index = {label: j for j, label in enumerate(columns)}
    empty_index = {label: j for j, label in enumerate(empty_labels)}
    labels, terms, direct_columns, formula_columns = [], [], [], []

    def add(label, entries, h_entries, empty=None):
        labels.append(label)
        terms.append(entries)
        direct_columns.append([Jempty[row][empty] if empty is not None
                               else sum(scalar * Jsource[row][col] for col, scalar in entries) % P
                               for row in range(len(Jsource))])
        formula_columns.append([sum(scalar * Hsource[row][col] for col, scalar in h_entries) % P
                                for row in range(len(Hsource))])

    for t in old:
        r = min(s for s in old if s != t)
        for a in range(3):
            for b in range(3):
                new, base = index[t, terminal, a, b], index[t, r, a, b]
                add(dict(kind='old_shared_terminal_first_difference', t=t, r=r, a=a, b=b),
                    [(new, 1), (base, -1)], [(new, -1)])
    for s in old[1:]:
        for a in range(3):
            for b in range(3):
                new, base = index[terminal, s, a, b], index[terminal, first, a, b]
                add(dict(kind='terminal_shared_first_difference', s=s, a=a, b=b),
                    [(new, 1), (base, -1)], [(new, -1), (base, 1)])
    for a in range(3):
        col = index[terminal, first, a, 0]
        add(dict(kind='terminal_shared_output_zero', a=a), [(col, 1)], [(col, -1)])
    for a in range(3):
        entries = [(index[terminal, first, a, b], 1) for b in range(3)]
        add(dict(kind='terminal_long_empty', a=a), entries, [(col, -scalar) for col, scalar in entries],
            empty=empty_index[terminal, a])
    assert len(labels) == 18 * q - 3
    Jboundary = [list(row) for row in zip(*direct_columns)]
    formula = [list(row) for row in zip(*formula_columns)]
    assert Jboundary == formula, 'N13 boundary formula does not match the actual source extraction.'
    C = [[0] * len(labels) for _ in columns]
    for col, entries in enumerate(terms):
        for row, scalar in entries:
            C[row][col] = (C[row][col] + scalar) % P
    return Jboundary, C, labels


def calculate(q, mode):
    started = time.monotonic()
    m = q + 1
    times = sparse.factors(m, mode)
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, times)
    geometry = differences.check_geometry(m, A)
    M, inverse_certificate = schur.invert(A[-1])
    _, columns = schur.canonical_labels(m + 2)
    empty_labels = [(t, a) for t in range(2, m + 2) for a in range(3)]
    seed_labels = [(t, a) for t in range(2, q + 2) for a in range(3)]
    _, _, _, constant_records = differences.seed_coefficients(m, A)
    constants = {(r['t'], r['A']): r['c_tA'] for r in constant_records}
    Jsource, Jempty, Hsource, native, output_labels, counts = extraction(q, A, M, columns, empty_labels, seed_labels, constants)
    boundary, C, labels = boundary_matrices(q, columns, empty_labels, Jsource, Jempty, Hsource)
    binary = [row for row, label in enumerate(output_labels) if label[2] in (1, 2)]
    Jbinary = [boundary[row] for row in binary]
    certificate = incoming.matrix_certificate(Jbinary)
    h = certificate['rank_certificate']['rank']
    pivot_columns = certificate['rank_certificate']['nonzero_minor']['columns']
    first_group_spans = h == 6 * q and all(col < 9 * q for col in pivot_columns)
    if first_group_spans:
        selected = (f'exactly columns 0 through {6 * q - 1}' if pivot_columns == list(range(6 * q))
                    else f'columns {pivot_columns}')
        first_group_evidence = (f'Existing nonzero minor uses {selected}, within the first {9 * q} '
                                'generators; no new computation.')
    else:
        first_group_evidence = 'The existing full-matrix minor does not certify surjectivity of this subgroup.'
    native_binary = [[native[j][row] for row in binary] for j in range(2)]
    assert all((x + y) % P == 0 for row0, row1 in zip(*native_binary) for x, y in zip(row0, row1))
    O, source_geometry = residue.residue_matrix(m + 2, A, P)
    old_certificate = incoming.matrix_certificate(O)
    old_invertible = old_certificate['rank_certificate']['rank'] == len(O)
    Ccertificate = incoming.matrix_certificate(C)
    assert Ccertificate['rank_certificate']['rank'] == len(labels)
    boundary_pair = schur.matrix_product(O, C)
    record = dict(q=q, m=m, time_fixture=mode, prime=P, G=G, time_factors=times,
                  geometry=geometry, actual_source_geometry=source_geometry,
                  terminal_coefficient_inverse=inverse_certificate,
                  checks=counts, all_N13_boundary_entries_verified=True,
                  N13_entries_checked=len(boundary) * len(labels), native_N16_verified=True,
                  actual_source_matrix=old_certificate, actual_source_invertible_at_fixture=old_invertible,
                  boundary_generator_count=len(labels), boundary_source_coefficients=Ccertificate,
                  actual_boundary_pair_matrix_sha256=residue.matrix_hash(boundary_pair),
                  boundary_binary_extraction=certificate, boundary_binary_rank=h, binary_output_dimension=6 * q,
                  first_old_shared_group_generators=9 * q,
                  first_old_shared_group_binary_rank=6 * q if first_group_spans else None,
                  first_old_shared_group_spans_all_binary_outputs=first_group_spans,
                  first_old_shared_group_evidence=first_group_evidence,
                  boundary_binary_cokernel_dimension=6 * q - h,
                  native_component_one_binary_extraction=incoming.matrix_certificate(native_binary[0]),
                  native_component_two_binary_sha256=residue.matrix_hash(native_binary[1]),
                  quotient_outer_dimensions_if_source_independent=[6 + h, 6 * q - h] if old_invertible else None,
                  extraction_source_sha256=residue.matrix_hash(Jsource), extraction_empty_sha256=residue.matrix_hash(Jempty),
                  binary_output_labels=[output_labels[row] for row in binary], boundary_generator_labels=labels,
                  old_seed_labels=seed_labels, elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(q=q, m=m, time_fixture=mode, generators=len(labels), binary_rank=h,
                          binary_outputs=6 * q, actual_source_invertible=old_invertible,
                          seconds=record['elapsed_seconds'])), flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second terminal-extraction cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB terminal-extraction RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation = None
    try:
        for q in (2, 3, 4):
            cases.append(calculate(q, 'economic'))
        if time.monotonic() - started < 16:
            cases.append(calculate(3, 'independent'))
    except TimeoutError as error:
        limitation = str(error)
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Exact finite-field actual-source terminal-extraction checks and boundary ranks; no all-length theorem.',
                  formulas='N6 actual transformed residues; N7 interior and full long-empty rows; N10 analytically cancelled raw residues; N12/N13 actual boundary extraction; N14/N15 native seed components; N16 binary cancellation.',
                  cancellation='Matching Xc is removed before evaluation. Native c=d=0 values are independently checked with order-two actual source jets against matching-divided conjugate-word first jets.',
                  limitations='Ranks are at the stated fixtures. No native independence modulo the full boundary span or flat limit, and no incoming or all-length independence, is inferred. Nonzero modular minors lift after denominator clearing; modular deficiencies alone do not give rational upper bounds.',
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
