#!/usr/bin/env python3
"""Exact q=4 certificate of the specific LC53--54 collision projection.

Reuse the saved actual leading/first-jet ordinary evaluations. Independently
extract the normalized transverse observation from the actual source words:
on L_(q,c)=0 put X(z)=P+z e0, extract the z^-2 coefficient, contract by
L_(q,d) diag(P)^-1 A_q^-1 e_d, d=c+1, and divide by P_c. Every transformed
column's z^-3 coefficient must vanish before this fixed covector is used.

The actual uncombined terms have pole order at most three, so regular
coefficients through z^1 suffice for z^-3 and z^-2. No intermediate discarded
power >=2 can reach -2, since the remaining total pole order is at most three.
The common product of the 3m earlier row forms clears the normalized output
to the paper's degree-(3m+2) binary polynomial. Twelve distinct line values
identify this degree-11 target at q=4; two further values per line are checked.

H consists of all 27 first-new jets V and the nine shared-new jets U at the
first earlier time. Project W9, S9, and the remaining U18 by the actual H
correction, then quotient by copied-old C120 and E-difference jets Z3.
The resulting 36-square minor is a finite-field certificate for this precise
projection, not an arbitrary-length theorem or a Lean-checked determinant.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import time
import traceback

import source24_last_time_coalescence as collision
import source24_schur as schur


P = collision.P
residue, sparse = collision.residue, collision.sparse
Q = 4
DIRECTION = (0, 1, 2)
LOW, HIGH = -3, 1
ZERO, ONE = {}, {0: 1}


def inverse(x):
    assert x % P, 'A required denominator is zero.'
    return pow(x % P, -1, P)


def add(a, b):
    result = a.copy()
    for k, value in b.items():
        result[k] = (result.get(k, 0) + value) % P
        if not result[k]:
            del result[k]
    return result


def scale(c, a):
    return {k: c * value % P for k, value in a.items() if c * value % P}


def subtract(a, b):
    return add(a, scale(-1, b))


def multiply(a, b):
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            if LOW <= i + j <= HIGH:
                result[i + j] = (result.get(i + j, 0) + x * y) % P
    return {k: value for k, value in result.items() if value}


def lidentity():
    return [[ONE if i == j else ZERO for j in range(3)] for i in range(3)]


def lmatmul(a, b):
    return [[add(add(multiply(a[i][0], b[0][j]), multiply(a[i][1], b[1][j])),
                 multiply(a[i][2], b[2][j])) for j in range(3)] for i in range(3)]


def lword(kernels, word):
    result = lidentity()
    for t in word:
        result = lmatmul(result, kernels[t])
    return result


def kernel_expansion(table, X, c=None):
    """Actual K and relative-time K' as Laurent series along X+z e0."""
    kernel, jet = [], []
    for a in range(3):
        v = [table[a][b] * X[b] % P for b in range(3)]
        dv = [table[a][0], 0, 0]
        L, L1 = sum(v) % P, table[a][0]
        ell, ell1 = sum(v[b] * DIRECTION[b] for b in range(3)) % P, 0
        krow, jrow = [], []
        for b in range(3):
            if a == c:
                assert L == 0 and L1 == 1 and ell1 == 0
                k = {-1: v[b], 0: dv[b]}
                j = {-2: -ell * v[b],
                     -1: v[b] * DIRECTION[b] - ell * dv[b],
                     0: dv[b] * DIRECTION[b]}
            else:
                unit = inverse(L)
                k0 = v[b] * unit % P
                k1 = (dv[b] - k0 * L1) * unit % P
                j0 = (v[b] * DIRECTION[b] - k0 * ell) * unit % P
                j1 = (dv[b] * DIRECTION[b] - k1 * ell - j0 * L1) * unit % P
                k, j = {0: k0, 1: k1}, {0: j0, 1: j1}
            krow.append({k: value % P for k, value in k.items() if value % P})
            jrow.append({k: value % P for k, value in j.items() if value % P})
        kernel.append(krow)
        jet.append(jrow)
    return kernel, jet


def actual_laurent_columns(tables, X, c):
    """Evaluate full actual E/F values and derivatives before taking differences."""
    q, new = len(tables) - 1, len(tables) - 1
    last = q - 1
    expansions = [kernel_expansion(table, X, c if t in (last, new) else None)
                  for t, table in enumerate(tables)]
    kernels = [item[0] for item in expansions]
    jet = expansions[new][1]
    products, derivatives = {}, {}
    for t in range(q + 1):
        for s in range(q + 1):
            if t == s:
                continue
            word = collision.order(q + 1, t, s)
            products[t, s] = lword(kernels, word)
            if new in word:
                position = word.index(new)
                derivatives[t, s] = lmatmul(lmatmul(lword(kernels, word[:position]), jet),
                                             lword(kernels, word[position + 1:]))
            else:
                derivatives[t, s] = [[ZERO for _ in range(3)] for _ in range(3)]
    values, prime = [], []
    for label in collision.labels(q + 1):
        if label[0] == 'E':
            _, t, a = label
            xa = {0: X[a], 1: int(a == 0)}
            values.append([multiply(xa, subtract(ONE if b == a else ZERO, kernels[t][a][b]))
                           for b in range(3)])
            prime.append([scale(-1, multiply(xa, jet[a][b])) if t == new else ZERO
                          for b in range(3)])
        else:
            _, t, s, a, b = label
            xa = {0: X[a], 1: int(a == 0)}
            prefactor = multiply(xa, kernels[t][a][b])
            prefactor_prime = multiply(xa, jet[a][b]) if t == new else ZERO
            complement = [subtract(ONE if j == b else ZERO, products[t, s][b][j])
                          for j in range(3)]
            values.append([multiply(prefactor, value) for value in complement])
            prime.append([subtract(multiply(prefactor_prime, complement[j]),
                                   multiply(prefactor, derivatives[t, s][b][j])) for j in range(3)])
    return values, prime


def line_points(tables, c, count):
    row = tables[-1][c]
    points, skipped, parameter = [], [], 0
    while len(points) < count:
        parameter += 1
        assert parameter < 10000
        X = [-(row[1] + row[2] * parameter) % P, 1, parameter]
        assert residue.dot(row, X, P) == 0
        bad = [(t, a) for t, table in enumerate(tables) for a in range(3)
               if not (t == len(tables) - 1 and a == c) and residue.dot(table[a], X, P) == 0]
        if not all(X) or bad:
            skipped.append(dict(parameter=parameter, zero_coordinates=not all(X), zero_row_forms=bad))
            continue
        points.append(X)
    return points, skipped


def selected_columns(matrix, columns):
    return [[row[j] for j in columns] for row in matrix]


def certificate(matrix):
    return dict(shape=[len(matrix), len(matrix[0])], sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def column_description(q, base, differences):
    descriptions = [dict(family='C' if j < len(collision.labels(q)) else 'W', **item)
                    for j, item in enumerate(base)]
    families = {'new_E_minus_last_old_E': 'Z', 'shared_new_minus_copied_last_shared': 'U',
                'first_new_minus_copied_last_first': 'V',
                'shared_new_last_minus_first_new_last': 'S'}
    descriptions += [dict(family=families[item['kind']], **item) for item in differences]
    return descriptions


def normalized_observation(tables, X, c, Ainv, base, differences):
    d = (c + 1) % 3
    values, prime = actual_laurent_columns(tables + [tables[-1]], X, c)
    rows = [values[item['terms'][0][0]] for item in base]
    for item in differences:
        left, right = [prime[index] for index, _ in item['terms']]
        rows.append([subtract(x, y) for x, y in zip(left, right)])
    assert all(not vector[j].get(-3, 0) for vector in rows for j in range(3)), 'Uncancelled cubic pole.'
    rho = [[entry.get(-2, 0) for entry in vector] for vector in rows]
    assert all(sum(vector) % P == 0 for vector in rho)
    Ld = residue.dot(tables[-1][d], X, P)
    covector = [Ld * inverse(X[j]) * Ainv[j][d] * inverse(X[c]) % P for j in range(3)]
    return [residue.dot(vector, covector, P) for vector in rho]


def formula_controls(tables, X, c, Ainv, H, descriptions, observed):
    """Independent LC33/49/52 and diagonal W/S formulas at each line point."""
    m, A = len(tables) - 1, tables[-1]
    d, e = (c + 1) % 3, (c + 2) % 3
    L = [residue.dot(row, X, P) for row in A]
    vc = [A[c][j] * X[j] % P for j in range(3)]
    ell = sum(vc[j] * DIRECTION[j] for j in range(3)) % P
    assert ell == sum(H[c][j] * L[j] for j in range(3)) % P
    K = [residue.ordinary_kernel(tables, t, X, P) for t in range(m)]
    full = residue.word_product(K, list(range(m)), P)
    fullrow = residue.matmul([vc], full, P)[0]
    qlambda = {a: sum(fullrow[j] * inverse(X[j]) * Ainv[j][a] for j in range(3)) % P
               for a in range(3)}
    checks = 0
    for item, value in zip(descriptions, observed):
        family = item['family']
        if family in ('C', 'Z'):
            expected = 0
        elif family == 'W':
            _, _, _, a, b = item['label']
            expected = -A[c][c] * X[c] * L[d] * qlambda[d] if a == b == c else 0
        elif family == 'V':
            _, t, _, a, b = item['left']
            if b != c:
                expected = 0
            else:
                tail = residue.word_product(K, [j for j in range(m) if j != t], P)
                vector = residue.matmul([vc], tail, P)[0]
                prefactor = tables[t][a][c] * X[a] * inverse(residue.dot(tables[t][a], X, P))
                expected = prefactor * (H[c][e] * L[e] * vector[d] - H[c][d] * L[d] * vector[e])
        elif family == 'U':
            _, _, s, a, b = item['left']
            if a != c:
                expected = 0
            else:
                tail = residue.word_product(K, [s] + [j for j in range(m) if j != s], P)
                expected = A[c][b] * (X[b] * (H[c][d] * L[d] * tail[b][c] + ell * tail[b][d])
                                      - ell * L[d] * Ainv[b][d])
        elif family == 'S':
            _, _, _, a, b = item['left']
            if a == b:
                if a != c:
                    expected = 0
                else:
                    directed = [vc[j] * (DIRECTION[j] - DIRECTION[c]) % P for j in range(3)]
                    row = residue.matmul([directed], full, P)[0]
                    contraction = sum(row[j] * inverse(X[j]) * Ainv[j][d] for j in range(3)) % P
                    expected = A[c][c] * L[d] * (X[c] * contraction - ell * Ainv[c][d])
            elif c == a:
                natural = A[a][b] * ell * (X[b] * sum(
                    residue.matmul([[A[b][j] * X[j] % P for j in range(3)]], full, P)[0][j]
                    * inverse(X[j]) * Ainv[j][b] for j in range(3)) - L[b] * Ainv[b][b])
                expected = natural if d == b else -natural
            elif c == b:
                natural = -A[a][b] * X[a] * ell * qlambda[a]
                expected = natural if d == a else -natural
            else:
                expected = 0
        else:
            raise AssertionError(family)
        assert value == expected % P, ('LC formula discrepancy', c, X, item, value, expected % P)
        checks += 1
    return checks


def interpolate_controls(points, rows, degree):
    nodes = [X[2] for X in points[:degree + 1]]
    vandermonde = 1
    for i, x in enumerate(nodes):
        for y in nodes[i + 1:]:
            vandermonde = vandermonde * (y - x) % P
    assert vandermonde
    weights = []
    for X, row in zip(points[degree + 1:], rows[degree + 1:]):
        x = X[2]
        interpolation = []
        for i, xi in enumerate(nodes):
            value = 1
            for j, xj in enumerate(nodes):
                if i != j:
                    value = value * (x - xj) * inverse(xi - xj) % P
            interpolation.append(value)
        for column, actual in enumerate(row):
            assert actual == sum(weight * rows[i][column] for i, weight in enumerate(interpolation)) % P
        weights.append(interpolation)
    return dict(degree=degree, interpolation_node_parameters=nodes,
                vandermonde_determinant=vandermonde, extra_point_weights=weights,
                independently_checked_extra_values=len(weights) * len(rows[0]))


def calculate(input_path):
    started = time.monotonic()
    input_bytes = input_path.read_bytes()
    source_hash = hashlib.sha256(input_bytes).hexdigest()
    saved = json.loads(input_bytes)
    case = next(case for case in saved['cases'] if case.get('case_label') == 'q4_relative_1_2')
    del saved, input_bytes
    assert case['q'] == Q and case['prime'] == P and case['G'] == [list(row) for row in collision.G]
    assert case['direction']['relative_u_derivative'] == 1 and case['direction']['relative_v_derivative'] == 2
    times = case['time_factors_at_collision']
    tables = sparse.coefficient_tables(collision.G, times[:-1])
    source_labels = collision.labels(Q + 1)
    base, differences, _ = collision.transformed_columns(Q, source_labels)
    assert json.loads(json.dumps(base)) == case['base_columns']
    assert json.loads(json.dumps(differences)) == case['vanishing_difference_columns']
    descriptions = column_description(Q, base, differences)
    ordinary = [left + right for left, right in zip(case['base_value_matrix'],
                                                   case['vanished_difference_derivative_matrix'])]
    assert residue.matrix_hash(case['base_value_matrix']) == case['base_leading_certificate']['sha256']
    assert residue.matrix_hash(ordinary) == case['specified_first_jet_certificate']['sha256']
    ordinary_controls = 0
    for i, X in enumerate(case['effect_points'][:3]):
        values, _ = collision.values_and_derivatives(tables + [tables[-1]], X,
                                                     case['direction']['new_u_derivative'],
                                                     case['direction']['new_v_derivative'])
        transformed = [values[item['terms'][0][0]] for item in base]
        transformed += [[collision.dual.sub(x, y) for x, y in zip(
            values[item['terms'][0][0]], values[item['terms'][1][0]])] for item in differences]
        for component in (0, 1):
            reconstructed = [row[component][0 if j < len(base) else 1]
                             for j, row in enumerate(transformed)]
            assert reconstructed == ordinary[2 * i + component]
            ordinary_controls += len(reconstructed)
    Ainv, A_certificate = schur.invert(tables[-1])
    H = residue.matmul([[tables[-1][a][b] * DIRECTION[b] % P for b in range(3)]
                        for a in range(3)], Ainv, P)
    observation, row_labels, line_records = [], [], []
    formula_count = cubic_count = 0
    degree = 3 * (Q - 1) + 2
    for c in range(3):
        points, skipped = line_points(tables, c, degree + 3)
        cleared_rows, clearing = [], []
        for X in points:
            observed = normalized_observation(tables, X, c, Ainv, base, differences)
            formula_count += formula_controls(tables, X, c, Ainv, H, descriptions, observed)
            cubic_count += 3 * len(descriptions)
            denom = 1
            for table in tables[:-1]:
                for row in table:
                    denom = denom * residue.dot(row, X, P) % P
            assert denom
            clearing.append(denom)
            cleared_rows.append([denom * x % P for x in observed])
        interpolation = interpolate_controls(points, cleared_rows, degree)
        observation += cleared_rows[:degree + 1]
        row_labels += [dict(sector=c, d=(c + 1) % 3, parameter=X[2], point=X,
                            earlier_denominator=clearing[i]) for i, X in enumerate(points[:degree + 1])]
        line_records.append(dict(sector=c, points=points, skipped=skipped,
                                 clearing_denominators=clearing, interpolation=interpolation,
                                 extra_observation_rows=cleared_rows[degree + 1:]))
    assert len(observation) == 36
    inherited = [j for j, item in enumerate(descriptions) if item['family'] in ('C', 'Z')]
    frame = [j for j, item in enumerate(descriptions) if item['family'] == 'V'] + [
        j for j, item in enumerate(descriptions) if item['family'] == 'U' and item['left'][2] == 0]
    remaining = [j for family in ('W', 'S', 'U') for j, item in enumerate(descriptions)
                 if item['family'] == family and j not in frame]
    assert (len(inherited), len(frame), len(remaining)) == (123, 36, 36)
    assert sorted(inherited + frame + remaining) == list(range(195))
    assert not any(x for row in selected_columns(observation, inherited) for x in row)
    OH, OY = selected_columns(observation, frame), selected_columns(observation, remaining)
    inverse_frame = schur.invert(OH)
    assert inverse_frame is not None, 'The specified H observation matrix is singular at this fixture.'
    OHinv, frame_certificate = inverse_frame
    corrections = schur.matrix_product(OHinv, OY)
    assert schur.matrix_product(OH, corrections) == OY
    ordinary_H = selected_columns(ordinary, frame)
    ordinary_Y = selected_columns(ordinary, remaining)
    projected = schur.matrix_difference(ordinary_Y, schur.matrix_product(ordinary_H, corrections))
    CZ = selected_columns(ordinary, inherited)
    CZ_certificate = certificate(CZ)
    assert CZ_certificate['rank_certificate']['rank'] == 123
    selected_base = CZ_certificate['rank_certificate']['nonzero_minor']['rows']
    CZminor = [CZ[i] for i in selected_base]
    CZinv, CZminor_certificate = schur.invert(CZminor)
    inherited_corrections = schur.matrix_product(CZinv, [projected[i] for i in selected_base])
    quotient = schur.matrix_difference(projected, schur.matrix_product(CZ, inherited_corrections))
    assert not any(x for i in selected_base for x in quotient[i])
    quotient_certificate = certificate(quotient)
    rank = quotient_certificate['rank_certificate']['rank']
    square_rows = quotient_certificate['rank_certificate']['nonzero_minor']['rows']
    square = [quotient[i] for i in square_rows]
    square_certificate = certificate(square)
    assert rank == 36, ('Specified projected quotient rank', rank)
    determinant = square_certificate['rank_certificate']['determinant_mod_prime']
    assert determinant
    mixed_matrix = [[observation[i][j] for j in frame + inherited + remaining] for i in range(36)]
    mixed_matrix += [[ordinary[i][j] for j in frame + inherited + remaining]
                     for i in selected_base + square_rows]
    factorized_minor = (frame_certificate['determinant_mod_prime'] *
                        CZminor_certificate['determinant_mod_prime'] * determinant) % P
    assert factorized_minor
    return dict(
        q=Q, m=Q - 1, prime=P, G=collision.G, time_factors_at_collision=times,
        relative_direction=DIRECTION, input_file=str(input_path), input_sha256=source_hash,
        saved_base_sha256=case['base_leading_certificate']['sha256'],
        saved_full_first_jet_sha256=case['specified_first_jet_certificate']['sha256'],
        saved_ordinary_row_labels=case['row_labels'], ordinary_points=case['effect_points'],
        source_column_labels=source_labels, transformed_column_descriptions=descriptions,
        observation_definition='D_earlier(P)/P_c * L_qd(P) * [z^-2]Y(P+z e0) * diag(P)^-1 A_q^-1 e_d; d=c+1 mod3.',
        Laurent_cutoff=dict(low=LOW, high=HIGH, maximum_actual_term_pole_order=3,
                            reason='To reach -3 or -2 with at most three total pole factors, no discarded exponent above 1 can contribute.'),
        terminal_table_inverse=Ainv, terminal_table_certificate=A_certificate, generator=H,
        observation_row_labels=row_labels, line_records=line_records,
        observation_matrix=observation, observation_sha256=residue.matrix_hash(observation),
        inherited_column_indices=inherited, frame_column_indices=frame, remaining_column_indices=remaining,
        frame_observation_matrix=OH, frame_observation_certificate=frame_certificate,
        remaining_observation_matrix=OY, frame_projection_coefficients=corrections,
        inherited_ordinary_certificate=CZ_certificate, inherited_minor_matrix=CZminor,
        inherited_minor_certificate=CZminor_certificate, inherited_projection_coefficients=inherited_corrections,
        projected_ordinary_values=projected, quotient_ordinary_values=quotient,
        quotient_certificate=quotient_certificate, Schur_row_indices=square_rows,
        Schur_matrix=square, Schur_certificate=square_certificate,
        mixed_minor=dict(shape=[195, 195], sha256=residue.matrix_hash(mixed_matrix),
                         columns=frame + inherited + remaining,
                         rows=dict(observation=list(range(36)), ordinary=selected_base + square_rows),
                         determinant_mod_prime=factorized_minor,
                         justification='Actual column corrections give block triangular diagonal OH, CZ_selected, and the recorded 36-square Schur matrix.'),
        controls=dict(saved_ordinary_actual_dual_entry_checks=ordinary_controls,
                      cubic_single_line_coefficients_checked_zero=cubic_count,
                      independent_LC_formula_entry_checks=formula_count,
                      O_C_and_O_Z_zero=True, frame_correction_identity=True,
                      inherited_correction_identity=True, all_line_denominators_and_coordinates_units=True,
                      interpolation_extra_entry_checks=sum(record['interpolation']['independently_checked_extra_values']
                                                           for record in line_records)),
        elapsed_seconds=time.monotonic() - started)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path,
                        default=Path(__file__).with_name('source24-last-time-coalescence-results.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or collision.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='One prescribed q=4 relative-(1,2) collision fixture; no parameter scan or all-q conclusion.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2))
    failure = None
    try:
        result['case'] = calculate(args.input)
        result['status'] = 'PASS: exact finite certificate of the specified LC53--54 projection.'
    except Exception as error:
        failure = error
        result['status'] = 'FAILED or incomplete bounded diagnostic; no full projection certificate asserted.'
        result['error'] = str(error)
        result['traceback'] = traceback.format_exc()
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = collision.maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Guarded calculation before JSON serialization; guard remains active during writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)
    case = result['case']
    print(json.dumps(dict(status=result['status'], frame_rank=36, inherited_rank=123,
                          Schur_rank=36, Schur_determinant=case['Schur_certificate']['rank_certificate']['determinant_mod_prime'],
                          mixed_minor_determinant=case['mixed_minor']['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'], maximum_rss_bytes=result['maximum_rss_bytes'])), flush=True)


if __name__ == '__main__':
    main()
