#!/usr/bin/env python3
"""Finite first time jets of new-pole/axis observations at equal old times.

Old factors are (1+e*tau_t, 1+e*nu_t), new factors stay (2,3).
Only ordinary points on new lines/axes are used; no coincident old-node
residue chart is evaluated. The induced derivative is measured modulo
the leading image on its actual coefficient kernel.
"""
import argparse
import json
from pathlib import Path
import signal
import time

import source24_raw_quotient as quotient

P = quotient.P
dual, incoming, schur = quotient.dual, quotient.incoming, quotient.schur
G = ((1, 2, 7), (1, 5, 3), (1, 11, 13))


def const(matrix):
    return [[(x % P, 0) for x in row] for row in matrix]


def row_product(row, matrix):
    result = []
    for j in range(3):
        value = dual.ZERO
        for k in range(3):
            value = dual.add(value, dual.mul(row[k], matrix[k][j]))
        result.append(value)
    return result


def scale(scalar, row):
    return [dual.mul(scalar, x) for x in row]


def coalesced_matching(A0, ANinv, columns):
    """Restrict Xc=0 first; all nonsingular old row-c factors are exactly zero."""
    blocks, N = list(range(2, len(A0))), len(A0) - 1
    rows = []
    for u in blocks[:-1]:
        for c, X in enumerate(((0, 7, -2), (-3, 0, 1), (-11, 1, 0))):
            J = {}
            for t in blocks:
                J[t] = []
                for a in range(3):
                    if a == c:
                        J[t].append([0, 0, 0])
                    else:
                        f = X[a] * quotient.inverse(quotient.residue.dot(A0[t][a], X, P)) % P
                        J[t].append(quotient.raw.row_scale(f, A0[t][a]))
            product = quotient.cached_product(J)
            row = []
            for label in columns:
                t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
                word = quotient.order(blocks, t, s)
                if t == u:
                    divided = quotient.raw.row_scale(A0[t][a][b], product(word)[b]) if a == c else [0, 0, 0]
                elif a == c:
                    # The extra departure factor vanishes before coalescing.
                    divided = [0, 0, 0]
                else:
                    pos = word.index(u)
                    before, after = product(word[:pos]), product(word[pos + 1:])
                    f = X[a] * A0[t][a][b] * quotient.inverse(quotient.residue.dot(A0[t][a], X, P)) * before[b][c]
                    divided = quotient.raw.row_scale(f, quotient.row_product(A0[u][c], after))
                row.append(sum(divided[j] * ANinv[j][c] for j in range(3)) % P)
            rows.append(row)
    return rows


def calculate(q, old_directions=None):
    """Optional {source block: (tau, nu)} map; old source blocks are 2,...,q+1."""
    N, blocks = q + 2, list(range(2, q + 3))
    A0 = [[list(row) for row in G] for _ in range(q + 3)]
    A0[N] = [[row[0], 2 * row[1], 3 * row[2]] for row in G]
    if old_directions is None:
        directions = {t: (t - 1, (t - 1) ** 2) for t in blocks if t != N}
    else:
        assert set(old_directions) == set(blocks[:-1])
        directions = {t: tuple(old_directions[t]) for t in blocks[:-1]}
        assert all(len(pair) == 2 and all(isinstance(x, int) for x in pair)
                   for pair in directions.values())
    A = {t: [[(G[a][j] % P, G[a][j] * (0, *directions[t])[j] % P)
              for j in range(3)] for a in range(3)] for t in directions}
    A[N] = const(A0[N])
    ANinv, _ = schur.invert(A0[N])
    _, columns = quotient.raw.labels(q)

    def values(X, new_state=None):
        J, denominators = {}, {}
        for t in blocks:
            if t == N and new_state is not None:
                continue
            denominators[t] = []
            J[t] = []
            for a in range(3):
                den = dual.ZERO
                for j in range(3):
                    den = dual.add(den, dual.scale(X[j], A[t][a][j]))
                denominators[t].append(den)
                J[t].append(scale(dual.scale(X[a], dual.inverse(den)), A[t][a]))
        cache = {(): dual.identity()}

        def product(word):
            key = tuple(word)
            if key not in cache:
                value = dual.identity()
                for t in word:
                    value = dual.mmul(value, J[t])
                cache[key] = value
            return cache[key]

        tail = const(ANinv)
        if new_state is not None:
            LN = [quotient.residue.dot(row, X, P) for row in A0[N]]
            tail = const([[ANinv[i][j] * LN[j] % P for j in range(3)] for i in range(3)])
        result = []
        for label in columns:
            t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
            if new_state is None:
                f = dual.mul(dual.scale(X[a], A[t][a][b]),
                             dual.inverse(denominators[t][a]))
                B = scale(f, product(quotient.order(blocks, t, s))[b])
            elif t == N:
                B = scale((X[a] * A0[N][a][b] % P, 0),
                          product(quotient.order(blocks, t, s))[b]) if a == new_state else [dual.ZERO] * 3
            elif b == new_state:
                f = dual.mul(dual.scale(X[a] * X[b], A[t][a][b]),
                             dual.inverse(denominators[t][a]))
                B = scale(f, row_product(A[N][b], product([u for u in blocks if u not in (t, N)])))
            else:
                B = [dual.ZERO] * 3
            result.append(row_product(B, tail))
        return result

    new_rows, axis_rows, samples, controls = [], [], [], 0
    for c in range(3):
        points, _ = quotient.line_points(A0, c, 3 * q + 3)
        samples.append(dict(kind='new_line', state=c, points=points))
        for X in points:
            actual = values(X, c)
            control, _, _ = quotient.new_line_residue(A0, ANinv, X, c, columns)
            assert [[v[0] for v in row] for row in actual] == control
            controls += 3 * len(columns)
            for d in range(3):
                if d != c:
                    new_rows.append([row[d] for row in actual])
    for d in range(3):
        points, _ = quotient.axis_points(A0, d, 2 * q + 4)
        samples.append(dict(kind='axis', state=d, points=points))
        for X in points:
            actual = values(X)
            control = quotient.boundary_C(A0, ANinv, X, columns)
            assert [[v[0] for v in row] for row in actual] == control
            controls += 3 * len(columns)
            axis_rows.append([row[d] for row in actual])

    def certificate(rows):
        M0 = [[x[0] for x in row] for row in rows]
        M1 = [[x[1] for x in row] for row in rows]
        _, free, kernel = dual.rref_kernel(M0)
        R = [list(row) for row in zip(*kernel)]
        assert not any(x for row in schur.matrix_product(M0, R) for x in row)
        derivative = schur.matrix_product(M1, R)
        augmented = [left + right for left, right in zip(M0, derivative)]
        leading, total = incoming.matrix_certificate(M0), incoming.matrix_certificate(augmented)
        r0, r1 = (x['rank_certificate']['rank'] for x in (leading, total))
        return dict(leading=leading, derivative_hash=quotient.residue.matrix_hash(M1),
                    right_kernel=kernel, right_free_columns=free,
                    leading_and_kernel_derivative=total,
                    leading_rank=r0, induced_derivative_rank=r1-r0,
                    certified_generic_rank_lower_bound=r1)

    new = certificate(new_rows)
    combined = certificate(new_rows + axis_rows)
    eta0 = coalesced_matching(A0, ANinv, columns)
    combined_rows = new_rows + axis_rows
    A0rows = [[x[0] for x in row] for row in combined_rows]
    A1rows = [[x[1] for x in row] for row in combined_rows]
    leading_full = A0rows + eta0
    _, joint_free, joint_kernel = dual.rref_kernel(leading_full)
    joint_R = [list(row) for row in zip(*joint_kernel)]
    assert not any(x for row in schur.matrix_product(leading_full, joint_R) for x in row)
    derivatives = schur.matrix_product(A1rows, joint_R)
    observed = incoming.matrix_certificate([a + d for a, d in zip(A0rows, derivatives)])
    full_leading_certificate = incoming.matrix_certificate(leading_full)
    partial_gain = observed['rank_certificate']['rank'] - combined['leading_rank']
    mixed_bound = full_leading_certificate['rank_certificate']['rank'] + partial_gain
    assert mixed_bound <= len(columns)
    matching_indices = [j for j, col in enumerate(columns) if col['s'] == N and col['a'] != col['b']]
    eta_certificate = incoming.matrix_certificate([[row[j] for j in matching_indices] for row in eta0])
    mixed = dict(matching_leading_hash=quotient.residue.matrix_hash(eta0),
                 matching_incoming_unequal_state_certificate=eta_certificate,
                 matching_incoming_unequal_state_columns=matching_indices,
                 full_leading=full_leading_certificate,
                 joint_right_kernel=joint_kernel, joint_free_columns=joint_free,
                 observed_new_axis_derivative=observed,
                 additional_certified_rank=partial_gain, certified_generic_rank_lower_bound=mixed_bound,
                 explanation='Left cokernel observations (L_new_axis,0) kill the full leading matrix; matching derivatives are unnecessary for this lower bound.')
    result = dict(q=q, prime=P, G=G, new_factors=[2, 3], directions=directions,
                  columns=columns, samples=samples, leading_control_component_checks=controls,
                  new_poles=new, new_poles_and_axes=combined,
                  matching_leading_with_new_axis_first_jet=mixed)
    print(json.dumps(dict(q=q, new=[new['leading_rank'], new['induced_derivative_rank']],
                          combined=[combined['leading_rank'], combined['induced_derivative_rank']],
                          mixed=[full_leading_certificate['rank_certificate']['rank'], partial_gain, mixed_bound])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases, limitation = time.monotonic(), [], None

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for q in (2, 3, 4, 5, 6):
            cases.append(calculate(q))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite coalesced old-time first jets of actual raw quotient observations.',
                  limitation='Only finite generic lower bounds. A deficient first jet is not a rational dependence or an upper bound for the full parameter family.',
                  construction='Rank M0 plus rank of M1 on ker M0 modulo im M0, computed as rank [M0 | M1 R].',
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
