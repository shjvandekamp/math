#!/usr/bin/env python3
"""Exact finite first jets of the actual conic outgoing transverse matrix.

Use CT2 directly in the moving conic chart X=(xy,-x-y,1). At each fixed
old pole y=q_ta compute ordinary-y residues of the entire actual word,
as dual numbers in x. No row-zero pivot is discarded: the induced kernel
map is L*M'(0)*R for full left/right kernels of M(0).

These are finite certificates for an auxiliary block, not the full source
Schur matrix or an all-even-length theorem.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming

P = incoming.P
dual, residue, schur = incoming.dual, incoming.residue, incoming.schur
ZERO = (0, 0)
TIMES = (2, 5, 11, 23, 47, 97)


def inverse(a):
    v = pow(a[0], -1, P)
    return v, -a[1] * v * v % P


def kernel(nodes, t, y, pole=None):
    rows = []
    for a, q in enumerate(nodes[t]):
        numerator = [(0, y), (-q * y % P, -q % P), (q * q % P, 0)]
        if pole is not None and t == pole[0]:
            if a != pole[1]:
                rows.append([ZERO] * 3)
                continue
            # Residue of 1/(q-y) at y=q is -1; q-x remains invertible.
            denominator_inverse = dual.scale(-1, inverse((q, -1 % P)))
        else:
            denominator_inverse = inverse((q * (q - y) % P, -(q - y) % P))
        rows.append([dual.mul(v, denominator_inverse) for v in numerator])
    return rows


def word(n, s):
    return [s] + [t for t in range(n) if t != s]


def product(kernels, order):
    value = dual.identity()
    for t in order:
        value = dual.mmul(value, kernels[t])
    return value


def scalar_columns(product_matrix, y):
    # P*h_x = x*P[:,0] - y*P[:,2].
    ph = [dual.add(dual.mul((0, 1), row[0]), dual.scale(-y, row[2]))
          for row in product_matrix]
    return [dual.scale(y, ph[0]), dual.mul((-y % P, -1 % P), ph[1]), ph[2]]


def check_recurrence(nodes):
    """Independently compare the affine and zero-sum recurrences at ordinary y."""
    n = len(nodes)
    checks = 0
    for y in (1, 13, 101):
        assert all(q != y for row in nodes for q in row)
        kernels = [kernel(nodes, t, y) for t in range(n)]
        data = []
        for t, (r, beta, gamma) in enumerate(nodes):
            f = beta * pow(beta - y, -1, P) % P
            u = (r * pow(r - y, -1, P) - f) % P
            d = (gamma * pow(gamma - y, -1, P) - f) % P
            h = y * pow(beta * (beta - y), -1, P) % P
            B = (beta + gamma - y) * pow(beta * gamma, -1, P) % P
            data.append((f, u, d, h, B))
        for s in range(n):
            order = word(n, s)
            matrix = product(kernels, order)
            f, a, g, D = 0, 0, 0, 1
            for t in order:
                ft, u, d, h, B = data[t]
                f, a, g = ((ft + d * f) % P,
                           (h + d * B * f) % P,
                           (d * g + u * a + pow(nodes[t][1] - y, -1, P)
                            + d * pow(y, -1, P) * f) % P)
                D = D * d % P
            assert (matrix[1][2][0], matrix[1][0][1], matrix[1][2][1]) == (f, a, g)
            Dprime = n * pow(y, -1, P)
            for left, right in zip(order, order[1:]):
                Dprime += data[left][4] * data[right][1] * pow(data[right][2], -1, P)
            Dprime = D * Dprime % P
            assert (matrix[2][2][0] - matrix[1][2][0]) % P == D
            assert (matrix[2][2][1] - matrix[1][2][1]) % P == Dprime
            checks += 5
    return checks


def calculate(n, alpha):
    nodes = [[a * b % P for a in alpha] for b in TIMES[:n]]
    flat = [q for row in nodes for q in row]
    assert len(set(flat)) == 3 * n and all(flat)
    M0, M1 = [], []
    for u in range(n):
        for c, y in enumerate(nodes[u]):
            kernels = [kernel(nodes, t, y, (u, c)) for t in range(n)]
            row = []
            for s in range(n):
                row.extend(scalar_columns(product(kernels, word(n, s)), y))
            M0.append([entry[0] for entry in row])
            M1.append([entry[1] for entry in row])
    leading = incoming.matrix_certificate(M0)
    expected = 3 * n if n % 2 else 3 * n - 2
    assert leading['rank_certificate']['rank'] == expected
    result = dict(n=n, prime=P, alpha=alpha, old_times=TIMES[:n],
                  old_nodes=nodes, all_old_nodes_distinct_nonzero=True,
                  row_order='(t,a), block then state, zero-based',
                  column_order='(s,j), move-first block then outgoing state, zero-based',
                  leading=leading, derivative_sha256=residue.matrix_hash(M1),
                  direct_recurrence_scalar_checks=check_recurrence(nodes),
                  full_old_pole_rows_retained=True)
    if n % 2 == 0:
        _, right_free, right = dual.rref_kernel(M0)
        _, left_free, left = dual.rref_kernel([list(row) for row in zip(*M0)])
        assert len(right) == len(left) == 2
        assert all(v[3 * s] == 0 for v in right for s in range(n))
        R = [list(row) for row in zip(*right)]
        assert not any(x for row in schur.matrix_product(M0, R) for x in row)
        assert not any(x for row in schur.matrix_product(left, M0) for x in row)
        correction = schur.matrix_product(schur.matrix_product(left, M1), R)
        determinant = (correction[0][0] * correction[1][1]
                       - correction[0][1] * correction[1][0]) % P
        certificate = incoming.matrix_certificate(correction)
        result.update(right_kernel=right, right_free_columns=right_free,
                      left_kernel=left, left_free_columns=left_free,
                      correction_matrix=correction, correction=certificate,
                      correction_determinant_mod_prime=determinant,
                      first_jet_resolves_both_directions=determinant != 0,
                      geometric_alpha_relation=alpha[0] * alpha[2] == alpha[1] ** 2)
    print(json.dumps(dict(n=n, alpha=alpha, leading_rank=expected,
                          correction_rank=result.get('correction', {}).get('rank_certificate', {}).get('rank'),
                          correction_determinant=result.get('correction_determinant_mod_prime'))), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases, limitation = time.monotonic(), [], None

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second cutoff')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB RSS cutoff')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for alpha in ((1, 2, 3), (1, 2, 4)):
            for n in (2, 3, 4, 6):
                cases.append(calculate(n, alpha))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite actual conic outgoing transverse first-jet certificates.',
                  construction='Dual-number ordinary-y residues of the complete CT2 functions; correction uses full left/right kernels, including state-zero rows.',
                  limitations='Only the recorded auxiliary-block fixtures are certified. This is not the full source Schur matrix, a uniform even-length proof, or a real upper bound inferred from modular deficiency.',
                  elapsed_seconds=time.monotonic() - started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
