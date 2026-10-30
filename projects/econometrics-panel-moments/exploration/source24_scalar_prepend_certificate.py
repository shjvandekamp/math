#!/usr/bin/env python3
"""Exact base and one independent first-jet check for scalar prepend induction.

Builds integer polynomial kernels for G=I+11^T on X=(-1-z,1,z).
Certifies the augmented m=3 determinant modulo 17, exact integer axis
values, and the m=3->4 leading determinant coefficient from actual dual
polynomial products. The arbitrary-length result uses the paper induction.
"""

import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
import time


G = ((2, 1, 1), (1, 2, 1), (1, 1, 2))
X = ((-1, -1), (1,), (0, 1))
FACTORS = ((3, 4), (4, 3), (5, 9))
PRIME = 17


def add(a, b):
    result = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        result[i] += x
    for i, x in enumerate(b):
        result[i] += x
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def scale(a, scalar):
    return [scalar * x for x in a]


def mul(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def sum_polys(items):
    result = [0]
    for item in items:
        result = add(result, item)
    return result


def row_product(row, matrix):
    return [sum_polys(mul(row[a], matrix[a][b]) for a in range(3)) for b in range(3)]


def block(u, v):
    d = (1, u, v)
    A = [[G[a][b] * d[b] for b in range(3)] for a in range(3)]
    L = [sum_polys(scale(X[b], A[a][b]) for b in range(3)) for a in range(3)]
    H = [mul(X[a], mul(L[(a + 1) % 3], L[(a + 2) % 3])) for a in range(3)]
    B = [[scale(mul(X[b], mul(L[(a + 1) % 3], L[(a + 2) % 3])), A[a][b])
          for b in range(3)] for a in range(3)]
    return L, H, B


def augmented_columns(factors):
    blocks = [block(u, v) for u, v in factors]
    columns = []
    for t, (_, H, _) in enumerate(blocks):
        row = X
        for s, (_, _, B) in enumerate(blocks):
            if s != t:
                row = row_product(row, B)
        # X1=1 in this chart, so output-coordinate division is exact.
        columns.extend(mul(row[1], H[a]) for a in range(3))
    row = X
    for _, _, B in blocks:
        row = row_product(row, B)
    columns.append(row[1])
    degree = 3 * len(factors)
    assert all(len(c) <= degree + 1 for c in columns)
    return columns


def coefficient_matrix(columns, degree, p):
    return [[(column[j] if j < len(column) else 0) % p for column in columns]
            for j in range(degree + 1)]


def determinant_no_swaps(matrix, p):
    work = [row[:] for row in matrix]
    pivots = []
    for j in range(len(work)):
        pivot = work[j][j]
        assert pivot, 'This certificate uses the displayed no-swap pivots.'
        pivots.append(pivot)
        for i in range(j + 1, len(work)):
            factor = work[i][j] * pow(pivot, -1, p) % p
            work[i] = [(x - factor * y) % p for x, y in zip(work[i], work[j])]
    determinant = 1
    for pivot in pivots:
        determinant = determinant * pivot % p
    return determinant, pivots


def determinant(matrix, p):
    work = [row[:] for row in matrix]
    answer = 1
    for j in range(len(work)):
        k = next(i for i in range(j, len(work)) if work[i][j])
        if k != j:
            work[j], work[k] = work[k], work[j]
            answer = -answer
        pivot = work[j][j]
        answer = answer * pivot % p
        for i in range(j + 1, len(work)):
            factor = work[i][j] * pow(pivot, -1, p) % p
            work[i] = [(x - factor * y) % p for x, y in zip(work[i], work[j])]
    return answer % p


def prepend_first_coefficient(old_columns):
    # Actual first-order B_new for u=1+eps, v=1+2eps.
    # L_new,a = X_a + eps*(ell+d_a*X_a) on the terminal line.
    ell, d = [1, 2], (0, 1, 2)
    Ldot = [add(ell, scale(X[a], d[a])) for a in range(3)]
    prod_other = [mul(X[(a + 1) % 3], X[(a + 2) % 3]) for a in range(3)]
    dot_other = [add(mul(Ldot[(a + 1) % 3], X[(a + 2) % 3]),
                     mul(X[(a + 1) % 3], Ldot[(a + 2) % 3])) for a in range(3)]
    Bdot = [[scale(mul(X[b], add(scale(prod_other[a], d[b]), dot_other[a])),
                   G[a][b]) for b in range(3)] for a in range(3)]
    U = old_columns[-1]
    Cdot = [mul(U, mul(X[a], dot_other[a])) for a in range(3)]
    row = row_product(X, Bdot)
    for u, v in FACTORS:
        row = row_product(row, block(u, v)[2])
    Zdot = row[1]
    delta = mul(mul(X[0], X[1]), X[2])
    # Standard new-column order: C0, C1, C2, inherited deletions, Z.
    # After subtracting C0 and 4*C0, the indicated three columns vanish
    # at order zero. Their derivatives determine the order-three term.
    transformed = [mul(delta, U),
                   add(Cdot[1], scale(Cdot[0], -1)),
                   add(Cdot[2], scale(Cdot[0], -1))]
    transformed.extend(scale(mul(delta, column), 4) for column in old_columns[:-1])
    transformed.append(add(Zdot, scale(Cdot[0], -4)))
    assert len(transformed) == 13 and all(len(c) <= 13 for c in transformed)
    return coefficient_matrix(transformed, 12, PRIME)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('28-second cap')))
    signal.alarm(28)
    start = time.monotonic()
    columns = augmented_columns(FACTORS)
    matrix = coefficient_matrix(columns, 9, PRIME)
    base_det, pivots = determinant_no_swaps(matrix, PRIME)
    assert pivots == [7, 11, 3, 3, 16, 12, 11, 16, 14, 3]
    assert base_det == 9
    U = columns[-1]
    axes = [sum(c * (-1) ** j for j, c in enumerate(U)), U[9], U[0]]
    assert axes == [-699840, -259200, -38880]
    first_matrix = prepend_first_coefficient(columns)
    first_det = determinant(first_matrix, PRIME)
    predicted = 2 * pow(4, 9, PRIME) * base_det
    for axis in axes:
        predicted = predicted * axis % PRIME
    assert first_det == predicted % PRIME != 0
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert rss <= 95 * 1024 * 1024
    result = dict(schema_version=1, status='external exact integer/modular certificate',
                  scope='m=3 augmented base and m=3-to-4 determinant first coefficient; all-m theorem is paper induction',
                  common_G=G, factors=FACTORS, chart='X=(-1-z,1,z), output1/X1',
                  polynomial_column_order='(time,state) lexicographic, then full product',
                  integer_polynomial_columns=columns, prime=PRIME, coefficient_matrix=matrix,
                  no_swap_pivots=pivots, determinant_mod_prime=base_det,
                  axis_representatives=[[0, 1, -1], [-1, 0, 1], [-1, 1, 0]],
                  integer_full_product_axis_values=axes,
                  prepend_first_coefficient_matrix=first_matrix,
                  prepend_order=3, prepend_first_coefficient_mod_prime=first_det,
                  predicted_prepend_coefficient_mod_prime=predicted % PRIME,
                  coefficient_matrix_sha256=hashlib.sha256(json.dumps(matrix).encode()).hexdigest(),
                  elapsed_seconds=time.monotonic() - start, maximum_rss_bytes=rss)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('base determinant mod17:', base_det, '; first prepend coefficient:', first_det)
    print('axis values:', axes)


if __name__ == '__main__':
    main()
