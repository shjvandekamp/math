#!/usr/bin/env python3
"""Exact rational nullspace of the T=5 conic equation-(24) residue matrix.

This is an external exact certificate, not a Lean theorem. It uses the
original economic witness, not smaller or altered covariates:
  G[q][a] = 2**(q*a), beta=(0,1,2), x_t=3*(t+1)*log(2).

At the intersection of L(w)=X0+w*X1+w*w*X2 and L(z), use the rationally
normalized point (w*z,-w-z,1). Residues have zero component sum, so their
first two components give coordinates without dividing by a basis minor.
This changes residue coordinates by invertible row operations only.

The program clears each rational row, uses fraction-free Gaussian
elimination, obtains primitive integer nullvectors, and verifies every
entry of R*v=0 against the original Fraction matrix. A nonzero minor
modulo 1,000,003 supplies the matching rank lower bound. A 55-second
deadline stops an unexpectedly expensive approach.

Reproduce from the project directory:
  nice -n 19 python3 exploration/conic_residue_nullspace.py --output exploration/conic-nullspace-results.json
"""

import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools as it
import json
import math
from pathlib import Path
import signal
import time


T = 5
Q = 3
BLOCKS = (2, 3, 4)
PRIME = 1000003
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('residue_model', ROOT / 'exploration/source24_residue.py')
residue_model = importlib.util.module_from_spec(spec)
spec.loader.exec_module(residue_model)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def identity():
    return [[F(int(i == j)) for j in range(Q)] for i in range(Q)]


def matmul(a, b):
    columns = list(zip(*b))
    return [[dot(row, column) for column in columns] for row in a]


def kernel(A, t, point):
    answer = []
    for a in range(Q):
        denominator = dot(A[t][a], point)
        assert denominator != 0
        answer.append([F(A[t][a][i] * point[i], denominator) for i in range(Q)])
    assert all(sum(row) == 1 for row in answer)
    return answer


def rational_matrix():
    A = residue_model.transition_table(T, transition22=16)
    columns = [(t, s, a, b) for t in BLOCKS for s in BLOCKS if t != s
               for a in range(Q) for b in range(Q)]
    rows, labels, normalization = [], [], []
    for u, v in it.combinations(BLOCKS, 2):
        for c, d in it.product(range(Q), repeat=2):
            w, z = A[u][c][1], A[v][d][1]
            assert A[u][c] == [1, w, w * w]
            assert A[v][d] == [1, z, z * z]
            assert w != z
            point = [w * z, -w - z, 1]
            assert all(point)
            values = {(t, a): dot(A[t][a], point) for t in BLOCKS for a in range(Q)}
            assert {key for key, value in values.items() if value == 0} == {(u, c), (v, d)}
            U = [A[u][c][i] * point[i] for i in range(Q)]
            V = [A[v][d][i] * point[i] for i in range(Q)]
            assert sum(U) == sum(V) == 0
            assert U[0] * V[1] - U[1] * V[0] != 0
            matrices = {}
            for t in BLOCKS:
                if t == u:
                    matrices[t] = [[F(x) for x in U] if a == c else [F(0)] * Q
                                   for a in range(Q)]
                elif t == v:
                    matrices[t] = [[F(x) for x in V] if a == d else [F(0)] * Q
                                   for a in range(Q)]
                else:
                    matrices[t] = kernel(A, t, point)
            words = {}
            for t in BLOCKS:
                remaining = [s for s in BLOCKS if s != t]
                for s in remaining:
                    word = [s] + [r for r in remaining if r != s]
                    product = identity()
                    for r in word:
                        product = matmul(product, matrices[r])
                    words[t, s] = product
            first, second = [], []
            for t, s, a, b in columns:
                if (t == u and a != c) or (t == v and a != d):
                    first.append(F(0))
                    second.append(F(0))
                    continue
                prefactor = F(A[t][a][b] * point[b])
                if t not in (u, v):
                    prefactor /= values[t, a]
                vector = [-point[a] * prefactor * x for x in words[t, s][b]]
                assert sum(vector) == 0
                first.append(vector[0])
                second.append(vector[1])
            rows.extend((first, second))
            labels.extend(((u, c, v, d, 0), (u, c, v, d, 1)))
            normalization.append((z - w, U, V))
    assert len(rows) == len(columns) == 54
    return A, rows, labels, columns, normalization


def fraction_string(value):
    value = F(value)
    return f'{value.numerator}/{value.denominator}'


def matrix_hash(matrix):
    digest = hashlib.sha256()
    for row in matrix:
        digest.update((','.join(fraction_string(x) for x in row) + '\n').encode())
    return digest.hexdigest()


def clear_rows(matrix):
    integers, scales = [], []
    for row in matrix:
        denominator = math.lcm(*(x.denominator for x in row))
        cleared = [x.numerator * (denominator // x.denominator) for x in row]
        common = math.gcd(*cleared)
        assert common > 0
        integers.append([x // common for x in cleared])
        scales.append(F(denominator, common))
    assert all(F(x) == scale * y for row, original, scale in zip(integers, matrix, scales)
               for x, y in zip(row, original))
    return integers, scales


def fraction_free_echelon(matrix, started):
    a = [row[:] for row in matrix]
    rows, columns = len(a), len(a[0])
    pivot_columns = []
    current, previous = 0, 1
    max_bits = max(abs(x).bit_length() for row in a for x in row)
    for c in range(columns):
        if time.monotonic() - started > 50:
            raise TimeoutError('Exact elimination reached its bounded deadline.')
        found = next((i for i in range(current, rows) if a[i][c]), None)
        if found is None:
            continue
        if found != current:
            a[current], a[found] = a[found], a[current]
        pivot = a[current][c]
        for i in range(current + 1, rows):
            factor = a[i][c]
            for j in range(c + 1, columns):
                numerator = pivot * a[i][j] - factor * a[current][j]
                value, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError('Fraction-free division was not exact.')
                a[i][j] = value
                max_bits = max(max_bits, abs(value).bit_length())
            a[i][c] = 0
        previous = pivot
        pivot_columns.append(c)
        current += 1
        if current == rows:
            break
    return a, pivot_columns, max_bits


def primitive_integer_nullvectors(echelon, pivots):
    columns = len(echelon[0])
    free = [c for c in range(columns) if c not in pivots]
    vectors = []
    for f in free:
        vector = [F(0)] * columns
        vector[f] = F(1)
        for row in reversed(range(len(pivots))):
            c = pivots[row]
            vector[c] = -sum(F(echelon[row][j]) * vector[j] for j in range(c + 1, columns)) / echelon[row][c]
        denominator = math.lcm(*(x.denominator for x in vector))
        integer = [x.numerator * (denominator // x.denominator) for x in vector]
        common = math.gcd(*integer)
        integer = [x // common for x in integer]
        if integer[f] < 0:
            integer = [-x for x in integer]
        assert integer[f] > 0
        assert all(integer[g] == 0 for g in free if g != f)
        vectors.append(integer)
    return free, vectors


def cross_check_modular_coordinates(A, matrix, normalization):
    previous, _ = residue_model.residue_matrix(T, A, PRIME)
    for i, (scale, U, V) in enumerate(normalization):
        inverse_scale_square = pow(scale * scale % PRIME, -1, PRIME)
        for c in range(len(matrix[0])):
            for coordinate in (0, 1):
                value = matrix[2 * i + coordinate][c]
                reduced = value.numerator * pow(value.denominator, -1, PRIME) % PRIME
                expected = ((previous[2 * i][c] * U[coordinate]
                             + previous[2 * i + 1][c] * V[coordinate])
                            * inverse_scale_square % PRIME)
                assert reduced == expected
    return True


def run():
    started = time.monotonic()
    A, matrix, row_labels, column_labels, normalization = rational_matrix()
    assert cross_check_modular_coordinates(A, matrix, normalization)
    integers, scales = clear_rows(matrix)
    echelon, pivots, max_bits = fraction_free_echelon(integers, started)
    free, vectors = primitive_integer_nullvectors(echelon, pivots)
    assert len(pivots) == 51 and len(vectors) == 3
    assert all(dot(row, vector) == 0 for row in matrix for vector in vectors)
    assert all(dot(row, vector) == 0 for row in integers for vector in vectors)
    lower_bound = residue_model.modular_rank(integers, PRIME)
    assert lower_bound['rank'] == 51
    free_diagonal = [vector[f] for vector, f in zip(vectors, free)]
    assert all(free_diagonal)
    groups = []
    for vector, f in zip(vectors, free):
        support = [i for i, x in enumerate(vector) if x]
        counts = {str(a): sum(column_labels[i][2] == a for i in support) for a in range(Q)}
        groups.append(dict(free_column=f, support_size=len(support),
                           support_count_by_shared_outcome=counts,
                           maximum_coefficient_bits=max(abs(x).bit_length() for x in vector)))
    return dict(status='Exact rational external certificate; not Lean-verified.',
                T=T, witness='Original conic witness: G[q][a]=2^(q*a), beta=(0,1,2), x_t=3*(t+1)*log(2). No witness was changed.',
                matrix_definition='Equation-(24) first-level extension double-pole residues, with normalized cross points (w*z,-w-z,1), recorded in their first two components.',
                row_labels=row_labels, row_label_meaning='[u,c,v,d,component], u<v, blocks are zero-based coefficient-table indices2,3,4.',
                column_labels=column_labels, column_label_meaning='[t,s,a,b]: shared block t, divergent block s, shared outcome a, divergent outcome b.',
                exact_geometry=dict(cross_line_points=27, all_coordinates_nonzero=True,
                                    no_third_denominator_line=True,
                                    first_two_coordinates_independent_on_zero_sum_plane=True),
                rational_matrix_sha256=matrix_hash(matrix),
                integer_row_cleared_matrix_sha256=matrix_hash(integers),
                row_multipliers=[fraction_string(x) for x in scales],
                modular_coordinate_cross_check_with_previous_program=True,
                exact_rank=51, exact_nullity=3,
                primitive_integer_nullvectors=[[str(x) for x in vector] for vector in vectors],
                nullvectors_independent_certificate=dict(free_columns=free,
                    restricted_matrix='Diagonal in the listed basis order.',
                    positive_diagonal=[str(x) for x in free_diagonal]),
                exact_verification=dict(original_Fraction_matrix_times_each_nullvector_is_zero=True,
                                        integer_cleared_matrix_times_each_nullvector_is_zero=True),
                rank_lower_bound=dict(prime=PRIME, nonzero_minor=lower_bound['nonzero_minor']),
                coefficient_growth=dict(maximum_input_integer_bits=max(abs(x).bit_length() for row in integers for x in row),
                                        maximum_fraction_free_intermediate_bits=max_bits,
                                        nullvector_summaries=groups),
                interpretation='The original conic residue matrix has real rank51, not merely a modular rank loss. Through the proved-on-paper quotient/residue reduction, its extension rank is9+51=60 rather than63; this is an exceptional-witness failure, not a generic counterexample.',
                limitation='No direct 162-coordinate source-matrix nullvectors or new Lean theorem are supplied here; the source-family consequence uses research/SOURCE24_INDUCTION.md.')


def deadline(_signum, _frame):
    raise TimeoutError('Exact conic nullspace diagnostic exceeded55 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(55)
    result = run()
    signal.alarm(0)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(exact_rank=result['exact_rank'], exact_nullity=result['exact_nullity'],
                          free_columns=result['nullvectors_independent_certificate']['free_columns'],
                          coefficient_growth=result['coefficient_growth'],
                          verification=result['exact_verification']), indent=2), flush=True)


if __name__ == '__main__':
    main()
