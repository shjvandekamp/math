#!/usr/bin/env python3
"""Kernel-complement first-jet test for an absorbing degeneration.

Let G_h=((1,1,1),(1,2,4),(1,4,h)), epsilon=1/h, and X2=epsilon*Z2.
Normalize the quotient columns by A_t(a,b), then divide E_a by
epsilon^[a=2] and Fbar_ab by epsilon^([a=2]+[b=2]). The resulting
columns have prefactors Z_a and Z_a*Z_b/L_ta, respectively, and are
analytic at epsilon=0.

This program evaluates M0 and M1 at fixed effect points modulo1000003,
finds a constant kernel basis N of M0, and ranks [M0_pivot_columns,M1*N].
It does NOT stack M0 and M1. Full rank would give a nonzero determinant
coefficient over the finite field, hence a nonzero rational determinant
after denominator clearing. No real leading-order equality is inferred
from the finite-field order. Only n=2,3 are considered.

Reproduce:
  nice -n 19 python3 exploration/absorbing_firstjet.py --output exploration/absorbing-firstjet-results.json
"""

import argparse
import importlib.util
import json
from pathlib import Path
import random
import signal


ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('sparse_model', ROOT / 'exploration/normalized_sparse_source24.py')
sparse = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sparse)
P = sparse.P
ZERO, ONE = (0, 0), (1, 0)


def add(a, b):
    return (a[0] + b[0]) % P, (a[1] + b[1]) % P


def sub(a, b):
    return (a[0] - b[0]) % P, (a[1] - b[1]) % P


def mul(a, b):
    return a[0] * b[0] % P, (a[0] * b[1] + a[1] * b[0]) % P


def scale(c, a):
    return c * a[0] % P, c * a[1] % P


def inverse(a):
    assert a[0] % P
    inv = pow(a[0], -1, P)
    return inv, -a[1] * inv * inv % P


def identity():
    return [[ONE if i == j else ZERO for j in range(3)] for i in range(3)]


def mmul(a, b):
    answer = []
    for i in range(3):
        row = []
        for j in range(3):
            value = ZERO
            for k in range(3):
                value = add(value, mul(a[i][k], b[k][j]))
            row.append(value)
        answer.append(row)
    return answer


def values_at_point(times, Z):
    x, y, z = Z
    kernels, inverses = [], []
    for u, v in times:
        numerators = [[(x, 0), (u * y % P, 0), (0, v * z % P)],
                      [(x, 0), (2 * u * y % P, 0), (0, 4 * v * z % P)],
                      [(x, 0), (4 * u * y % P, 0), (v * z % P, 0)]]
        denominators = [tuple(sum(value[k] for value in row) % P for k in (0, 1))
                        for row in numerators]
        if any(value[0] == 0 for value in denominators):
            return None
        inv = [inverse(value) for value in denominators]
        kernel = [[mul(value, inv[a]) for value in row] for a, row in enumerate(numerators)]
        assert all(tuple(sum(value[k] for value in row) % P for k in (0, 1)) == ONE
                   for row in kernel)
        kernels.append(kernel)
        inverses.append(inv)
    n = len(times)
    values = []
    for t in range(n):
        for a in range(3):
            values.append([scale(Z[a], sub(ONE if i == a else ZERO, kernels[t][a][i]))
                           for i in range(3)])
    for t in range(n):
        for s in range(n):
            if t == s:
                continue
            product = identity()
            for block in [s] + [i for i in range(n) if i not in (s, t)]:
                product = mmul(product, kernels[block])
            for a in range(3):
                for b in range(3):
                    prefactor = scale(Z[a] * Z[b] % P, inverses[t][a])
                    values.append([mul(prefactor, sub(ONE if i == b else ZERO, product[b][i]))
                                   for i in range(3)])
    assert all(sum(value[k] for value in vector) % P == 0 for vector in values for k in (0, 1))
    return values


def rref_kernel(matrix):
    a = [row[:] for row in matrix]
    nrows, ncols = len(a), len(a[0])
    rank, pivots = 0, []
    for c in range(ncols):
        found = next((i for i in range(rank, nrows) if a[i][c]), None)
        if found is None:
            continue
        a[rank], a[found] = a[found], a[rank]
        inv = pow(a[rank][c], -1, P)
        a[rank] = [x * inv % P for x in a[rank]]
        for i in range(nrows):
            if i == rank:
                continue
            factor = a[i][c]
            if factor:
                a[i] = [(x - factor * y) % P for x, y in zip(a[i], a[rank])]
        pivots.append(c)
        rank += 1
        if rank == nrows:
            break
    free = [c for c in range(ncols) if c not in pivots]
    vectors = []
    for f in free:
        vector = [0] * ncols
        vector[f] = 1
        for i, c in enumerate(pivots):
            vector[c] = -a[i][f] % P
        vectors.append(vector)
    assert all(sum(x * y for x, y in zip(row, vector)) % P == 0
               for row in matrix for vector in vectors)
    assert all(vector[f] == int(i == j) for i, vector in enumerate(vectors)
               for j, f in enumerate(free))
    return pivots, free, vectors


def finite_epsilon_control(times, Z):
    """Check the normalization against the original normalized columns at h17."""
    G = ((1, 1, 1), (1, 2, 4), (1, 4, 17))
    epsilon = pow(17, -1, P)
    X = (Z[0], Z[1], Z[2] * epsilon % P)
    original = sparse.evaluated_columns(sparse.coefficient_tables(G, times), X)
    if original is None:
        return False
    # The finite-epsilon normalized values can also be computed from the
    # effective coefficient table with X=Z: its third column is multiplied
    # by epsilon except in row2, where h*epsilon=1.
    effective = ((1, 1, epsilon), (1, 2, 4 * epsilon % P), (1, 4, 1))
    normalized = sparse.evaluated_columns(sparse.coefficient_tables(effective, times), Z)
    assert normalized is not None
    labels = sparse.column_labels(len(times))
    for label, before, after in zip(labels, original, normalized):
        exponent = int(label[2] == 2) if label[0] == 'E' else int(label[3] == 2) + int(label[4] == 2)
        factor = pow(17, exponent, P)
        assert [factor * value % P for value in before] == after
    return True


def check_case(n, mode):
    times = sparse.factors(n, mode)
    target = 3 * n * (3 * n - 2)
    rng = random.Random(910240 + n)
    points, M0, M1 = [], [], []
    controls = 0
    while len(points) < target + 16:
        Z = (1, rng.randrange(1, P), rng.randrange(1, P))
        values = values_at_point(times, Z)
        if values is None:
            continue
        if controls < 3:
            controls += finite_epsilon_control(times, Z)
        points.append(Z)
        for component in (0, 1):
            M0.append([value[component][0] for value in values])
            M1.append([value[component][1] for value in values])
    pivots, free, vectors = rref_kernel(M0)
    jet = [[row0[c] for c in pivots]
           + [sum(x * y for x, y in zip(row1, vector)) % P for vector in vectors]
           for row0, row1 in zip(M0, M1)]
    echelon = sparse.general.Echelon(target, P)
    for i, row in enumerate(jet):
        echelon.add(row, i)
    result = dict(n=n, source_panel_T=n + 2, mode=mode, prime=P,
                  time_factors=times, effect_point_seed=910240 + n, effect_points=points,
                  columns=target, M0_rank=len(pivots), M0_nullity=len(free),
                  kernel_complement_first_jet_rank=echelon.rank,
                  full_first_jet_rank=echelon.rank == target,
                  M0_pivot_columns=pivots, M0_free_columns=free,
                  kernel_vectors_sparse=[[[j, x] for j, x in enumerate(vector) if x] for vector in vectors],
                  kernel_verification_M0N_zero=True,
                  constant_basis_invertibility='Kernel vectors restrict to the identity on free coordinates; adjoining the original pivot-column standard vectors is invertible.',
                  first_jet_matrix_definition='[M0[:,pivot_columns], M1*N]; N is the listed constant kernel basis of M0.',
                  M0_sha256=sparse.general.matrix_hash(M0), M1_sha256=sparse.general.matrix_hash(M1),
                  first_jet_sha256=sparse.general.matrix_hash(jet),
                  nonzero_first_jet_minor=dict(size=echelon.rank, rows=echelon.rows,
                      columns=echelon.columns, determinant_mod_prime=echelon.determinant,
                      order='Rows and columns in listed order; rows2j,2j+1 are components0,1 at pointj.'),
                  finite_h17_normalization_comparisons=controls,
                  conditional_finite_field_leading_exponent=len(free) if echelon.rank == target else None,
                  scope='Full rank would certify a nonzero rational determinant for this finite n after denominator clearing. A non-full first jet does not exclude a higher-order determinant term.')
    print(json.dumps({key: result[key] for key in
                      ('n', 'mode', 'columns', 'M0_rank', 'M0_nullity', 'kernel_complement_first_jet_rank', 'full_first_jet_rank')}), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Absorbing first-jet test exceeded43 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(43)
    cases = [check_case(n, mode) for mode in ('independent', 'economic') for n in (2, 3)]
    signal.alarm(0)
    result = dict(status='External finite-field first-jet exploration; no Lean or all-n theorem.',
                  degeneration='G_h=((1,1,1),(1,2,4),(1,4,h)), epsilon=1/h, X=(Z0,Z1,epsilon*Z2).',
                  column_normalization='First divide F by A_t(a,b), then divide Fbar by epsilon^([a=2]+[b=2]); divide E_a by epsilon^[a=2].',
                  normalized_limit='Prefactors become Z_a and Z_a*Z_b/L_ta; epsilon remains only in K and L.',
                  legitimate_jet_test='Choose independent columns of M0 and a constant basis N of ker(M0); test [M0_piv,M1*N]. Stacking M0 and M1 is not used.',
                  finite_field_lift='All constant denominators are nonzero modulo the prime. A nonzero determinant coefficient modulo the prime would imply the cleared rational determinant is not identically zero over the reals; its real leading order need not equal its finite-field leading order.',
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
