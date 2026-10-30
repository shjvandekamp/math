#!/usr/bin/env python3
"""Exact order-two identity spot-checks near equal covariates.

Standard-library Fraction arithmetic in Q[epsilon]/(epsilon**3). These
checks do not certify a source-family rank, a determinant, or an all-T
independence theorem. Matrices act on row vectors. Block labels here are
zero-based ordered positions, rather than the time labels of the source.

Each block is a normalized softmax matrix with coefficient table
G diag(1,1+epsilon*delta_i,1+epsilon*zeta_i). In particular its epsilon**2
coefficient is retained; the checks do not replace the normalized matrix
by a linear approximation.

Reproduce from the project directory:
  nice -n 19 python3 exploration/coalescent_checks.py --output exploration/coalescent-checks.json
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import signal


Q = 3
ZERO = (F(0), F(0), F(0))
ONE = (F(1), F(0), F(0))


def constant(x):
    return F(x), F(0), F(0)


def sadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sneg(a):
    return tuple(-x for x in a)


def ssub(a, b):
    return sadd(a, sneg(b))


def smul(a, b):
    return tuple(sum(a[j] * b[k - j] for j in range(k + 1)) for k in range(3))


def sinv(a):
    assert a[0]
    return (1 / a[0], -a[1] / a[0] ** 2,
            a[1] ** 2 / a[0] ** 3 - a[2] / a[0] ** 2)


def sscale(scalar, a):
    return tuple(scalar * x for x in a)


def identity():
    return [[F(int(i == j)) for j in range(Q)] for i in range(Q)]


def sid():
    return [[ONE if i == j else ZERO for j in range(Q)] for i in range(Q)]


def mmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(Q)) for j in range(Q)] for i in range(Q)]


def smmul(a, b):
    answer = []
    for i in range(Q):
        row = []
        for j in range(Q):
            value = ZERO
            for k in range(Q):
                value = sadd(value, smul(a[i][k], b[k][j]))
            row.append(value)
        answer.append(row)
    return answer


def madd(a, b):
    return [[x + y for x, y in zip(arow, brow)] for arow, brow in zip(a, b)]


def mscale(scalar, a):
    return [[scalar * x for x in row] for row in a]


def msub(a, b):
    return madd(a, mscale(-1, b))


def mpow(a, n):
    answer = identity()
    for _ in range(n):
        answer = mmul(answer, a)
    return answer


def commutator(a, b):
    return msub(mmul(a, b), mmul(b, a))


def coefficient(a, degree):
    return [[x[degree] for x in row] for row in a]


def kernel_series(G, X, delta, zeta):
    tilts = (ZERO, (F(0), F(delta), F(0)), (F(0), F(zeta), F(0)))
    rows = []
    for a in range(Q):
        numerators = [sscale(F(G[a][i] * X[i]), sadd(ONE, tilts[i])) for i in range(Q)]
        denominator = tuple(sum(x[k] for x in numerators) for k in range(3))
        rows.append([smul(value, sinv(denominator)) for value in numerators])
    assert all(tuple(sum(x[k] for x in row) for k in range(3)) == ONE for row in rows)
    return rows


def source_products(kernels):
    products = {}
    blocks = list(range(len(kernels)))
    for t in blocks:
        for s in blocks:
            if s == t:
                continue
            word = [s] + [i for i in blocks if i not in (s, t)]
            product = sid()
            for i in word:
                product = smmul(product, kernels[i])
            products[t, s] = product
    return products


def source_images(kernels, X, a, b, products):
    answer = {}
    for (t, s), product in products.items():
        scalar = sscale(F(X[a]), kernels[t][a][b])
        answer[t, s] = [smul(scalar, ssub(ONE if i == b else ZERO, product[b][i]))
                        for i in range(Q)]
        assert all(sum(value[k] for value in answer[t, s]) == 0 for k in range(3))
    return answer


def vadd(a, b):
    return [sadd(x, y) for x, y in zip(a, b)]


def vsub(a, b):
    return [ssub(x, y) for x, y in zip(a, b)]


def edge(images, excluded, left, right):
    return vsub(images[excluded, left], images[excluded, right])


def triangle_prediction(K, derivatives, X, a, b, r, s, t, n):
    j, c = r + 1, n - t - 1
    U, V = msub(derivatives[s], derivatives[r]), msub(derivatives[t], derivatives[r])
    ell_U, ell_V = X[a] * U[a][b], X[a] * V[a][b]
    p = X[a] * K[a][b]
    k_j, k_before = mpow(K, j), mpow(K, j - 1)
    braces = msub(mscale(ell_V, commutator(U, k_j)),
                  mscale(ell_U, commutator(V, k_j)))
    braces = madd(braces, mscale(p, msub(mmul(mmul(V, k_before), U),
                                       mmul(mmul(U, k_before), V))))
    return mmul(braces, mpow(K, c))[b]


def prefix_prediction(K, derivatives, X, a, b, u, v, k, n):
    L, R = u, n - v - 1
    U = msub(derivatives[k + 1], derivatives[k])
    V = msub(derivatives[v], derivatives[u])
    ell_U, p = X[a] * U[a][b], X[a] * K[a][b]
    first = mmul(mmul(mmul(V, mpow(K, k)), U), mpow(K, L - k - 1))
    second = mmul(mmul(mmul(mpow(K, k + 1), U), mpow(K, L - k - 2)), V)
    braces = madd(mscale(-ell_U, commutator(V, mpow(K, L))),
                  mscale(p, msub(first, second)))
    return mmul(braces, mpow(K, R))[b]


def suffix_prediction(K, derivatives, X, a, b, u, v, k, n):
    L, R = u, n - v - 1
    t = v + 1 + k
    U = msub(derivatives[t + 1], derivatives[t])
    V = msub(derivatives[v], derivatives[u])
    ell_U, p = X[a] * U[a][b], X[a] * K[a][b]
    braces = msub(mscale(p, mmul(mmul(mpow(K, k), U), mpow(K, R - k - 2))),
                  mscale(ell_U, mpow(K, R - 1)))
    return mmul(commutator(V, mpow(K, L + 1)), braces)[b]


def check_triangles(G, X, n):
    directions = [(i + 1, (i + 1) ** 2 + 1) for i in range(n)]
    kernels = [kernel_series(G, X, delta, zeta) for delta, zeta in directions]
    K = coefficient(kernels[0], 0)
    derivatives = [coefficient(k, 1) for k in kernels]
    products = source_products(kernels)
    assert all(coefficient(k, 0) == K for k in kernels)
    assert any(x for kernel in kernels for row in coefficient(kernel, 2) for x in row)
    tested = nonzero = prefix_count = suffix_count = edge_count = 0
    prefix_nonzero = suffix_nonzero = 0
    for a in range(Q):
        for b in range(Q):
            images = source_images(kernels, X, a, b, products)
            for r in range(n - 2):
                s, t = r + 1, r + 2
                actual = vsub(vadd(edge(images, t, r, s), edge(images, r, s, t)),
                              edge(images, s, r, t))
                assert all(value[0] == value[1] == 0 for value in actual)
                expected = triangle_prediction(K, derivatives, X, a, b, r, s, t, n)
                assert [value[2] for value in actual] == expected
                tested += 1
                nonzero += any(expected)
            for u in range(n - 1):
                v = u + 1
                L, R = u, n - v - 1
                V = msub(derivatives[v], derivatives[u])
                p = X[a] * K[a][b]
                for t in range(n):
                    if t in (u, v):
                        continue
                    actual = edge(images, t, u, v)
                    before, after = L - int(t < u), R - int(t > v)
                    expected = mscale(p, mmul(commutator(V, mpow(K, before + 1)),
                                              mpow(K, after)))[b]
                    assert all(value[0] == 0 for value in actual)
                    assert [value[1] for value in actual] == expected
                    edge_count += 1
                for k in range(L - 1):
                    actual = vsub(edge(images, k, u, v), edge(images, k + 1, u, v))
                    expected = prefix_prediction(K, derivatives, X, a, b, u, v, k, n)
                    assert all(value[0] == value[1] == 0 for value in actual)
                    assert [value[2] for value in actual] == expected
                    prefix_count += 1
                    prefix_nonzero += any(expected)
                for k in range(R - 1):
                    t = v + 1 + k
                    actual = vsub(edge(images, t, u, v), edge(images, t + 1, u, v))
                    expected = suffix_prediction(K, derivatives, X, a, b, u, v, k, n)
                    assert all(value[0] == value[1] == 0 for value in actual)
                    assert [value[2] for value in actual] == expected
                    suffix_count += 1
                    suffix_nonzero += any(expected)
    return dict(n=n, G=G, effect_point=X, directions=directions,
                triangle_identities_checked=tested, nonzero_second_order_vectors=nonzero,
                first_order_edge_identities_checked=edge_count,
                prefix_grid_identities_checked=prefix_count,
                suffix_grid_identities_checked=suffix_count,
                nonzero_prefix_curvatures=prefix_nonzero,
                nonzero_suffix_curvatures=suffix_nonzero,
                coefficients_zero_and_one_cancel=True,
                order_two_matches_curvature_formula=True,
                normalized_kernel_second_order_terms_retained=True)


def determinant(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def determinant_derivative(a, derivative):
    value = F(0)
    for row in range(Q):
        replaced = [r[:] for r in a]
        replaced[row] = derivative[row][:]
        value += determinant(replaced)
    return value


def boundary_checks():
    G = ((1, 1, 1), (1, 1, 0), (1, 0, 1))
    X = (1, 1, 1)
    directions = ((0, 0), (1, 0), (0, 1))
    kernels = [kernel_series(G, X, *direction) for direction in directions]
    K = coefficient(kernels[0], 0)
    derivatives = [coefficient(k, 1) for k in kernels]
    expected_K = [[F(1, 3)] * 3, [F(1, 2), F(1, 2), F(0)], [F(1, 2), F(0), F(1, 2)]]
    expected_U = [[-F(1, 9), F(2, 9), -F(1, 9)], [-F(1, 4), F(1, 4), F(0)], [F(0)] * 3]
    expected_V = [[-F(1, 9), -F(1, 9), F(2, 9)], [F(0)] * 3, [-F(1, 4), F(0), F(1, 4)]]
    assert K == expected_K and derivatives[1] == expected_U and derivatives[2] == expected_V
    images = source_images(kernels, X, 0, 0, source_products(kernels))
    actual = vsub(vadd(edge(images, 2, 0, 1), edge(images, 0, 1, 2)), edge(images, 1, 0, 2))
    expected = [F(0), -F(1, 54), F(1, 54)]
    assert [value[2] for value in actual] == expected
    assert all(value[0] == value[1] == 0 for value in actual)
    assert triangle_prediction(K, derivatives, X, 0, 0, 0, 1, 2, 3) == expected
    assert determinant(K) == -F(1, 12)

    # Here t and s are the effect coordinates X1 and X2, not block labels.
    Xj = (1, 1, 2)
    Kj = coefficient(kernel_series(G, Xj, 0, 0), 0)
    Dt = coefficient(kernel_series(G, Xj, F(1, Xj[1]), 0), 1)
    Ds = coefficient(kernel_series(G, Xj, 0, F(1, Xj[2])), 1)
    tau = sum(Kj[i][i] for i in range(Q)) - 1
    d = determinant(Kj)
    tau_t, tau_s = sum(Dt[i][i] for i in range(Q)), sum(Ds[i][i] for i in range(Q))
    d_t, d_s = determinant_derivative(Kj, Dt), determinant_derivative(Kj, Ds)
    jacobian = tau_t * d_s - tau_s * d_t
    assert (tau, d) == (F(5, 12), -F(1, 12))
    assert (tau_t, tau_s, d_t, d_s) == (F(3, 16), F(7, 144), -F(1, 48), F(1, 144))
    assert jacobian == F(1, 432)
    return dict(G=G, boundary_not_positive=True,
                curvature=dict(effect_point=X, directions=directions, shared_outcome=0,
                               divergence_outcome=0, prefix_exponent_j=1, suffix_exponent_c=0,
                               value=[fraction_string(x) for x in expected],
                               original_source_column_series_verified=True,
                               determinant_K=fraction_string(determinant(K))),
                tau_d_jacobian=dict(effect_point=Xj, variables=['X1', 'X2'],
                                    tau=fraction_string(tau), d=fraction_string(d),
                                    derivatives=[fraction_string(x) for x in (tau_t, tau_s, d_t, d_s)],
                                    value=fraction_string(jacobian)),
                scope='The displayed G has zero entries; these exact boundary evaluations do not themselves provide a positive economic independence witness.')


def fraction_string(x):
    x = F(x)
    return f'{x.numerator}/{x.denominator}'


def deadline(_signum, _frame):
    raise TimeoutError('Coalescent identity checks exceeded55 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(55)
    matrices = [((1, 1, 1), (1, 2, 4), (1, 4, 17)),
                ((1, 1, 1), (1, 2, 5), (1, 7, 11))]
    points = [(1, 1, 2), (1, 2, 3), (2, 3, 5)]
    result = dict(status='Exact rational identity spot-checks; not rank or determinant certificates.',
                  coefficient_ring='Q[epsilon]/(epsilon^3)',
                  matrix_orientation='G[lag][outcome]; row-vector transitions.',
                  perturbation='A_i=G diag(1,1+epsilon*delta_i,1+epsilon*zeta_i).',
                  boundary_checks=boundary_checks(),
                  triangle_checks=[check_triangles(G, X, n)
                                   for G in matrices for X in points for n in range(3, 7)])
    signal.alarm(0)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(triangle_cases=len(result['triangle_checks']),
                          triangle_identities=sum(c['triangle_identities_checked'] for c in result['triangle_checks']),
                          first_order_edge_identities=sum(c['first_order_edge_identities_checked'] for c in result['triangle_checks']),
                          prefix_grid_identities=sum(c['prefix_grid_identities_checked'] for c in result['triangle_checks']),
                          suffix_grid_identities=sum(c['suffix_grid_identities_checked'] for c in result['triangle_checks']),
                          boundary=result['boundary_checks']), indent=2))


if __name__ == '__main__':
    main()
