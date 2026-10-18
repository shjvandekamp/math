#!/usr/bin/env python3
"""Exact discovery for the binary inverse-product Laurent sublemma.

Computes Q_word and R_word, verifies their direct binary-product meaning,
and peels the nested independent pairs h_s,z*h_s from both baseline
columns. This is a smaller algebraic diagnostic, not a proof of the
multinomial source-family independence conjecture. rho=-1 is algebraic
only and is not a positive economic specialization.

Reproduce:
  nice -n 19 python3 exploration/binary_laurent.py --output exploration/binary-laurent-results.json
"""

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import signal


def clean(a):
    return {p: F(x) for p, x in a.items() if x}


def add(a, b):
    return clean({p: a.get(p, 0) + b.get(p, 0) for p in a.keys() | b.keys()})


def scale(c, a):
    return clean({p: c * x for p, x in a.items()})


def sub(a, b):
    return add(a, scale(-1, b))


def mul(a, b):
    answer = {}
    for p, x in a.items():
        for q, y in b.items():
            answer[p + q] = answer.get(p + q, F(0)) + x * y
    return clean(answer)


def shift(a, degree=1):
    return {p + degree: x for p, x in a.items()}


def evaluate(a, z):
    return sum(x * z ** p for p, x in a.items())


def scalar_functions(rho, c):
    H = {-1: 1 / ((rho - 1) * c), 0: (rho + 1) / (rho - 1), 1: rho * c / (rho - 1)}
    Q = {0: 1 / (rho - 1), 1: rho * c / (rho - 1)}
    R = {0: 1 / ((rho - 1) * c), 1: 1 / (rho - 1)}
    H, Q, R = clean(H), clean(Q), clean(R)
    assert add(R, shift(Q)) == shift(sub(H, {0: F(1)}))
    return H, Q, R


def word_functions(functions, word):
    product, Q, R = {0: F(1)}, {}, {}
    for i in word:
        H_i, Q_i, R_i = functions[i]
        Q = add(Q, mul(Q_i, product))
        R = add(R, mul(R_i, product))
        product = mul(product, H_i)
    assert add(R, shift(Q)) == shift(sub(product, {0: F(1)}))
    return Q, R


def nested_h(functions, rho, cs, s):
    answer, product = {}, {0: F(1)}
    for i in range(s):
        scalar = (cs[i] - cs[s]) / (cs[i] * cs[s] * (rho - 1) ** 2)
        local = {-1: F(1), 0: rho * (cs[i] + cs[s]), 1: rho * cs[i] * cs[s]}
        answer = add(answer, scale(scalar, mul(local, product)))
        product = mul(product, functions[i][0])
    return answer


def mmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def minverse(a):
    determinant = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    assert determinant
    return [[a[1][1] / determinant, -a[0][1] / determinant],
            [-a[1][0] / determinant, a[0][0] / determinant]]


def direct_binary_check(rho, cs, words, computed):
    points = (F(1, 7), F(2, 11))
    for z in points:
        kernels = [[[1 / (1 + c * z), c * z / (1 + c * z)],
                    [1 / (1 + rho * c * z), rho * c * z / (1 + rho * c * z)]] for c in cs]
        for word, (Q, R) in zip(words, computed):
            product = [[F(1), F(0)], [F(0), F(1)]]
            for i in word:
                product = mmul(product, kernels[i])
            inverse = minverse(product)
            q, r = evaluate(Q, z), evaluate(R, z)
            assert inverse == [[1 + q, -q], [-r / z, 1 + r / z]]
    return [str(z) for z in points]


def rank(matrix):
    a = [[F(x) for x in row] for row in matrix]
    current = 0
    for c in range(len(a[0])):
        found = next((i for i in range(current, len(a)) if a[i][c]), None)
        if found is None:
            continue
        a[current], a[found] = a[found], a[current]
        pivot = a[current][c]
        for i in range(current + 1, len(a)):
            factor = a[i][c] / pivot
            if factor:
                a[i] = [x - factor * y for x, y in zip(a[i], a[current])]
        current += 1
        if current == len(a):
            break
    return current


def serialize(a):
    return {str(p): str(x) for p, x in sorted(a.items())}


def check_case(rho, cs, family):
    rho, cs = F(rho), list(map(F, cs))
    m = len(cs)
    functions = [scalar_functions(rho, c) for c in cs]
    words = [[s] + [i for i in range(m) if i != s] for s in range(m)]
    computed = [word_functions(functions, word) for word in words]
    Qbase, Rbase = computed[0]
    hs, endpoints = {}, []
    for s in range(1, m):
        h = sub(computed[s][0], Qbase)
        assert h == nested_h(functions, rho, cs, s)
        assert sub(computed[s][1], Rbase) == scale(-1, shift(h))
        assert min(h) == -s and max(h) == s
        low = (cs[s - 1] - cs[s]) / ((rho - 1) ** (s + 1) * cs[s] * math.prod(cs[:s]))
        high = rho ** s * (cs[s - 1] - cs[s]) * math.prod(cs[:s - 1]) / (rho - 1) ** (s + 1)
        assert h[-s] == low and h[s] == high and low and high
        hs[s] = h
        endpoints.append(dict(s=s + 1, lowest_exponent=-s, highest_exponent=s,
                              lowest_coefficient=str(low), highest_coefficient=str(high)))
    remainders, peeling = [], []
    for column in (Qbase, Rbase):
        remainder = column.copy()
        coefficients = []
        for s in reversed(range(1, m)):
            h = hs[s]
            alpha = remainder.get(-s, F(0)) / h[-s]
            beta = remainder.get(s + 1, F(0)) / h[s]
            remainder = sub(sub(remainder, scale(alpha, h)), scale(beta, shift(h)))
            assert all(-s < p < s + 1 for p in remainder)
            coefficients.append(dict(s=s + 1, h_coefficient=str(alpha), zh_coefficient=str(beta)))
        assert set(remainder) <= {0, 1}
        reconstructed = remainder.copy()
        for entry in coefficients:
            h = hs[entry['s'] - 1]
            reconstructed = add(reconstructed, scale(F(entry['h_coefficient']), h))
            reconstructed = add(reconstructed, scale(F(entry['zh_coefficient']), shift(h)))
        assert reconstructed == column
        remainders.append(remainder)
        peeling.append(coefficients)
    remainder_matrix = [[column.get(p, F(0)) for column in remainders] for p in (0, 1)]
    determinant = remainder_matrix[0][0] * remainder_matrix[1][1] - remainder_matrix[0][1] * remainder_matrix[1][0]
    remainder_rank = rank(remainder_matrix)
    all_columns = [column for pair in computed for column in pair]
    coefficient_matrix = [[column.get(p, F(0)) for column in all_columns] for p in range(1 - m, m + 1)]
    exact_rank = rank(coefficient_matrix)
    assert exact_rank == 2 * (m - 1) + remainder_rank
    if m == 2:
        h = hs[1]
        assert Qbase == scale(cs[1] / (cs[0] - cs[1]), add(h, scale(rho * cs[0], shift(h))))
        assert Rbase == scale(1 / (cs[0] - cs[1]), add(h, scale(cs[0], shift(h))))
    points = direct_binary_check(rho, cs, words, computed)
    result = dict(m=m, rho=str(rho), c_family=family, c=[str(c) for c in cs],
                  coefficient_powers=list(range(1 - m, m + 1)),
                  original_column_count=2 * m, exact_coefficient_matrix_rank=exact_rank,
                  baseline_Q=serialize(Qbase), baseline_R=serialize(Rbase),
                  difference_endpoint_certificates=endpoints,
                  nested_h_formula_verified=True, R_difference_equals_negative_z_h=True,
                  peeling_coefficients_Q_and_R=peeling,
                  remainder_Q=serialize(remainders[0]), remainder_R=serialize(remainders[1]),
                  remainder_matrix=[[str(x) for x in row] for row in remainder_matrix],
                  remainder_determinant=str(determinant), remainder_rank=remainder_rank,
                  exact_reconstruction_after_peeling=True,
                  direct_binary_product_points=points,
                  all_s_first_word_products_verified=True)
    print(json.dumps({key: result[key] for key in
                      ('m', 'rho', 'c_family', 'exact_coefficient_matrix_rank', 'remainder_matrix', 'remainder_determinant')}), flush=True)
    return result


def deadline(_signum, _frame):
    raise TimeoutError('Binary Laurent diagnostic exceeded28 seconds.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(28)
    cases = [check_case(rho, list(range(1, m + 1)) if family == 'consecutive' else [2 ** i for i in range(m)], family)
             for rho in (2, -1) for family in ('consecutive', 'powers_of_two') for m in range(1, 7)]
    signal.alarm(0)
    result = dict(status='External exact Fraction Laurent calculation for a binary sublemma; not a Lean theorem.',
                  definitions=dict(H='(1+c_i*z)*(1+rho*c_i*z)/((rho-1)*c_i*z)',
                                   Q='(1+rho*c_i*z)/(rho-1)', R='(1+c_i*z)/((rho-1)*c_i)'),
                  word_rule='s first, then every other index in increasing order; baseline is1,2,...,m.',
                  inverse_product_identity='(K_word)^(-1)=[[1+Q_word,-Q_word],[-R_word/z,1+R_word/z]].',
                  peeling_rule='For s=m,...,2 subtract h_s using power1-s and z*h_s using power s, leaving powers0,1.',
                  cases=cases,
                  scope='Exact ranks concern only the displayed binary inverse-product Laurent columns. rho=-1 is not a positive economic specialization. No multinomial or all-m source-independence conclusion is asserted.')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
