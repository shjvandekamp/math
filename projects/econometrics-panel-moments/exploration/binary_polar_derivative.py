#!/usr/bin/env python3
"""Exact checks of the auxiliary even-length polar derivative calculation.

The kernel is solved over constant rational coefficients in the Laurent
coefficient matrix. We compare its two actual product derivatives with the
proposed closed expressions at three rational points, and verify the Laurent
quotient reductions coefficient by coefficient. These finite checks support
the paper derivation; they do not prove all-length source independence.

Reproduce:
  python3 exploration/binary_polar_derivative.py --output exploration/binary-polar-derivative-results.json
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import binary_laurent as b


def mmul(a, c):
    return [[sum(a[i][k] * c[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def madd(a, c):
    return [[x + y for x, y in zip(ar, cr)] for ar, cr in zip(a, c)]


def kernel_with_last(columns, m, p, q):
    """Solve for a constant kernel vector with prescribed last-word entries."""
    n = 2 * m - 2
    rows = [[col.get(k, F(0)) for col in columns[:n]] +
            [-p * columns[n].get(k, F(0)) - q * columns[n + 1].get(k, F(0))]
            for k in range(1 - m, m + 1)]
    for c in range(n):
        pivot = next(r for r in range(c, len(rows)) if rows[r][c])
        rows[c], rows[pivot] = rows[pivot], rows[c]
        value = rows[c][c]
        rows[c] = [x / value for x in rows[c]]
        for r in range(len(rows)):
            if r != c:
                value = rows[r][c]
                rows[r] = [x - value * y for x, y in zip(rows[r], rows[c])]
    assert all(not any(row) for row in rows[n:])
    vector = [rows[c][-1] for c in range(n)] + [F(p), F(q)]
    total = {}
    for scalar, col in zip(vector, columns):
        total = b.add(total, b.scale(scalar, col))
    assert not total
    return vector


def case(m, rho, eta):
    cs = [F(5)**i for i in range(m)]
    e, c, d = cs[0], cs[-2], cs[-1]
    functions = [b.scalar_functions(rho, x) for x in cs]
    words = [[s] + [i for i in range(m) if i != s] for s in range(m)]
    columns = [col for word in words for col in b.word_functions(functions, word)]
    kernel = [kernel_with_last(columns, m, 1, 0), kernel_with_last(columns, m, 0, 1)]
    hs = {s: b.nested_h(functions, rho, cs, s) for s in range(1, m)}

    def project(poly):
        out = poly.copy()
        for s in reversed(range(1, m)):
            h = hs[s]
            out = b.sub(out, b.scale(out.get(-s, F(0)) / h[-s], h))
            out = b.sub(out, b.scale(out.get(s + 1, F(0)) / h[s], b.shift(h)))
        assert set(out) <= {0, 1}
        return out

    U, V = b.word_functions(functions, list(range(m - 1)))
    _, Qc, Rc = functions[-2]
    _, Qe, _ = functions[0]
    Rd = functions[-1][2]
    shifts = [project(b.shift(U, -1)), project(b.shift(U, 1)), project(b.shift(V, -1)), project(b.shift(V, 1))]
    expected = [b.sub({0: -d}, b.scale(d, Qc)), b.sub({1: F(-1)}, b.scale(1/d, Qc)),
                b.sub({0: F(-1)}, b.scale(rho*d, Rc)), b.sub({1: -1/(rho*d)}, b.scale(1/(rho*d), Rc))]
    assert shifts == expected
    np = b.scale(rho / ((rho-1)**2*d), b.mul({-1: F(1), 0: d},
                b.add(b.sub(b.mul({0: F(1), 1: d-c}, U), b.scale(c, V)), {1: d-c})))
    nq_laurent = b.scale(rho/(rho-1), b.mul(Rd, b.sub(b.scale(d, V), U)))
    P = project(np)
    Q = b.sub(project(nq_laurent), b.scale((eta-1)/((rho-1)*eta*e), Qe))
    assert P == b.scale(rho*c/(rho-1), Rc)
    assert Q == {0: (1/c-(eta-1)/(eta*e))/(rho-1)**2, 1: rho/(eta*(rho-1)**2)}
    determinant = P.get(0, F(0))*Q.get(1, F(0))-P.get(1, F(0))*Q.get(0, F(0))
    expected_det = rho/(eta*(rho-1)**4)*(rho-eta+(c/e)*(eta-1))
    assert determinant == expected_det and determinant
    points = (F(1, 7), F(2, 11), F(-1, 13))
    for z in points:
        kernels = [[[F(0), 1/(1+k*x*z), k*x*z/(1+k*x*z)] for k in (eta, F(1), rho)] for x in cs]
        zero = [[F(0)]*3 for _ in range(3)]
        derivatives = [zero for _ in range(m)]
        derivative = [[F(0)]*3 for _ in range(3)]
        r = 1/(1+rho*d*z)
        derivative[2] = [r, -r*kernels[-1][2][1], -r*kernels[-1][2][2]]
        derivatives[-1] = derivative
        values = []
        for word in words:
            product = [[F(int(i == j)) for j in range(3)] for i in range(3)]
            tangent = [[F(0)]*3 for _ in range(3)]
            for t in word:
                tangent = madd(mmul(tangent, kernels[t]), mmul(product, derivatives[t]))
                product = mmul(product, kernels[t])
            values.extend((tangent[1][2], -z*tangent[2][2]))
        D = F(1)
        for H, _, _ in functions:
            D /= b.evaluate(H, z)
        actual = [sum(x*y for x, y in zip(v, values))/D for v in kernel]
        Z1 = (eta-1)/(rho-1)*(1+rho*e*z)/(1+eta*e*z)
        predicted = [b.evaluate(np, z), b.evaluate(nq_laurent, z)-b.evaluate(Rd, z)*Z1]
        assert actual == predicted, (m, rho, eta, z, actual, predicted)
        z0 = -1/(eta*e)
        row0_correction = (b.evaluate(Rd, z)-b.evaluate(Rd, z0))*Z1
        assert row0_correction == (eta-1)/((rho-1)*eta*e)*b.evaluate(Qe, z)
    return dict(m=m, rho=str(rho), eta=str(eta), c=list(map(str, cs)),
                constant_kernel_basis=[list(map(str, v)) for v in kernel],
                constant_kernel_exactly_verified=True,
                four_shift_reductions_coefficientwise_verified=True,
                P=b.serialize(P), Q=b.serialize(Q), quotient_determinant=str(determinant),
                expected_determinant=str(expected_det),
                direct_product_derivative_points=list(map(str, points)),
                direct_product_derivatives_match_closed_expressions=True,
                row_zero_pole_subtraction_checked=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = [case(m, F(rho), F(eta)) for m in (2, 4, 6, 8) for rho, eta in ((2, 3), (3, 2))]
    result = dict(status='External exact rational checks supporting a paper proof; not a Lean theorem.',
                  scope='Auxiliary shared-new polar derivative only; the full regular Schur complement remains open.',
                  boundary='Only the last old block leaks to state0, t1=0,t2=1, with row0 odds eta*c_i*z.',
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases), exact_kernel_and_Laurent_checks='passed',
                         product_derivative_comparisons=6*len(cases), all_quotient_determinants_nonzero=True)))


if __name__ == '__main__':
    main()
