#!/usr/bin/env python3
"""Exact symbolic first jet of the proposed endpoint formula, without CAS.

Work in Q[kappa,B][epsilon]/epsilon^4. Here A=4^m, B=3^m and
A/t=3A/(A-1)=4*kappa. This checks the supplied closed formula only;
its identification with actual source endpoints is a separate proof.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import resource
import signal
import sys
import time


class Poly:
    def __init__(self, value=0):
        data = value.terms if isinstance(value, Poly) else value if isinstance(value, dict) else {(0, 0): F(value)}
        self.terms = {key: F(coefficient) for key, coefficient in data.items() if coefficient}

    def __add__(self, other):
        data = dict(self.terms)
        for key, coefficient in Poly(other).terms.items():
            data[key] = data.get(key, F(0)) + coefficient
        return Poly(data)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        data = {}
        for (i, j), a in self.terms.items():
            for (k, l), b in Poly(other).terms.items():
                key = (i + k, j + l)
                data[key] = data.get(key, F(0)) + a * b
        return Poly(data)

    __rmul__ = __mul__

    def __truediv__(self, denominator):
        return self * (1 / F(denominator))

    def __pow__(self, power):
        result = Poly(1)
        for _ in range(power):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    def encode(self):
        return [dict(first_power=i, B_power=j, numerator=c.numerator, denominator=c.denominator)
                for (i, j), c in sorted(self.terms.items())]


ORDER = 3


class Jet:
    def __init__(self, value=0):
        data = value.coefficients if isinstance(value, Jet) else value if isinstance(value, list) else [value]
        self.coefficients = [Poly(data[i] if i < len(data) else 0) for i in range(ORDER + 1)]

    def __add__(self, other):
        return Jet([a + b for a, b in zip(self.coefficients, Jet(other).coefficients)])

    __radd__ = __add__

    def __neg__(self):
        return Jet([-a for a in self.coefficients])

    def __sub__(self, other):
        return self + -Jet(other)

    def __rsub__(self, other):
        return Jet(other) + -self

    def __mul__(self, other):
        rhs = Jet(other).coefficients
        return Jet([sum((self.coefficients[i] * rhs[n - i] for i in range(n + 1)), Poly())
                    for n in range(ORDER + 1)])

    __rmul__ = __mul__

    def inverse(self):
        a = self.coefficients
        assert set(a[0].terms) == {(0, 0)}, 'Only rational nonzero constant denominators are used.'
        constant = a[0].terms[(0, 0)]
        result = [Poly(1 / constant)]
        for n in range(1, ORDER + 1):
            result.append(-sum((a[i] * result[n - i] for i in range(1, n + 1)), Poly()) / constant)
        inverse = Jet(result)
        assert (self * inverse).coefficients == Jet(1).coefficients
        return inverse

    def __truediv__(self, other):
        return self * Jet(other).inverse()

    def __rtruediv__(self, other):
        return Jet(other) * self.inverse()


K, B = Poly({(1, 0): 1}), Poly({(0, 1): 1})


def determinant(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def closed_formula(z):
    U, T, g = sum(z, Jet()), sum((1 / value for value in z), Jet()), (2, 1, 1)
    matrix = [[Jet() for _ in range(3)] for _ in range(3)]
    for b in range(3):
        for c in range(3):
            if b != c:
                e = 3 - b - c
                factor = 2 * z[0] * g[b] / (3 * (2 * z[c] - z[e]))
                inner = U + z[c] - 4 * z[b] + Jet((B - 1) / 2) * (U + z[c] - z[b]) * (3 - z[b] * T)
                matrix[b][c] = factor * (Jet(B) * (3 - z[b] * T) - Jet(4 * K) * inner / (U + z[c]))
    return matrix


def clear_substitution(polynomial, degree):
    """Substitute kappa=3A/[4(A-1)], then multiply by [4(A-1)]^degree."""
    A = K  # The first formal variable now denotes A, not kappa.
    assert all(i <= degree for i, _ in polynomial.terms)
    return sum((coefficient * (3 * A) ** i * (4 * (A - 1)) ** (degree - i) * B ** j
                for (i, j), coefficient in polynomial.terms.items()), Poly())


def calculate():
    chi = B - F(3, 2) * K * (B - 1)
    p, ell, d = B * (3 * K - 2), chi - K, chi - 2 * K
    expected = [[Poly(), F(4, 3) * p, F(4, 3) * p],
                [F(2, 3) * d, Poly(), F(2, 3) * ell],
                [F(2, 3) * d, F(2, 3) * ell, Poly()]]
    expected_det = F(32, 27) * p * ell * d
    assert determinant(expected) == expected_det
    curves = ([Jet([1, 1]), Jet(1), Jet(1)], [Jet([1, 1]), Jet([1, 0, 1]), Jet([1, 0, 2])])
    records, matrices = [], []
    for name, curve in zip(('(1+epsilon,1,1)', '(1+epsilon,1+epsilon^2,1+2epsilon^2)'), curves):
        matrix = closed_formula(curve)
        assert all(entry.coefficients[0] == 0 for row in matrix for entry in row)
        first = [[entry.coefficients[1] for entry in row] for row in matrix]
        assert first == expected
        det = determinant(matrix).coefficients
        assert det[:3] == [Poly(), Poly(), Poly()] and det[3] == expected_det
        matrices.append(matrix)
        records.append(dict(curve=name, matrix_epsilon_coefficients=[[[coefficient.encode() for coefficient in entry.coefficients]
                        for entry in row] for row in matrix], determinant_coefficients=[value.encode() for value in det],
                        claimed_first_matrix_verified=True, claimed_determinant_coefficient_verified=True))
    assert any(matrices[0][i][j].coefficients[2] != matrices[1][i][j].coefficients[2] for i in range(3) for j in range(3))
    A = K
    assert clear_substitution(p, 1) == B * (A + 8)
    assert clear_substitution(ell, 1) == (3 * A - (A + 8) * B) / 2
    assert clear_substitution(d, 1) == (-3 * A - (A + 8) * B) / 2
    assert clear_substitution(expected_det, 3) == F(8, 27) * B * (A + 8) * (((A + 8) * B) ** 2 - 9 * A ** 2)
    return dict(status='PASS: exact symbolic expansion; no discrepancy in p or determinant coefficient.',
                ring='Q[kappa,B][epsilon]/(epsilon^4); encoded first_power is the power of kappa.',
                substitutions=dict(A='4^m', B='3^m', kappa='3A/[4(A-1)]', A_over_t='4*kappa'),
                curves=records, second_coefficients_differ=True,
                rational_factors=dict(p='B(A+8)/[4(A-1)]', ell='[3A-(A+8)B]/[8(A-1)]',
                    d='[-3A-(A+8)B]/[8(A-1)]', determinant='B(A+8)[(A+8)^2 B^2-9A^2]/[216(A-1)^3]'),
                nonvanishing_argument='For m>=1, A>=4 and B>=3. Thus p>0, ell<0, d<0: (A+8)B>=3A+24>3A. The displayed determinant coefficient is positive.',
                limitations='Exact algebra of the supplied closed formula only. No actual-source limit identification or uniform source independence is established here.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def rss():
        value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return value if sys.platform == 'darwin' else value * 1024

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or rss() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second /95MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = calculate()
    result.update(elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=rss(),
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2))
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'rational_factors', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)


if __name__ == '__main__':
    main()
