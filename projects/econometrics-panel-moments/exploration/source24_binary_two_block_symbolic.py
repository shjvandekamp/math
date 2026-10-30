#!/usr/bin/env python3
"""One exact symbolic check of the Pro54 two-block binary base.

Use Q(a,c,r), beta=1, G=I+11^T, X=(1,-r,r), v=(0,-r,r).
Completed rows are h_tb=X_b e_b K_t K_o and j_tc=mu_tc v K_o,
in their actual moved-first/omitted-factor order. Derive their binary
values and first weak coefficient [delta]C_2 directly from these words.
Check four kappa identities, two gauges, the proposed raw weak formulas,
ordinary-r residues, and Q=(8T)^-1 diag(a^-3,4a^-3,c^-3,4c^-3) N.

All arithmetic uses standard-library sparse rational polynomials, known
denominator factors, and exact polynomial cross multiplication. Every
accepted factor cancellation is checked by multiplication. There is no
numeric specialization, parameter sweep, symbolic package, or determinant
simplification. beta is restored by homogeneity of every weak coefficient.
One guarded execution: 26 calculation seconds, 28 total seconds, 95 MiB.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback


VARIABLES = ['a', 'c', 'r']
ZERO_MONOMIAL = (0, 0, 0)
FACTORS = {}
FACTOR_IDS = {}
COUNTS = dict(polynomial_products=0, exact_factor_cancellations=0,
              rational_normalizations=0, cross_multiplications=0,
              maximum_polynomial_terms=0)


def clean(poly):
    answer = {power: Fraction(value) for power, value in poly.items() if value}
    COUNTS['maximum_polynomial_terms'] = max(COUNTS['maximum_polynomial_terms'], len(answer))
    return answer


def constant(value):
    return {} if not value else {ZERO_MONOMIAL: Fraction(value)}


def add(left, right):
    answer = dict(left)
    for power, value in right.items():
        answer[power] = answer.get(power, 0) + value
    return clean(answer)


def scale(poly, value):
    return clean({power: coefficient * value for power, coefficient in poly.items()})


def multiply(left, right):
    COUNTS['polynomial_products'] += 1
    answer = {}
    for p, x in left.items():
        for q, y in right.items():
            power = tuple(u + v for u, v in zip(p, q))
            answer[power] = answer.get(power, 0) + x * y
    return clean(answer)


def power(poly, exponent):
    answer = constant(1)
    for _ in range(exponent):
        answer = multiply(answer, poly)
    return answer


def exact_divide(numerator, denominator):
    """Lexicographic multivariate long division; accept only zero remainder."""
    assert denominator
    work, quotient = dict(numerator), {}
    lead_d = max(denominator)
    while work:
        lead_n = max(work)
        if all(x >= y for x, y in zip(lead_n, lead_d)):
            p = tuple(x - y for x, y in zip(lead_n, lead_d))
            q = work[lead_n] / denominator[lead_d]
            quotient[p] = quotient.get(p, 0) + q
            work = add(work, scale(multiply({p: Fraction(1)}, denominator), -q))
        else:
            # With one divisor, a leading monomial it cannot divide already
            # proves a nonzero remainder; no remaining terms need division.
            return None
    quotient = clean(quotient)
    assert multiply(quotient, denominator) == numerator
    return quotient


def register_factor(poly):
    assert poly
    leading = poly[max(poly)]
    monic = scale(poly, 1 / leading)
    key = tuple(sorted(monic.items()))
    if key not in FACTOR_IDS:
        factor_id = 'f' + str(len(FACTOR_IDS))
        FACTOR_IDS[key] = factor_id
        FACTORS[factor_id] = monic
    return FACTOR_IDS[key], leading


def poly_json(poly):
    return [[list(p), str(x)] for p, x in sorted(poly.items())]


class Rational:
    def __init__(self, numerator, denominator=None):
        self.n = clean(numerator)
        self.d = dict(denominator or {})
        COUNTS['rational_normalizations'] += 1
        if not self.n:
            self.d = {}
            return
        for factor in list(self.d):
            while self.d[factor]:
                quotient = exact_divide(self.n, FACTORS[factor])
                if quotient is None:
                    break
                self.n = quotient
                self.d[factor] -= 1
                COUNTS['exact_factor_cancellations'] += 1
            if not self.d[factor]:
                del self.d[factor]

    @staticmethod
    def of(value):
        return value if isinstance(value, Rational) else Rational(constant(value))

    def __add__(self, other):
        other = self.of(other)
        common = {f: max(self.d.get(f, 0), other.d.get(f, 0))
                  for f in self.d.keys() | other.d.keys()}
        numerators = []
        for item in (self, other):
            numerator = item.n
            for factor, exponent in common.items():
                numerator = multiply(numerator, power(FACTORS[factor],
                                                       exponent - item.d.get(factor, 0)))
            numerators.append(numerator)
        return Rational(add(*numerators), common)

    __radd__ = __add__

    def __neg__(self):
        return Rational(scale(self.n, -1), self.d)

    def __sub__(self, other):
        return self + -self.of(other)

    def __rsub__(self, other):
        return self.of(other) - self

    def __mul__(self, other):
        other = self.of(other)
        denominator = dict(self.d)
        for factor, exponent in other.d.items():
            denominator[factor] = denominator.get(factor, 0) + exponent
        return Rational(multiply(self.n, other.n), denominator)

    __rmul__ = __mul__

    def inverse(self):
        assert self.n, 'Cannot invert the zero rational function.'
        numerator = constant(1)
        for factor, exponent in self.d.items():
            numerator = multiply(numerator, power(FACTORS[factor], exponent))
        if set(self.n) == {ZERO_MONOMIAL}:
            return Rational(scale(numerator, 1 / self.n[ZERO_MONOMIAL]))
        factor, leading = register_factor(self.n)
        return Rational(scale(numerator, 1 / leading), {factor: 1})

    def __truediv__(self, other):
        return self * self.of(other).inverse()

    def __rtruediv__(self, other):
        return self.of(other) * self.inverse()

    def __pow__(self, exponent):
        assert exponent >= 0
        answer = Rational.of(1)
        for _ in range(exponent):
            answer = answer * self
        return answer

    def denominator_poly(self):
        answer = constant(1)
        for factor, exponent in self.d.items():
            answer = multiply(answer, power(FACTORS[factor], exponent))
        return answer

    def json(self):
        return dict(numerator=poly_json(self.n), denominator_factors=self.d)


def variable(index):
    p = [0, 0, 0]
    p[index] = 1
    return Rational({tuple(p): Fraction(1)})


def verify(records, name, left, right=0):
    left, right = Rational.of(left), Rational.of(right)
    lhs = multiply(left.n, right.denominator_poly())
    rhs = multiply(right.n, left.denominator_poly())
    difference = add(lhs, scale(rhs, -1))
    COUNTS['cross_multiplications'] += 1
    records.append(dict(name=name, left=left.json(), right=right.json(),
                        expanded_difference=poly_json(difference), passed=not difference))
    assert not difference, 'Polynomial identity failed: ' + name


def poly_at_r(poly, node):
    answer = Rational.of(0)
    for (i, j, k), coefficient in poly.items():
        term = Rational({(i, j, 0): coefficient})
        answer += term * node ** k
    return answer


def at_r(value, node):
    answer = poly_at_r(value.n, node)
    for factor, exponent in value.d.items():
        answer /= poly_at_r(FACTORS[factor], node) ** exponent
    return answer


def ordinary_residue(value, row_form, node, slope):
    """Remove the selected simple factor, substitute its node, divide slope."""
    factor, leading = register_factor(row_form.n)
    assert not row_form.d
    multiplicity = value.d.get(factor, 0)
    assert multiplicity <= 1, 'Expected at most a simple selected pole.'
    if not multiplicity:
        return Rational.of(0)
    denominator = dict(value.d)
    del denominator[factor]
    # row_form=leading*monic_factor, so lim row_form*value gains leading.
    regular_part = Rational(scale(value.n, leading), denominator)
    return at_r(regular_part, node) / slope


def rowmul(row, matrix):
    return [sum(row[i] * matrix[i][j] for i in range(3)) for j in range(3)]


def combine(coefficients, columns):
    sample = next(iter(columns.values()))
    if isinstance(sample, list):
        return [sum(value * columns[label][j] for label, value in coefficients.items())
                for j in range(len(sample))]
    return sum(value * columns[label] for label, value in coefficients.items())


def calculate(result):
    records = result['identities']
    a, c, r = [variable(i) for i in range(3)]
    delta_a = a - c
    parameters = [a, c]
    G = [[1 + int(i == j) for j in range(3)] for i in range(3)]
    X, v = [Rational.of(1), -r, r], [Rational.of(0), -r, r]
    forms, kernels, last_column_derivatives, mu = [], [], [], []
    for A in parameters:
        L = [2 - A*r, 1 - 2*A*r, 1 - A*r]
        forms.append(L)
        kernels.append([[G[i][0] / L[i], -G[i][1]*A*r / L[i], Rational.of(0)]
                        for i in range(3)])
        last_column_derivatives.append([G[i][2]*r/L[i] for i in range(3)])
        mu.append([2/L[0], -r/L[1], r/L[2]])
    for t in range(2):
        for i in range(3):
            verify(records, f'K{t+1}_binary_row_{i}_sum', sum(kernels[t][i]), 1)
            verify(records, f'K{t+1}_binary_row_{i}_output2', kernels[t][i][2])
    binary, weak, heads = {}, {}, {}
    for t in range(2):
        o = 1 - t
        for b in range(3):
            hlabel, jlabel = f'H{t+1}{b}', f'J{t+1}{b}'
            first = [X[b] * value for value in kernels[t][b]]
            binary[hlabel] = rowmul(first, kernels[o])
            weak[hlabel] = sum(first[i] * last_column_derivatives[o][i] for i in range(3))
            heads[hlabel] = [X[b] if j == b else Rational.of(0) for j in range(3)]
            binary[jlabel] = [mu[t][b] * value for value in rowmul(v, kernels[o])]
            weak[jlabel] = mu[t][b] * sum(v[i] * last_column_derivatives[o][i]
                                         for i in range(3))
            heads[jlabel] = [Rational.of(0)] * 3
        A, C = parameters[t], parameters[o]
        Lt, Lo = forms[t], forms[o]
        proposed_h = [
            r*(2*Lo[1]-A*r*Lo[0])/Lt[0]/Lo[0]/Lo[1],
            -r**2*(Lo[1]-2*A*r*Lo[0])/Lt[1]/Lo[0]/Lo[1],
            r**2*(Lo[1]-A*r*Lo[0])/Lt[2]/Lo[0]/Lo[1]]
        omega = r**2*(1-3*C*r)/Lo[1]/Lo[2]
        proposed_j = [2*omega/Lt[0], -r*omega/Lt[1], r*omega/Lt[2]]
        for b in range(3):
            verify(records, f'H{t+1}{b}_weak_actual_word', weak[f'H{t+1}{b}'], proposed_h[b])
            verify(records, f'J{t+1}{b}_weak_actual_word', weak[f'J{t+1}{b}'], proposed_j[b])
    combinations = {}
    for t in range(2):
        o, A, C = 1-t, parameters[t], parameters[1-t]
        d = A-C
        combinations[f'kappa{t+1}1'] = {
            f'J{t+1}1': Rational.of(1), f'H{t+1}1': 1/A,
            f'H{t+1}2': (A-2*C)/(2*A*d), f'H{o+1}2': 1/(2*d),
            f'J{t+1}0': (A-4*C)/(4*C*d), f'J{o+1}0': 3*C/(4*A*d)}
        combinations[f'kappa{t+1}2'] = {
            f'J{t+1}2': Rational.of(1), f'H{t+1}1': -(2*A-C)/(A*d),
            f'H{t+1}2': -1/A, f'H{o+1}1': 1/d,
            f'J{t+1}0': -(A-2*C)/(2*C*d), f'J{o+1}0': -C/(2*A*d)}
    combinations['gamma0'] = dict(H10=a/delta_a, H11=2*a*c/delta_a,
                                   H20=-c/delta_a, H21=-2*a*c/delta_a)
    combinations['gamma1'] = dict(H10=-2/delta_a, H11=-c/delta_a,
                                   H20=2/delta_a, H21=a/delta_a)
    combined_weak = {}
    for name, coefficients in combinations.items():
        actual_binary, actual_head = combine(coefficients, binary), combine(coefficients, heads)
        if name.startswith('kappa'):
            t = int(name[5]) - 1
            sign = 1 if name.endswith('1') else -1
            expected_binary = [Rational.of(0)] * 3
            expected_head = [sign * entry / parameters[t] for entry in v]
        else:
            expected_binary = ([Rational.of(1), Rational.of(0), Rational.of(0)]
                               if name == 'gamma0' else [Rational.of(0), -r, Rational.of(0)])
            expected_head = expected_binary
        for j in range(3):
            verify(records, f'{name}_binary_component_{j}', actual_binary[j], expected_binary[j])
            verify(records, f'{name}_source_head_component_{j}', actual_head[j], expected_head[j])
        if name.startswith('kappa'):
            verify(records, f'{name}_exact_completed_row_sum', sum(actual_head))
        combined_weak[name] = combine(coefficients, weak)
    kappa_names = ['kappa11', 'kappa12', 'kappa21', 'kappa22']
    gauge_names = ['gamma0', 'gamma1']
    A_nodes = [(0, 0, 2/a, -a), (1, 0, 2/c, -c)]
    I_nodes = [(0, 1, 1/(2*a), -2*a), (0, 2, 1/a, -a),
               (1, 1, 1/(2*c), -2*c), (1, 2, 1/c, -c)]

    def residues(nodes, names):
        return [[ordinary_residue(combined_weak[name], forms[t][state], node, slope)
                 for name in names] for t, state, node, slope in nodes]

    GA, WA = residues(A_nodes, gauge_names), residues(A_nodes, kappa_names)
    GI, WI = residues(I_nodes, gauge_names), residues(I_nodes, kappa_names)
    proposed_GA = [
        [2/delta_a/(a-4*c), -4/a/delta_a/(a-4*c)],
        [-2/delta_a/(c-4*a), 4/c/delta_a/(c-4*a)]]
    for i in range(2):
        for j in range(2):
            verify(records, f'gauge_A_residue_{i}_{j}', GA[i][j], proposed_GA[i][j])
    det_GA = 8/a/c/delta_a/(a-4*c)/(c-4*a)
    verify(records, 'gauge_A_determinant', GA[0][0]*GA[1][1]-GA[0][1]*GA[1][0], det_GA)
    inverse_GA = [[GA[1][1]/det_GA, -GA[0][1]/det_GA],
                  [-GA[1][0]/det_GA, GA[0][0]/det_GA]]
    N = [
        [-2*(a**2-3*a*c+11*c**2), 6*(a-2*c)**2, -9*a*(a+c), 6*a*(2*a-c)],
        [(a-2*c)*(a-5*c), -6*(a-2*c)*delta_a, -a*(a-5*c), Rational.of(0)],
        [9*c*(a+c), 6*c*(a-2*c), 2*(11*a**2-3*a*c+c**2), -6*(2*a-c)**2],
        [-c*(5*a-c), Rational.of(0), -(2*a-c)*(5*a-c), 6*delta_a*(2*a-c)]]
    scales = [1/a**3, 4/a**3, 1/c**3, 4/c**3]
    Q = []
    for i in range(4):
        row = []
        for j in range(4):
            value = WI[i][j] - sum(GI[i][u]*inverse_GA[u][v_]*WA[v_][j]
                                   for u in range(2) for v_ in range(2))
            target = scales[i]*N[i][j]/8/(a-2*c)/delta_a/(2*a-c)
            verify(records, f'Q_actual_weak_residue_{i}_{j}', value, target)
            row.append(value)
        Q.append(row)
    result.update(
        binary_completed_columns={key: [value.json() for value in row] for key, row in binary.items()},
        weak_completed_columns={key: value.json() for key, value in weak.items()},
        coefficient_combinations={key: {label: value.json() for label, value in row.items()}
                                  for key, row in combinations.items()},
        gauge_A=[[entry.json() for entry in row] for row in GA],
        weak_A=[[entry.json() for entry in row] for row in WA],
        gauge_I=[[entry.json() for entry in row] for row in GI],
        weak_I=[[entry.json() for entry in row] for row in WI],
        actual_gauge_quotient=[[entry.json() for entry in row] for row in Q],
        proposed_N=[[entry.json() for entry in row] for row in N],
        all_identities_passed=all(record['passed'] for record in records))


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024*value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started, phase = time.monotonic(), 'calculation'

    def guard(_signum, _frame):
        if time.monotonic()-started >= (26 if phase == 'calculation' else 28):
            raise TimeoutError('Prescribed 28-second budget; no retry.')
        if maximum_rss_bytes() >= 95*1024**2:
            raise MemoryError('Prescribed 95 MiB budget; no retry.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(
        scope='One independent rational-identity verification of the Pro54 m=2 base; no numeric fixture or all-length claim.',
        variables=VARIABLES, coefficient_field='Q', beta_specialization=1,
        beta_recovery='Every actual weak coefficient contains exactly one last-kernel derivative, hence is linear in the shared beta. W and G scale by beta and Q does likewise.',
        assumptions='a,c are distinct in (1,2); beta is nonzero. Work in Q(a,c,r) before taking ordinary residues.',
        completed_convention='H=X_b e_b K_t K_o; J=mu_tc v K_o. Actual sources are X_b e_b-H and -J.',
        weak_derivation='At delta=0 every K has zero output-2 column. Thus [delta](K_t K_o)_2=K_t(0)[delta](K_o)_2; derivatives of the first factor and external mu multiply a zero column. [delta](K_o)_{i2}=r G_{i2}/l_oi at beta=1.',
        residue_A_order=['2/a', '2/c'],
        residue_I_order=['1/(2a)', '1/a', '1/(2c)', '1/c'],
        kappa_order=['kappa11', 'kappa12', 'kappa21', 'kappa22'],
        gauge_order=['gamma0', 'gamma1'],
        proposed_Q='(1/(8T))*diag(a^-3,4a^-3,c^-3,4c^-3)*N; T=(a-2c)(a-c)(2a-c)',
        arithmetic='Sparse polynomials with exact Fraction coefficients; denominator factors are made monic. Every accepted cancellation is multiplied back, and every final identity is independently cross multiplied to a zero polynomial.',
        resource_limits=dict(process_seconds=28, calculation_seconds=26,
                             maximum_rss_bytes=95*1024**2),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        dependencies='Python standard library only',
        proposal_source='https://chatgpt.com/c/6ad1ea67-9660-83eb-a47d-cd9663f5605b',
        identities=[], errors=[])
    failure = None
    try:
        calculate(result)
        result['status'] = 'PASS: actual binary identities, raw weak coefficients, and gauge-adjusted ordinary residues agree exactly.'
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete single prescribed symbolic calculation; no retry.',
                      error=str(error), traceback=traceback.format_exc())
        result['errors'].append(dict(type=type(error).__name__, message=str(error)))
    phase = 'serialization'
    result.update(
        denominator_factor_registry={key: poly_json(poly) for key, poly in FACTORS.items()},
        arithmetic_counts=COUNTS, elapsed_seconds=time.monotonic()-started,
        maximum_rss_bytes=maximum_rss_bytes(),
        resource_measurement_scope='Before JSON serialization; guard remains active while saving.')
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(dict(status=result['status'], identities=len(result['identities']),
                          elapsed_seconds=result['elapsed_seconds'],
                          maximum_rss_bytes=result['maximum_rss_bytes'],
                          arithmetic_counts=COUNTS)), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
