#!/usr/bin/env python3
"""One prescribed exact finite initialization for the invariant-tail proposal.

Construct the actual nonzero-z binary completed rows at length two, verify
the supplied four-column kernel and its retained source heads over Q(r),
and recurse NH8/NH23 through lengths three, four and five over Q(r).
Clear all 3k binary row forms and certify the three square coefficient
matrices by exact arithmetic modulo 1000003. This is a finite external
certificate, not an all-length proof or a Lean theorem. No parameter sweep.

Standard library only. One guarded execution: 26 calculation seconds,
28 total seconds, 95 MiB maximum RSS; partial output is retained on failure.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback


PRIME = 1000003
Z = F(1, 10)
AS = [F(6, 5), F(7, 5), F(3, 2), F(8, 5), F(17, 10)]
BS = [F(1), F(2), F(5, 2), F(20, 9), F(2465, 1053)]
M = [
    [-12586, -2387, 217, -15841],
    [777245, -3710, -31535, 1250270],
    [197960, -15680, -9800, 344960],
    [6048, 2016, 0, 6048],
    [-842625, 0, 33705, -1348200],
    [-263340, 11970, 11970, -442890],
    [-28620, -18810, 1710, -50742],
    [121086, -4788, -40698, 131796],
    [176400, 0, 0, 0], [0, 20580, 0, 0],
    [0, 0, 49392, 0], [0, 0, 0, 246960],
]
GAMMA_SCALES = [176400, 20580, 49392, 246960]
THETA = [F(-467, 1260), F(-53, 294), F(155, 3528), F(-1399, 3528)]
EXPECTED_DETERMINANTS = {
    3: F(-23293073163309376328273039957039428517207511,
         107684172689914703369140625000000),
    4: F(-1439373716364379585158029548699737332352884408645799224850937398943547392,
         940206571452273376365837975754402577877044677734375),
    5: F(-7690485706092878317508410262130212365271709591150260405342507751018765647752072773147666758078329170128519855473756010306453255652710023168,
         33947936543618314162737453181825271482067222236826198903428977271361233203350593612412922084331512451171875),
}
COUNTS = dict(polynomial_products=0, exact_linear_cancellations=0,
              rational_normalizations=0, identity_checks=0,
              maximum_numerator_degree=0, fraction_reductions_mod_prime=0)
DENOMINATOR_UNITS = {}


def trim(poly):
    out = list(poly)
    while out and not out[-1]:
        out.pop()
    return tuple(out)


def padd(left, right):
    out = [F(0)] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] += value
    for i, value in enumerate(right):
        out[i] += value
    return trim(out)


def pscale(poly, scale):
    return trim([value * scale for value in poly])


def pmul(left, right):
    COUNTS['polynomial_products'] += 1
    if not left or not right:
        return ()
    out = [F(0)] * (len(left) + len(right) - 1)
    for i, value in enumerate(left):
        for j, other in enumerate(right):
            out[i + j] += value * other
    return trim(out)


def peval(poly, point):
    value = F(0)
    for coefficient in reversed(poly):
        value = value * point + coefficient
    return value


def divide_linear(poly, root):
    """Synthetic division by r-root; return None for nonzero remainder."""
    if len(poly) < 2:
        return None
    out = [F(0)] * (len(poly) - 1)
    out[-1] = poly[-1]
    for j in range(len(out) - 2, -1, -1):
        out[j] = poly[j + 1] + root * out[j + 1]
    if poly[0] + root * out[0]:
        return None
    answer = trim(out)
    assert pmul(answer, (-root, F(1))) == poly
    COUNTS['exact_linear_cancellations'] += 1
    return answer


def rational_mod(value):
    value = F(value)
    denominator = value.denominator
    if denominator not in DENOMINATOR_UNITS:
        residue = denominator % PRIME
        assert residue, 'Rational denominator is not a unit modulo the prescribed prime.'
        inverse = pow(residue, -1, PRIME)
        assert residue * inverse % PRIME == 1
        DENOMINATOR_UNITS[denominator] = inverse
    COUNTS['fraction_reductions_mod_prime'] += 1
    return value.numerator % PRIME * DENOMINATOR_UNITS[denominator] % PRIME


def qstr(value):
    value = F(value)
    rational_mod(value)
    return str(value)


def poly_json(poly):
    return [qstr(value) for value in poly]


class Rat:
    """Univariate Q(r), with a monic product of known linear denominators."""

    def __init__(self, numerator=(), denominator=None):
        self.n = trim(tuple(F(value) for value in numerator))
        self.d = dict(denominator or {})
        COUNTS['rational_normalizations'] += 1
        if not self.n:
            self.d = {}
            return
        for root in sorted(self.d):
            while self.d[root]:
                quotient = divide_linear(self.n, root)
                if quotient is None:
                    break
                self.n = quotient
                self.d[root] -= 1
            if not self.d[root]:
                del self.d[root]
        COUNTS['maximum_numerator_degree'] = max(
            COUNTS['maximum_numerator_degree'], len(self.n) - 1)

    @staticmethod
    def of(value):
        return value if isinstance(value, Rat) else Rat((F(value),))

    def __add__(self, other):
        other = Rat.of(other)
        common = {root: max(self.d.get(root, 0), other.d.get(root, 0))
                  for root in self.d.keys() | other.d.keys()}
        numerators = []
        for term in (self, other):
            numerator = term.n
            for root in sorted(common):
                for _ in range(common[root] - term.d.get(root, 0)):
                    numerator = pmul(numerator, (-root, F(1)))
            numerators.append(numerator)
        return Rat(padd(*numerators), common)

    __radd__ = __add__

    def __neg__(self):
        return Rat(pscale(self.n, -1), self.d)

    def __sub__(self, other):
        return self + -Rat.of(other)

    def __rsub__(self, other):
        return Rat.of(other) - self

    def __mul__(self, other):
        other = Rat.of(other)
        denominator = dict(self.d)
        for root, exponent in other.d.items():
            denominator[root] = denominator.get(root, 0) + exponent
        return Rat(pmul(self.n, other.n), denominator)

    __rmul__ = __mul__

    def inverse(self):
        assert self.n, 'Attempted inversion of zero.'
        numerator = self.denominator_poly()
        assert len(self.n) <= 2, 'This calculation only inverts scalars or linear numerators.'
        if len(self.n) == 1:
            return Rat(pscale(numerator, 1 / self.n[0]))
        root = -self.n[0] / self.n[1]
        return Rat(pscale(numerator, 1 / self.n[1]), {root: 1})

    def __truediv__(self, other):
        return self * Rat.of(other).inverse()

    def __rtruediv__(self, other):
        return Rat.of(other) * self.inverse()

    def denominator_poly(self):
        out = (F(1),)
        for root in sorted(self.d):
            for _ in range(self.d[root]):
                out = pmul(out, (-root, F(1)))
        return out

    def at(self, point):
        point = F(point)
        denominator = F(1)
        for root, exponent in self.d.items():
            denominator *= (point - root) ** exponent
        assert denominator, 'Evaluation at a pole.'
        return peval(self.n, point) / denominator

    def infinity(self):
        if not self.n:
            return F(0)
        degree = sum(self.d.values())
        assert len(self.n) - 1 <= degree, 'Unbounded function at infinity.'
        return self.n[-1] if len(self.n) - 1 == degree else F(0)

    def residue(self, point):
        point = F(point)
        if point not in self.d:
            return F(0)
        assert self.d[point] == 1, 'Ordinary residue routine requires a simple pole.'
        denominator = F(1)
        for root, exponent in self.d.items():
            if root != point:
                denominator *= (point - root) ** exponent
        return peval(self.n, point) / denominator

    def json(self):
        return dict(numerator_coefficients_ascending=poly_json(self.n),
                    monic_linear_denominator=[dict(root=qstr(root), exponent=self.d[root])
                                             for root in sorted(self.d)])


R = Rat((0, 1))


def verify(record, name, left, right=0):
    left, right = Rat.of(left), Rat.of(right)
    difference = padd(pmul(left.n, right.denominator_poly()),
                      pscale(pmul(right.n, left.denominator_poly()), -1))
    COUNTS['identity_checks'] += 1
    item = dict(name=name, cross_multiplied_difference=poly_json(difference),
                passed=not difference)
    record['identities'].append(item)
    assert item['passed'], 'Exact Q(r) identity failed: ' + name


def rowmul(row, matrix):
    return [sum((row[i] * matrix[i][j] for i in range(3)), Rat.of(0)) for j in range(3)]


def matmul(left, right):
    return [rowmul(row, right) for row in left]


def kernel(a):
    forms = [2 - a * R, 1 - 2 * a * R, 1 - a * R]
    scales = [Rat.of(1), -a * R, Rat.of(0)]
    return [[(1 + int(i == j)) * scales[j] / forms[i] for j in range(3)]
            for i in range(3)]


def d_function(a):
    return -3 * a * R / (2 - a * R) / (1 - 2 * a * R)


def q_function(a):
    return (a * R * R + (2 * a * Z - 2) * R - Z) / (3 * (1 - a * R))


def a_function(a):
    return (1 + a * R) / (3 * a * R)


def matrix_json(matrix):
    return [[qstr(value) for value in row] for row in matrix]


def determinant_q(matrix):
    work = [[F(value) for value in row] for row in matrix]
    n, answer, swaps, pivots = len(work), F(1), [], []
    assert all(len(row) == n for row in work)
    for j in range(n):
        chosen = next((i for i in range(j, n) if work[i][j]), None)
        assert chosen is not None, 'Singular exact-Q constraint pivot.'
        if chosen != j:
            work[j], work[chosen] = work[chosen], work[j]
            answer = -answer
            swaps.append([j, chosen])
        pivot = work[j][j]
        answer *= pivot
        factors = []
        for i in range(j + 1, n):
            factor = work[i][j] / pivot
            factors.append(dict(row=i, multiplier=qstr(factor)))
            for col in range(j, n):
                work[i][col] -= factor * work[j][col]
        pivots.append(dict(column=j, chosen_row=chosen, value=qstr(pivot),
                           eliminations=factors))
    return dict(determinant=qstr(answer), pivot_records=pivots, row_swaps=swaps,
                upper_triangular_matrix=matrix_json(work))


def determinant_mod_certificate(matrix):
    original = [[rational_mod(value) for value in row] for row in matrix]
    work = [row[:] for row in original]
    n, answer, pivots, swaps = len(work), 1, [], []
    assert all(len(row) == n for row in work)
    for j in range(n):
        chosen = next((i for i in range(j, n) if work[i][j]), None)
        assert chosen is not None, 'Singular coefficient matrix modulo the prescribed prime.'
        if chosen != j:
            work[j], work[chosen] = work[chosen], work[j]
            answer = -answer % PRIME
            swaps.append([j, chosen])
        pivot = work[j][j]
        inverse = pow(pivot, -1, PRIME)
        answer = answer * pivot % PRIME
        eliminations = []
        for i in range(j + 1, n):
            factor = work[i][j] * inverse % PRIME
            eliminations.append(dict(row=i, multiplier=factor))
            for col in range(j, n):
                work[i][col] = (work[i][col] - factor * work[j][col]) % PRIME
        pivots.append(dict(column=j, chosen_row=chosen, value=pivot, inverse=inverse,
                           eliminations=eliminations))
    replay = [row[:] for row in original]
    for item in pivots:
        j, chosen = item['column'], item['chosen_row']
        replay[j], replay[chosen] = replay[chosen], replay[j]
        assert replay[j][j] == item['value']
        assert item['value'] * item['inverse'] % PRIME == 1
        for elimination in item['eliminations']:
            i, factor = elimination['row'], elimination['multiplier']
            replay[i] = [(x - factor * y) % PRIME for x, y in zip(replay[i], replay[j])]
    assert replay == work
    assert all(not work[i][j] for i in range(n) for j in range(i))
    return dict(prime=PRIME, matrix_mod_prime=original, determinant_mod_prime=answer,
                rank=n, pivot_records=pivots, row_swaps=swaps,
                upper_triangular_matrix=work, independent_operation_replay_passed=True)


def clear_coefficients(record, name, function, common, size):
    cleared = function * common
    assert not cleared.d, 'Prescribed common denominator did not clear ' + name
    assert len(cleared.n) <= size, 'Prescribed degree bound failed for ' + name
    assert not common.d
    difference = padd(pmul(cleared.n, function.denominator_poly()),
                      pscale(pmul(function.n, common.n), -1))
    COUNTS['identity_checks'] += 1
    record['identities'].append(dict(name=name + '_clearing_identity',
                                     cross_multiplied_difference=poly_json(difference),
                                     passed=not difference))
    assert not difference, 'Independent denominator clearing identity failed: ' + name
    return list(cleared.n) + [F(0)] * (size - len(cleared.n))


def calculate(record):
    kernels = [kernel(a) for a in AS]
    record['actual_binary_kernels'] = [
        [[entry.json() for entry in row] for row in k] for k in kernels]
    X, v = [Rat.of(1), -R, R - Z], [Rat.of(Z), -R, R - Z]
    labels = [f'{kind}{s + 1}{c}' for kind in ('H', 'J') for s in range(2) for c in range(3)]
    binary, weak, heads = [], [], []
    for kind in ('H', 'J'):
        for s in range(2):
            other = 1 - s
            forms = [2 - AS[s] * R, 1 - 2 * AS[s] * R, 1 - AS[s] * R]
            other_forms = [2 - AS[other] * R, 1 - 2 * AS[other] * R, 1 - AS[other] * R]
            u = [1 / other_forms[0], 1 / other_forms[1], 2 / other_forms[2]]
            mus = [2 / forms[0], -R / forms[1], (R - Z) / forms[2]]
            product = matmul(kernels[s], kernels[other])
            for c in range(3):
                if kind == 'H':
                    binary.append([X[c] * entry for entry in product[c]])
                    weak.append(BS[other] * X[c] * sum(
                        (kernels[s][c][i] * u[i] for i in range(3)), Rat.of(0)))
                    heads.append([X[c] if i == c else Rat.of(0) for i in range(3)])
                else:
                    binary.append([mus[c] * entry for entry in rowmul(v, kernels[other])])
                    weak.append(BS[other] * mus[c] * sum(
                        (v[i] * u[i] for i in range(3)), Rat.of(0)))
                    heads.append([Rat.of(0)] * 3)
    gamma = [[F(M[i][j], GAMMA_SCALES[j]) for j in range(4)] for i in range(12)]
    head_sums = [sum(row, Rat.of(0)) for row in heads]
    for i, label in enumerate(labels):
        verify(record, label + '_completed_row_sum_equals_head_sum', sum(binary[i], Rat.of(0)), head_sums[i])
        assert not head_sums[i].d and len(head_sums[i].n) <= 2
    poles = [node for a in AS[:2] for node in (2 / a, 1 / (2 * a), 1 / a)]
    constraints = [[head_sums[j].n[i] if len(head_sums[j].n) > i else F(0)
                    for j in range(12)] for i in range(2)]
    constraints.extend([[binary[j][1].residue(node) for j in range(12)] for node in poles])
    pivot = determinant_q([row[:8] for row in constraints])
    assert F(pivot['determinant']) == F(-1075, 117504), 'Supplied first-eight constraint determinant mismatch.'
    S, combined_heads = [], []
    for j in range(4):
        for i, row in enumerate(constraints):
            verify(record, f'gamma{j}_constraint{i}', sum(row[t] * gamma[t][j] for t in range(12)))
        for output in range(3):
            verify(record, f'gamma{j}_actual_binary_output{output}', sum(
                (gamma[t][j] * binary[t][output] for t in range(12)), Rat.of(0)))
        head = [sum((gamma[t][j] * heads[t][output] for t in range(12)), Rat.of(0))
                for output in range(3)]
        for output in range(3):
            verify(record, f'gamma{j}_retained_head{output}', head[output], THETA[j] * v[output])
        verify(record, f'gamma{j}_exact_row_sum_zero', sum(
            (gamma[t][j] * head_sums[t] for t in range(12)), Rat.of(0)))
        combined_heads.append([entry.json() for entry in head])
        S.append(sum((gamma[t][j] * weak[t] for t in range(12)), Rat.of(0)))
    assert [row[:] for row in gamma[8:]] == [[F(int(i == j)) for j in range(4)] for i in range(4)]
    record['base'] = dict(
        source_order=labels, supplied_M=M, gamma_column_denominators=GAMMA_SCALES,
        gamma=matrix_json(gamma), gamma_last_four_rows_identity=True,
        actual_completed_binary_rows=[[entry.json() for entry in row] for row in binary],
        actual_weak_normalized_rows=[entry.json() for entry in weak],
        actual_source_heads=[[entry.json() for entry in row] for row in heads],
        combined_source_heads=combined_heads, theta=[qstr(x) for x in THETA],
        constraint_row_order=['row_sum_coefficient_r0', 'row_sum_coefficient_r1'] +
                             ['ordinary_r_residue_at_' + qstr(node) for node in poles],
        constraint_matrix=matrix_json(constraints), first_eight_constraint_pivot=pivot,
        weak_kernel_functions=[entry.json() for entry in S])
    all_nodes = [node for a in AS for node in (2 / a, 1 / (2 * a), 1 / a)]
    assert len(set(all_nodes)) == len(all_nodes)
    assert Z not in all_nodes and all(a > 0 for a in AS) and all(b > 0 for b in BS)
    record['parameter_guards'] = dict(all_a_positive=True, all_b_positive=True,
                                      all_fifteen_poles_distinct=True, z_avoids_all_poles=True,
                                      all_poles=[qstr(node) for node in all_nodes])
    prefix = matmul(kernels[0], kernels[1])
    D = d_function(AS[0]) * d_function(AS[1])
    common = Rat.of(1)
    for a in AS[:2]:
        common = common * (2 - a * R) * (1 - 2 * a * R) * (1 - a * R)
    Q = q_function(AS[0])
    S_labels = [f'base_gamma{j}' for j in range(4)]
    for k in (3, 4, 5):
        a, previous_a = AS[k - 1], AS[k - 2]
        b, previous_b = BS[k - 1], BS[k - 2]
        xi = 1 / a
        qxi, dxi = Q.at(xi), D.at(xi)
        assert qxi and dxi and a != previous_a
        dk, qk = d_function(a), q_function(a)
        delta = b * a_function(a) - previous_b * a_function(previous_a)
        chi = 4 * b * (R - Z) / (3 * (1 - a * R))
        beta = [2 * Q / (2 - a * R), -R * Q / (1 - 2 * a * R),
                dk * qk + (R - Z) * Q / (qxi * (1 - a * R))]
        new = [delta * D * value for value in beta]
        moved = matmul(kernels[k - 1], prefix)
        B0, B1 = moved[0][1], -R * moved[1][1]
        W0 = delta * B0 + (previous_b - b) / 3
        W1 = delta * B1 + (b - previous_b) * R / 3
        verify(record, f'k{k}_W_relation', W1, -R * W0 - R * delta * D * dk)
        w00 = previous_b / 2 - b / 3 - previous_a * b / (6 * a)
        w1inf = previous_b / (2 * previous_a) - b / (6 * previous_a) - b / (3 * a)
        verify(record, f'k{k}_W0_at0', W0.at(0), w00)
        verify(record, f'k{k}_W0_at_infinity', W0.infinity())
        verify(record, f'k{k}_W1_at0', W1.at(0))
        verify(record, f'k{k}_W1_at_infinity', W1.infinity(), w1inf)
        kappa0 = Z / 2 * ((3 * previous_a - 2 * a) * b - a * previous_b) / (a - previous_a)
        kappainf = (a * previous_b - (3 * a - 2 * previous_a) * b) / (2 * a * (a - previous_a))
        transported = []
        for j, c in enumerate(S):
            c0, cinf, cxi = c.at(0), c.infinity(), c.at(xi)
            alpha0 = Z * a / (a - previous_a) * c0
            alphainf = -previous_a / (a - previous_a) * cinf
            value = chi * c - delta * (cxi / dxi) * D * dk * qk - alpha0 * W0 - alphainf * W1
            verify(record, f'k{k}_T{j}_endpoint0', value.at(0), kappa0 * c0)
            verify(record, f'k{k}_T{j}_endpoint_infinity', value.infinity(), kappainf * cinf)
            transported.append(value)
        for j, value in enumerate(new):
            verify(record, f'k{k}_N{j}_at0', value.at(0))
            verify(record, f'k{k}_N{j}_at_infinity', value.infinity())
        S = new + transported
        S_labels = [f'N{k}_{j}' for j in range(3)] + [f'T{k}({label})' for label in S_labels]
        common = common * (2 - a * R) * (1 - 2 * a * R) * (1 - a * R)
        functions = S + [Rat.of(1), W0, W1]
        column_labels = S_labels + ['1', f'W{k}_0', f'W{k}_1']
        n = 3 * k + 1
        assert len(functions) == n
        columns = [clear_coefficients(record, f'k{k}_column{j}', value, common, n)
                   for j, value in enumerate(functions)]
        matrix = [list(row) for row in zip(*columns)]
        certificate = determinant_mod_certificate(matrix)
        expected = rational_mod(EXPECTED_DETERMINANTS[k])
        assert certificate['determinant_mod_prime'] == expected, f'Pro61 determinant mismatch at k={k}.'
        endpoint_values = dict(at_zero=[qstr(c.at(0)) for c in S],
                               at_infinity=[qstr(c.infinity()) for c in S],
                               at_z=[qstr(c.at(Z)) for c in S])
        for j, c in enumerate(S):
            verify(record, f'k{k}_prescribed_zero_at0_column{j}', c.at(0))
            if k >= 4:
                verify(record, f'k{k}_prescribed_zero_at_infinity_column{j}', c.infinity())
            if k == 5:
                verify(record, f'k{k}_prescribed_zero_at_z_column{j}', c.at(Z))
        allowed_nodes = set(all_nodes[:3 * k])
        assert all(set(c.d).issubset(allowed_nodes) and all(e == 1 for e in c.d.values()) for c in functions)
        record['stages'].append(dict(
            length=k, dimension=n, S_dimension=len(S), column_order=column_labels,
            row_order=[f'coefficient_r^{i}' for i in range(n)],
            common_denominator_coefficients_ascending=poly_json(common.n),
            S_functions=[c.json() for c in S], N_functions=[c.json() for c in new],
            W0=W0.json(), W1=W1.json(), delta=delta.json(), chi=chi.json(),
            exact_rational_coefficient_matrix=matrix_json(matrix),
            coefficient_matrix_sha256=hashlib.sha256(json.dumps(matrix_json(matrix), separators=(',', ':')).encode()).hexdigest(),
            determinant_certificate=certificate,
            proposed_exact_determinant=qstr(EXPECTED_DETERMINANTS[k]),
            proposed_determinant_mod_prime=expected, proposed_determinant_matches_mod_prime=True,
            endpoint_values=endpoint_values,
            guards=dict(Q_at_xi=qstr(qxi), D_old_at_xi=qstr(dxi),
                        a_difference=qstr(a - previous_a), kappa0=qstr(kappa0),
                        kappa_infinity=qstr(kappainf), delta_at_z=qstr(delta.at(Z)),
                        all_functions_have_only_allowed_simple_poles=True,
                        all_functions_bounded_at_infinity=True,
                        common_denominator_exactly_clears_all_columns=True)))
        prefix = matmul(prefix, kernels[k - 1])
        D = D * dk
    record['all_prescribed_checks_passed'] = True


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024 * value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started, phase = time.monotonic(), 'calculation'

    def guard(_signum, _frame):
        if time.monotonic() - started >= (26 if phase == 'calculation' else 28):
            raise TimeoutError('Prescribed single-run time budget exhausted; no retry.')
        if maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise MemoryError('Prescribed 95 MiB RSS budget exhausted; no retry.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    root = Path(__file__).resolve().parents[1]
    research = root / 'research/SOURCE24_NONZERO_H_WEAK_TRANSFER.md'
    record = dict(
        scope='One prescribed exact finite initialization, lengths 2 through 5; external certificate, not Lean and not an all-length conclusion.',
        parameters=dict(z=qstr(Z), a=[qstr(a) for a in AS], b=[qstr(b) for b in BS], prime=PRIME),
        scalar_field='Q(r), then exact reduction modulo 1000003 for the square coefficient determinants',
        actual_conventions='G=I+11^T; X=(1,-r,r-z); v=(z,-r,r-z); K_t^0=diag(l_t)^-1 G diag(1,a_t,0) diag(X). Completed H=X_c e_c K_s K_other and J=mu_sc v K_other. Actual source heads are retained; actual sources are head-H and -J.',
        weak_conventions='c=[delta]C_2/(r-z). Weak H=b_other X_c e_c K_s^0 u_other, weak J=b_other mu_sc v u_other, u=(1/l0,1/l1,2/l2). This derives from the last kernel since every binary K has zero output-2 column.',
        recurrence='NH8 new columns followed by NH23 transports: S_k=[N0,N1,N2]+[T_full(c) for c in S_(k-1)]. All arithmetic is exact Q(r).',
        matrix_convention='Rows are coefficients r^0 through r^(3k); columns are S_k,1,W0,W1 after multiplication by Lambda_k=product_t (2-a_t r)(1-2a_t r)(1-a_t r).',
        arithmetic='Fraction coefficient univariate polynomials; factored monic linear denominators. Every accepted cancellation is multiplied back. Final identities are cross multiplied. Modular elimination records all pivots and operations, replayed on the original matrix.',
        guards='Endpoint multipliers and delta(z) may intentionally vanish; no generic injectivity condition is assumed. Only actual formula denominators and rational-to-modular reduction denominators must be units.',
        resource_limits=dict(process_seconds=28, calculation_seconds=26, maximum_rss_bytes=95 * 1024 ** 2),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_dependencies={'research/SOURCE24_NONZERO_H_WEAK_TRANSFER.md': hashlib.sha256(research.read_bytes()).hexdigest()},
        software_dependencies='Python standard library only', python_version=sys.version,
        identities=[], stages=[], errors=[])
    failure = None
    try:
        calculate(record)
        record['status'] = 'PASS: exact actual base identities, endpoint specializations, and all three nonzero modular determinant certificates.'
    except Exception as error:
        failure = error
        record.update(status='FAILED or incomplete single prescribed calculation; no automatic retry.',
                      error=str(error), traceback=traceback.format_exc())
        record['errors'].append(dict(type=type(error).__name__, message=str(error)))
    phase = 'serialization'
    record.update(arithmetic_counts=COUNTS, elapsed_seconds=time.monotonic() - started,
                  maximum_rss_bytes=maximum_rss_bytes(),
                  resource_measurement_scope='Before JSON serialization; guard remains active during saving.',
                  rational_denominator_unit_certificates=[
                      dict(denominator=str(denominator), residue=denominator % PRIME,
                           inverse_mod_prime=inverse)
                      for denominator, inverse in sorted(DENOMINATOR_UNITS.items())])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(dict(status=record['status'], elapsed_seconds=record['elapsed_seconds'],
                          maximum_rss_bytes=record['maximum_rss_bytes'],
                          identities=len(record['identities']),
                          determinants={stage['length']: stage['determinant_certificate']['determinant_mod_prime']
                                        for stage in record['stages']})), flush=True)
    if failure is not None:
        print(record['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
