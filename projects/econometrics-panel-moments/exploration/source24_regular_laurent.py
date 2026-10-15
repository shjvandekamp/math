#!/usr/bin/env python3
"""Bounded, precision-tracked Laurent exploration of the regular Schur block.

Old-old rows are transported by K_N^-1, making O the constant old residue
matrix. Beta rows are divided by their canonical B coefficient J. A
shared-N column (a,b) is divided by A_N(a,b)*epsilon^([a=0]+[b=0]).
The polar inverse is computed after a constant kernel-complement change
of columns and division of its vanishing kernel columns by epsilon.

Every scalar carries an absolute error cutoff O(epsilon^precision).
No unobserved tail is treated as a proved zero. The calculation is over
F_1000003((epsilon)); it is finite evidence, not an all-length theorem.

Run one bounded case:
  nice -n 19 python3 exploration/source24_regular_laurent.py --m 2 --output exploration/source24-regular-laurent-results.json

Record the separate leading-operator diagnostic without replacing any case:
  nice -n 19 python3 exploration/source24_regular_laurent.py --m 3 --precision 6 --leading-operator-diagnostic --output exploration/source24-regular-laurent-results.json
"""

import argparse
from functools import lru_cache
import json
from pathlib import Path
import resource
import signal
import sys
import time

import absorbing_firstjet as dual
import normalized_sparse_source24 as sparse
import source24_residue as residue
import source24_schur as schur


P, G, INF = residue.PRIME, schur.G, float('inf')
RELATIVE_PRECISION = 10


class PrecisionFailure(Exception):
    pass


class Laurent:
    __slots__ = ('terms', 'precision')

    def __init__(self, coefficients=(), precision=INF):
        self.terms = tuple(sorted((e, c % P) for e, c in dict(coefficients).items() if e < precision and c % P))
        self.precision = precision

    @staticmethod
    def cast(value):
        return value if isinstance(value, Laurent) else Laurent(((0, value),))

    @property
    def valuation(self):
        return self.terms[0][0] if self.terms else self.precision

    def coefficient(self, exponent):
        if exponent >= self.precision:
            raise PrecisionFailure(f'Coefficient {exponent} not known below cutoff {self.precision}.')
        return dict(self.terms).get(exponent, 0)

    def __bool__(self):
        # False means no *known* nonzero coefficient. It need not mean exact zero.
        return bool(self.terms)

    def __add__(self, other):
        other = self.cast(other)
        precision = min(self.precision, other.precision)
        values = dict(self.terms)
        for e, c in other.terms:
            values[e] = values.get(e, 0) + c
        return Laurent(values.items(), precision)

    __radd__ = __add__

    def __neg__(self):
        return Laurent(((e, -c) for e, c in self.terms), self.precision)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        other = self.cast(other)
        if (not self.terms and self.precision == INF) or (not other.terms and other.precision == INF):
            return Laurent()
        precision = min(INF, self.precision + other.valuation, other.precision + self.valuation)
        values = {}
        for e, c in self.terms:
            for f, d in other.terms:
                if e + f < precision:
                    values[e + f] = (values.get(e + f, 0) + c * d) % P
        return Laurent(values.items(), precision)

    __rmul__ = __mul__

    def __mod__(self, modulus):
        assert modulus == P
        return self

    def __eq__(self, other):
        # Congruence through the common known cutoff, not equality of unknown tails.
        return not (self - other).terms

    def __pow__(self, exponent, modulus=None):
        assert modulus is None or modulus == P
        if exponent == -1:
            return inverse_series(self.terms, self.precision)
        assert exponent >= 0
        answer, base = Laurent.cast(1), self
        while exponent:
            if exponent & 1:
                answer = answer * base
            exponent //= 2
            if exponent:
                base = base * base
        return answer


@lru_cache(maxsize=2048)
def inverse_series(terms, precision):
    if not terms:
        raise PrecisionFailure('Cannot invert a scalar whose leading term is not known.')
    valuation, leading = terms[0]
    inverse_leading = pow(leading, -1, P)
    if len(terms) == 1 and precision == INF:
        return Laurent(((-valuation, inverse_leading),))
    cutoff = min(-valuation + RELATIVE_PRECISION, precision - 2 * valuation)
    coefficients = {e - valuation: c for e, c in terms}
    values = [inverse_leading]
    for k in range(1, cutoff + valuation):
        values.append(-inverse_leading * sum(coefficients.get(j, 0) * values[k - j]
                                            for j in range(1, k + 1)) % P)
    return Laurent(((-valuation + k, value) for k, value in enumerate(values)), cutoff)


def monomial(exponent, coefficient=1):
    return Laurent(((exponent, coefficient),))


def minimum_precision(matrix):
    return min(Laurent.cast(x).precision for row in matrix for x in row)


def unit_inverse(matrix):
    """Invert an analytic matrix with invertible constant term; no pole pivots."""
    n = len(matrix)
    a = [[Laurent.cast(x) for x in row] + [Laurent.cast(int(i == j)) for j in range(n)]
         for i, row in enumerate(matrix)]
    for c in range(n):
        found = next((i for i in range(c, n) if a[i][c].coefficient(0)), None)
        if found is None:
            raise PrecisionFailure('The normalized polar constant matrix is singular.')
        a[c], a[found] = a[found], a[c]
        inverse = pow(a[c][c], -1, P)
        a[c] = [x * inverse for x in a[c]]
        for i in range(n):
            if i != c:
                factor = a[i][c]
                # A finite-cutoff zero still contributes unknown terms. In
                # particular, skipping it can overstate inverse precision.
                a[i] = [x - factor * y for x, y in zip(a[i], a[c])]
    inverse = [row[n:] for row in a]
    product = schur.matrix_product(matrix, inverse)
    assert all(not (x - int(i == j)).terms for i, row in enumerate(product) for j, x in enumerate(row))
    assert minimum_precision(product) > 0
    return inverse


def polar_inverse(matrix):
    assert all(Laurent.cast(x).valuation >= 0 for row in matrix for x in row)
    constant = [[Laurent.cast(x).coefficient(0) for x in row] for row in matrix]
    pivots, free, kernel = dual.rref_kernel(constant)
    n = len(matrix)
    change = [[int(i == c) for c in pivots] + [vector[i] for vector in kernel] for i in range(n)]
    normalized = schur.matrix_product(matrix, change)
    for row in normalized:
        for j in range(len(pivots), n):
            row[j] = row[j] * monomial(-1)
    assert all(x.valuation >= 0 for row in normalized for x in row)
    leading = [[x.coefficient(0) for x in row] for row in normalized]
    leading_certificate = residue.modular_rank(leading, P)
    if leading_certificate['rank'] != n:
        raise PrecisionFailure('First-order polar kernel complement is not invertible.')
    inverse = unit_inverse(normalized)
    scaled_change = [[Laurent.cast(x) * monomial(-int(j >= len(pivots)))
                      for j, x in enumerate(row)] for row in change]
    return schur.matrix_product(scaled_change, inverse), dict(
        leading_rank=len(pivots), leading_nullity=len(free),
        normalized_constant_determinant_mod_prime=leading_certificate['determinant_mod_prime'],
        normalized_matrix_minimum_precision=minimum_precision(normalized),
        inverse_minimum_precision=minimum_precision(inverse))


def determinant_leading(matrix):
    """Complete-pivot Laurent elimination; stop if precision cannot certify a pivot."""
    a = [[Laurent.cast(x) for x in row] for row in matrix]
    n, sign, order, coefficient, pivots = len(a), 1, 0, 1, []
    for k in range(n):
        candidates = [(a[i][j].valuation, i, j) for i in range(k, n) for j in range(k, n) if a[i][j]]
        if not candidates:
            return dict(certified=False, completed_pivots=k,
                        remaining_minimum_precision=min(a[i][j].precision for i in range(k, n) for j in range(k, n)),
                        reason='No remaining leading coefficient is known; no vanishing tail is inferred.', pivots=pivots)
        valuation, i, j = min(candidates)
        if i != k:
            a[k], a[i] = a[i], a[k]
            sign = -sign
        if j != k:
            for row in a:
                row[k], row[j] = row[j], row[k]
            sign = -sign
        pivot = a[k][k]
        leading = pivot.terms[0][1]
        pivots.append(dict(valuation=valuation, leading_coefficient=leading, precision=pivot.precision))
        order += valuation
        coefficient = coefficient * leading % P
        inverse = pow(pivot, -1, P)
        for row in range(k + 1, n):
            factor = a[row][k] * inverse
            for column in range(k + 1, n):
                a[row][column] = a[row][column] - factor * a[k][column]
    return dict(certified=True, valuation=order, leading_coefficient_mod_prime=sign * coefficient % P,
                pivots=pivots)


def check_precision_rules():
    """Regression for unknown-tail propagation and cancellation, without rank scans."""
    tail = Laurent((), 4)
    assert not tail and tail.precision != INF
    inverse = unit_inverse([[1, tail], [0, 1]])
    assert not inverse[0][1] and inverse[0][1].precision == 4
    shifted = tail * monomial(-3)
    assert not shifted and shifted.precision == 1
    cancelled = Laurent(((0, 1),), 4) - 1
    assert not cancelled and cancelled.precision == 4
    assert (Laurent() * monomial(-3)).precision == INF
    reciprocal = pow(Laurent(((2, 1), (3, 1)), 6), -1, P)
    assert reciprocal.precision == 2
    assert reciprocal.terms == ((-2, 1), (-1, P - 1), (0, 1), (1, P - 1))
    uncertain = determinant_leading([[1, 1], [1, Laurent(((0, 1),), 4)]])
    assert not uncertain['certified'] and uncertain['completed_pivots'] == 1


def check_odd_incoming_formula(m, A, PinvQ, Zminus3, labels):
    """Check the proposed odd-m lambda0 and incoming old-residue formulas."""
    assert m % 2 == 1
    old_blocks = list(range(2, m + 2))
    c = {}
    first_old = {t: min(s for s in old_blocks if s != t) for t in old_blocks}
    for t in old_blocks:
        r = first_old[t]
        point = [0, A[r][0][2], -A[r][0][1] % P]
        Kt = residue.ordinary_kernel(A, t, point, P)
        binary_determinant = (Kt[1][1] * Kt[2][2] - Kt[1][2] * Kt[2][1]) % P
        for a in range(3):
            c[t, a] = point[a] * pow(residue.dot(A[t][a], point, P) * binary_determinant % P, -1, P) % P if a else 0
    physical_lambda = []
    predicted_lambda = []
    for i, (_, r, a, b) in enumerate(labels['shared_new_column_labels']):
        physical = [x * monomial(-int(a == 0) - int(b == 0)) for x in PinvQ[i]]
        assert all(x.valuation >= 0 for x in physical)
        physical_lambda.append([x.coefficient(0) for x in physical])
        predicted_lambda.append([A[t][cstate][dstate] * c[t, cstate] % P
                                 if (r, a, b) == (first_old[t], dstate, 0) else 0
                                 for t, _, cstate, dstate in labels['first_new_column_labels']])
    assert physical_lambda == predicted_lambda

    G_inverse, _ = schur.invert([list(row) for row in G])
    w = G_inverse[2]
    predicted_Z = []
    for u in old_blocks:
        for v in old_blocks:
            if u >= v:
                continue
            for cstate in range(3):
                for dstate in range(3):
                    point = residue.cross(A[u][cstate], A[v][dstate], P)
                    U = [A[u][cstate][i] * point[i] % P for i in range(3)]
                    V = [A[v][dstate][i] * point[i] % P for i in range(3)]
                    kernels = {}
                    for k in old_blocks:
                        if k == u:
                            kernels[k] = [U[:] if a == cstate else [0, 0, 0] for a in range(3)]
                        elif k == v:
                            kernels[k] = [V[:] if a == dstate else [0, 0, 0] for a in range(3)]
                        else:
                            kernels[k] = residue.ordinary_kernel(A, k, point, P)
                    omitted = {t: residue.word_product(kernels, [k for k in old_blocks if k != t], P)[0][2]
                               for t in old_blocks}
                    first_words = {r: residue.word_product(kernels, residue.ordered_word(old_blocks, r), P)[0][2]
                                   for r in old_blocks}
                    alpha, beta = [], []
                    for t, _, a, b in labels['first_new_column_labels']:
                        # If t is a pole block, its missing kernel pole must
                        # instead come from the prefactor 1/L_ta.
                        if (t == u and a != cstate) or (t == v and a != dstate):
                            first_term = 0
                        else:
                            first_term = -point[a] * omitted[t] % P
                            if t not in (u, v):
                                first_term = first_term * pow(residue.dot(A[t][a], point, P), -1, P) % P
                        scalar = A[t][a][b] * point[b] * point[0] * pow(point[2], -1, P) % P
                        scalar = scalar * (first_term + c[t, a] * first_words[first_old[t]]) % P
                        av, bv = residue.coordinates([scalar * x % P for x in w], U, V, P)
                        alpha.append(av)
                        beta.append(bv)
                    predicted_Z.extend((alpha, beta))
    assert predicted_Z == Zminus3
    return dict(physical_lambda0_entrywise_verified=True,
                lambda_conversion='lambda_physical=diag(epsilon^(-[shared_a=0]-[divergent_b=0]))*(Pnorm^-1*Q)',
                lambda_support='Column (t,N,A,B) has only row (N,min(old blocks except t),B,0), coefficient A_t(A,B)*c_tA; c_t0=0.',
                c_tA_definition='For A!=0, X_A/(L_tA*det(K_t restricted to states 1,2)) at X0=L_r0=0, r=min(old blocks except t).',
                c_tA=[dict(t=t, a=a, coefficient=value) for (t, a), value in sorted(c.items())],
                physical_lambda0_sha256=residue.matrix_hash(physical_lambda),
                physical_lambda0_rank_certificate=residue.modular_rank(physical_lambda, P),
                incoming_Z_minus3_double_residues_entrywise_verified=True,
                incoming_formula='psi*w, w=e_2*G^-1, psi=A_t(A,B)*X_B*X0/X2*(-X_A*P_omit_t[0,2]/L_tA+c_tA*P_first_r[0,2]); both old pole kernels replaced by residue rows.',
                incoming_Z_minus3_sha256=residue.matrix_hash(predicted_Z))


def leading_operator_diagnostic(m, A, blocks, PinvQ, old_inverse, OinvD, OinvE, H, labels):
    """Auxiliary coefficient identities and ranks; no general nonvanishing claim."""
    multiply, subtract = schur.matrix_product, schur.matrix_difference
    Z = subtract(blocks['E'], multiply(blocks['D'], PinvQ))
    OinvZ = subtract(OinvE, multiply(OinvD, PinvQ))
    direct = subtract(blocks['S'], multiply(blocks['R'], PinvQ))
    feedback = multiply(blocks['B'], OinvZ)
    for left, right in ((OinvZ, multiply(old_inverse, Z)), (H, subtract(direct, feedback))):
        difference = subtract(left, right)
        assert all(not x.terms for row in difference for x in row)
        assert minimum_precision(difference) > -3

    def valuation(matrix):
        entries = [Laurent.cast(x) for row in matrix for x in row]
        known = [x.valuation for x in entries if x]
        if not known:
            raise PrecisionFailure('No leading coefficient known for a diagnostic matrix.')
        answer = min(known)
        if any(x.precision <= answer for x in entries):
            raise PrecisionFailure('An unknown tail could precede a diagnostic leading term.')
        return answer

    def coefficient(matrix, exponent):
        return [[Laurent.cast(x).coefficient(exponent) for x in row] for row in matrix]

    matrices = dict(B=blocks['B'], E=blocks['E'], D=blocks['D'], PinvQ=PinvQ,
                    Areg=direct, Z=Z, OinvZ=OinvZ, Feedback=feedback, H=H)
    valuations = {name: valuation(matrix) for name, matrix in matrices.items()}
    if valuations['B'] < 0 or valuations['Z'] < -3 or valuations['Areg'] <= -3:
        raise PrecisionFailure('Leading-operator bounds do not justify the requested factorization.')
    B0, Zminus3, OinvZminus3 = coefficient(blocks['B'], 0), coefficient(Z, -3), coefficient(OinvZ, -3)
    _, old_columns = schur.canonical_labels(m + 2)
    J = [[int((t, a, b) == (k, c, d)) for k, s, c, d in old_columns]
         for t, N, a, b in labels['beta_row_labels']]
    product = multiply(B0, OinvZminus3)
    Hminus3 = coefficient(H, -3)
    assert OinvZminus3 == multiply(old_inverse, Zminus3)
    assert product == coefficient(feedback, -3)
    assert [[-x % P for x in row] for row in product] == Hminus3
    coefficients = dict(B0=B0, J_incidence=J, T0=subtract(J, B0), Z_minus3=Zminus3,
                        OinvZ_minus3=OinvZminus3, B0_OinvZ_minus3=product, H_minus3=Hminus3,
                        Areg_minus3=coefficient(direct, -3))
    incoming = check_odd_incoming_formula(m, A, PinvQ, Zminus3, labels)
    return dict(diagnostic='leading_operator', m=m, prime=P, G=G,
                old_time_factors=sparse.factors(m, 'economic'), new_times='epsilon,epsilon^3',
                relative_inverse_precision=RELATIVE_PRECISION,
                minimum_valuations=valuations,
                minimum_absolute_precisions={name: minimum_precision(matrix) for name, matrix in matrices.items()},
                coefficient_rank_certificates={name: residue.modular_rank(matrix, P) for name, matrix in coefficients.items()},
                coefficient_matrix_sha256={name: residue.matrix_hash(matrix) for name, matrix in coefficients.items()},
                definitions='Z=E-D*(P^-1*Q); OinvZ=O_old^-1*Z; T0=J_incidence-B0. J_incidence is distinct from the beta-row scalar normalizer J.',
                OinvZ_coefficient_identity_verified=True,
                H_minus3_equals_negative_B0_OinvZ_minus3_verified=True,
                odd_incoming_formula=incoming,
                precision_regression_checks_passed=True,
                scope='Exact modular auxiliary factorization at one fixture; no all-m rank or nonvanishing theorem.')


def calculate(m, leading_operator=False):
    started = time.monotonic()
    T, epsilon = m + 3, monomial(1)
    old_times = sparse.factors(m, 'economic')
    AN = [[Laurent.cast(1), row[1] * epsilon, row[2] * monomial(3)] for row in G]
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G, old_times) + [AN]
    raw, _ = residue.residue_matrix(T, A, P)
    blocks, labels = schur.partition(raw, T)
    for column, (_, _, a, b) in enumerate(labels['shared_new_column_labels']):
        inverse = pow(AN[a][b] * monomial(int(a == 0) + int(b == 0)), -1, P)
        for name in ('D', 'P', 'R'):
            for row in blocks[name]:
                row[column] = row[column] * inverse
    beta_factors = []
    for row, (t, _, a, b) in enumerate(labels['beta_row_labels']):
        X = residue.cross(A[t][a], AN[b], P)
        J = -A[t][a][b] * X[a] * X[b]
        beta_factors.append(dict(valuation=J.valuation, leading_coefficient=J.terms[0][1]))
        inverse = pow(J, -1, P)
        for name in ('B', 'R', 'S'):
            blocks[name][row] = [x * inverse for x in blocks[name][row]]
    G_inverse, _ = schur.invert([list(row) for row in G])
    AN_inverse = [[G_inverse[i][j] * monomial(-(0, 1, 3)[i]) for j in range(3)] for i in range(3)]
    old_matrix, _ = residue.residue_matrix(T - 1, A[:-1], P)
    old_inverse, _ = schur.invert(old_matrix)
    row = 0
    for u in range(2, T - 1):
        for v in range(u + 1, T - 1):
            for c in range(3):
                for d in range(3):
                    X = residue.cross(A[u][c], A[v][d], P)
                    U = [A[u][c][i] * X[i] % P for i in range(3)]
                    V = [A[v][d][i] * X[i] % P for i in range(3)]
                    LN = [residue.dot(r, X, P) for r in AN]
                    KN_inverse = [[pow(X[i], -1, P) * AN_inverse[i][j] * LN[j]
                                   for j in range(3)] for i in range(3)]
                    moved = residue.matmul([U, V], KN_inverse, P)
                    au, bu = residue.coordinates(moved[0], U, V, P)
                    av, bv = residue.coordinates(moved[1], U, V, P)
                    transform = [[au, av], [bu, bv]]
                    for name in ('O', 'D', 'E'):
                        blocks[name][row:row + 2] = schur.matrix_product(transform, blocks[name][row:row + 2])
                    row += 2
    assert all(not (Laurent.cast(x) - y).terms and Laurent.cast(x).precision > 0
               for rr, ss in zip(blocks['O'], old_matrix) for x, y in zip(rr, ss))
    Pinverse, polar_certificate = polar_inverse(blocks['P'])
    D = schur.matrix_product(old_inverse, blocks['D'])
    E = schur.matrix_product(old_inverse, blocks['E'])
    R = schur.matrix_difference(blocks['R'], schur.matrix_product(blocks['B'], D))
    S = schur.matrix_difference(blocks['S'], schur.matrix_product(blocks['B'], E))
    PinvQ = schur.matrix_product(Pinverse, blocks['Q'])
    H = schur.matrix_difference(S, schur.matrix_product(R, PinvQ))
    if leading_operator:
        result = leading_operator_diagnostic(m, A, blocks, PinvQ, old_inverse, D, E, H, labels)
        result['elapsed_seconds'] = time.monotonic() - started
        print(json.dumps(dict(m=m, diagnostic='leading_operator', valuations=result['minimum_valuations'],
                              ranks={name: cert['rank'] for name, cert in result['coefficient_rank_certificates'].items()},
                              seconds=result['elapsed_seconds'])), flush=True)
        return result
    known = [x.valuation for rr in H for x in rr if x]
    if not known:
        raise PrecisionFailure('No regular coefficient is known at the current precision.')
    valuation = min(known)
    leading = [[x.coefficient(valuation) for x in rr] for rr in H]
    leading_rank = residue.modular_rank(leading, P)
    row_orders = [min(x.valuation for x in rr if x) for rr in H]
    normalized = [[x * monomial(-row_orders[i]) for x in rr] for i, rr in enumerate(H)]
    column_orders = [min(normalized[i][j].valuation for i in range(len(H)) if normalized[i][j]) for j in range(len(H))]
    normalized = [[x * monomial(-column_orders[j]) for j, x in enumerate(rr)] for rr in normalized]
    normalized_leading = [[x.coefficient(0) for x in rr] for rr in normalized]
    normalized_rank = residue.modular_rank(normalized_leading, P)
    determinant = determinant_leading(H)
    # Independent first-jet check of the globally normalized leading matrix.
    # A full kernel-complement jet determines the leading determinant using
    # only two coefficient matrices and ordinary finite-field elimination.
    first = [[x.coefficient(valuation + 1) for x in rr] for rr in H]
    pivots, free, kernel = dual.rref_kernel(leading)
    change = [[int(i == c) for c in pivots] + [vector[i] for vector in kernel]
              for i in range(len(H))]
    jet = [[row0[c] for c in pivots]
           + [sum(x * y for x, y in zip(row1, vector)) % P for vector in kernel]
           for row0, row1 in zip(leading, first)]
    jet_certificate = residue.modular_rank(jet, P)
    jet_result = dict(rank_certificate=jet_certificate, kernel_basis_verified=True,
                      leading_pivot_columns=pivots, leading_free_columns=free)
    if jet_certificate['rank'] == len(H):
        change_determinant = residue.modular_rank(change, P)['determinant_mod_prime']
        jet_coefficient = jet_certificate['determinant_mod_prime'] * pow(change_determinant, -1, P) % P
        jet_order = len(H) * valuation + len(free)
        assert determinant['certified'] and determinant['valuation'] == jet_order
        assert determinant['leading_coefficient_mod_prime'] == jet_coefficient
        jet_result.update(independent_determinant_coefficient_verified=True,
                          determinant_valuation=jet_order, determinant_leading_coefficient_mod_prime=jet_coefficient)
    result = dict(m=m, prime=P, G=G, old_time_factors=old_times, new_times='epsilon,epsilon^3',
                  relative_inverse_precision=RELATIVE_PRECISION,
                  old_block_transport_to_constant_R_verified=True,
                  beta_row_normalizers_J=beta_factors, polar_inverse=polar_certificate,
                  regular_matrix_minimum_absolute_precision=minimum_precision(H),
                  regular_global_valuation=valuation, regular_global_leading_matrix=leading,
                  regular_global_leading_rank_certificate=leading_rank,
                  extra_row_monomial_orders=row_orders, extra_column_monomial_orders=column_orders,
                  row_column_normalized_leading_matrix=normalized_leading,
                  row_column_normalized_leading_rank_certificate=normalized_rank,
                  regular_determinant_leading=determinant,
                  global_kernel_complement_first_jet=jet_result,
                  precision_regression_checks_passed=True,
                  elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(m=m, H_valuation=valuation, H_leading_rank=leading_rank['rank'],
                          normalized_leading_rank=normalized_rank['rank'], size=len(H),
                          precision=minimum_precision(H), determinant=determinant,
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else value * 1024


def main():
    global RELATIVE_PRECISION
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--m', type=int, choices=(2, 3, 4, 5), default=2)
    parser.add_argument('--precision', type=int, choices=range(6, 13), default=10)
    parser.add_argument('--leading-operator-diagnostic', action='store_true',
                        help='Save the separate m=3, precision=6 leading-operator check; preserve main cases.')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.leading_operator_diagnostic and (args.m != 3 or args.precision != 6):
        parser.error('The bounded leading-operator diagnostic requires --m 3 --precision 6.')
    RELATIVE_PRECISION = args.precision
    started = time.monotonic()

    def resource_guard(_signum, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('Laurent exploration reached the 28-second cutoff.')
        # Leave headroom below the requested 100 MiB process budget.
        if maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('Laurent exploration reached the 95 MiB RSS guard (100 MiB budget).')

    signal.signal(signal.SIGALRM, resource_guard)
    signal.setitimer(signal.ITIMER_REAL, 0.05, 0.05)
    try:
        check_precision_rules()
        case = calculate(args.m, leading_operator=args.leading_operator_diagnostic)
    except (PrecisionFailure, TimeoutError) as error:
        case = dict(m=args.m, relative_inverse_precision=RELATIVE_PRECISION,
                    certified_result=False, limitation=str(error))
        print(json.dumps(case), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    case['maximum_rss_bytes'] = maximum_rss_bytes()
    result = dict(status='External exact precision-tracked Laurent calculation; no all-m or Lean theorem.',
                  normalization='Old-old row pairs transported by K_N^-1; regular beta rows divided by canonical J; shared-N columns divided by A_N(a,b)*epsilon^([a=0]+[b=0]).',
                  invertibility='All stated monomial and J normalizers are nonzero for nonzero formal epsilon. Polar kernel columns are divided by epsilon only after their constant term is verified zero.',
                  precision_rule='A scalar stores all coefficients below its absolute cutoff. Addition uses the minimum cutoff; multiplication uses min(p_a+v_b,p_b+v_a); inversion uses p_a-2v_a, capped at the requested relative precision. Unknown tails never certify zero.',
                  scope='A certified nonzero Laurent coefficient modulo the prime lifts after denominator clearing. Its finite-field leading order need not equal the real leading order.',
                  cases=[] if args.leading_operator_diagnostic else [case])
    if args.output:
        old = {}
        if args.output.exists():
            old = json.loads(args.output.read_text())
        if 'leading_operator_diagnostics' in old:
            result['leading_operator_diagnostics'] = old['leading_operator_diagnostics']
        if args.leading_operator_diagnostic:
            result['cases'] = old.get('cases', [])
            result['leading_operator_diagnostics'] = [x for x in old.get('leading_operator_diagnostics', [])
                                                       if (x.get('m'), x.get('relative_inverse_precision')) != (args.m, args.precision)] + [case]
        else:
            result['cases'] = [x for x in old.get('cases', []) if x.get('m') != args.m] + [case]
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
