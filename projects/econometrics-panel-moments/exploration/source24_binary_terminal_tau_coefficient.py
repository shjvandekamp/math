#!/usr/bin/env python3
"""Test the proposed first-tau determinant coefficient at one old fixture.

Use G=I+11^T, sector a=0, old times (1,8^s,8^(2s)), s=1,...,m,
m=1,2,3 modulo 1000003. Only the shorter paired matrix is inverted.
There is no terminal inversion, singular terminal-node evaluation, tau
sweep, or parameter search.

phi=P*e1/X1 is evaluated after canceling X1 in the last kernel. Put
beta=v*phi, E=(0,-1,1), k0=(phi0-phi2)(E)/beta(E), and
chi_hat=[X2*(phi0-phi2)-k0*beta]/X0. Its removable edge value is obtained
with exact dual arithmetic along X=(x,-2*x-1,1). Lambda=(1,1,2)*X.

For f0 equal to t0(0), t1(0), or Lambda*chi_hat, use the canonical constants
(s0,k,s2)=-(R10*f0(Q0),R11*f0(Q1),R12*f0(Q2))*G, R=G^-1.
The old row is R0=s0*X0*e0-(s0,f0+k,s2)*R*diag(G[:,0]*X0).
Recover its actual shorter paired coefficients and polynomial multiple
lambda*v, then M0(f0)=lambda*g+headsum-(s0,0,0).

The tested claim identifies (1/g2) times this three-column determinant
with the first-tau coefficient of the terminal response determinant.
This script tests that coefficient matrix, not an all-length theorem.
The m=1 coefficient is expected to vanish.
"""

import argparse
import json
from pathlib import Path
import signal
import time
import traceback

import source24_residue as residue
import source24_schur as schur
import source24_equal_weight_boundary as paired
import source24_binary_terminal_jet as dual


P, G = paired.P, paired.G
NORMAL = G[0]
EDGES = [[0, 1, -1], [1, 0, -2], [1, -2, 0]]
E = [0, -1, 1]
LAMBDA_COEFFICIENTS = [NORMAL[c] * G[c][2] * pow(G[c][0], -1, P) % P for c in range(3)]


def inv(value):
    assert value % P, 'A required denominator is zero at the prescribed fixture.'
    return pow(value % P, -1, P)


def matvec(matrix, vector):
    return [residue.dot(row, vector, P) for row in matrix]


class Coefficient:
    def __init__(self, m):
        self.m = m
        self.tables, self.fixture = paired.fixture(m)
        self.old = paired.calculate_sector(self.tables, 0)
        inverse_data = schur.invert(self.old['matrix'])
        assert inverse_data is not None, 'The shorter paired matrix is singular.'
        self.Binverse, self.Binverse_certificate = inverse_data
        self.R, self.R_certificate = schur.invert(G)
        phi = self.phi(E)
        beta = residue.dot(self.v(E), phi, P)
        self.k0 = (phi[0] - phi[2]) * inv(beta) % P
        self.edge_derivative = self.canceled_edge_derivative()
        self.k0_record = dict(point=E, phi=phi, beta=beta, k0=self.k0)
        constant_normalization = paired.scale(-1, paired.rowmul(self.R[1], G))
        assert constant_normalization == [0, P - 1, 0]

    def v(self, X):
        return [NORMAL[j] * X[j] % P for j in range(3)]

    def forms(self, X):
        return {t: [residue.dot(row, X, P) for row in self.tables[t]] for t in range(1, self.m + 1)}

    def kernels(self, X):
        return {t: residue.ordinary_kernel(self.tables, t, X, P) for t in range(1, self.m + 1)}

    def phi(self, X):
        forms, kernels = self.forms(X), self.kernels(X)
        prefix = residue.word_product(kernels, list(range(1, self.m)), P)
        last = [self.tables[self.m][i][1] * inv(forms[self.m][i]) % P for i in range(3)]
        return matvec(prefix, last)

    def canceled_edge_derivative(self):
        X = [(0, 1), (P - 1, P - 2), (1, 0)]
        tables = {t: [[dual.constant(value) for value in row] for row in self.tables[t]]
                  for t in range(1, self.m + 1)}
        forms = {t: [dual.dot(row, X) for row in tables[t]] for t in tables}
        kernels = {t: [[dual.divide(dual.mul(tables[t][i][j], X[j]), forms[t][i]) for j in range(3)]
                       for i in range(3)] for t in tables}
        prefix = dual.word_product(kernels, list(range(1, self.m)))
        last = [dual.divide(tables[self.m][i][1], forms[self.m][i]) for i in range(3)]
        phi = [dual.dot(row, last) for row in prefix]
        whole = dual.word_product(kernels, list(range(1, self.m + 1)))
        assert phi == [dual.divide(row[1], X[1]) for row in whole]
        v = [dual.mul(dual.constant(NORMAL[j]), X[j]) for j in range(3)]
        beta = dual.dot(v, phi)
        numerator = dual.add(dual.mul(X[2], dual.add(phi[0], dual.neg(phi[2]))),
                             dual.neg(dual.mul(dual.constant(self.k0), beta)))
        assert numerator[0] == 0
        assert [value[0] for value in phi] == self.phi(E)
        Lambda = dual.dot([dual.constant(value) for value in LAMBDA_COEFFICIENTS], X)
        scalar_limit = Lambda[0] * numerator[1] % P
        return dict(chart='X=(x,-2*x-1,1), at x=0.', point_and_derivative=X,
                    phi_dual=phi, beta_dual=beta, chi_numerator_dual=numerator,
                    chi_hat_at_E=numerator[1], chi_hat_at_Q0=-numerator[1] % P,
                    Lambda_dual=Lambda, Lambda_chi_hat_at_Q0=scalar_limit,
                    convention='Q0=-E, so chi_hat changes sign and Lambda*chi_hat is unchanged.')

    def scalar(self, kind, X):
        phi = self.phi(X)
        if kind in (0, 1):
            return (int(kind == 1) - X[kind] * phi[0]) % P
        if X[0] % P == 0:
            assert residue.dot(NORMAL, X, P) == 0 and X[2] % P
            return self.edge_derivative['Lambda_chi_hat_at_Q0']
        beta = residue.dot(self.v(X), phi, P)
        chi_numerator = (X[2] * (phi[0] - phi[2]) - self.k0 * beta) % P
        return residue.dot(LAMBDA_COEFFICIENTS, X, P) * chi_numerator * inv(X[0]) % P

    def phi_residue(self, node):
        u, d, X = node['old_block'], node['state'], node['point']
        forms = self.forms(X)
        w = [self.tables[u][d][j] * X[j] % P for j in range(3)]
        kernels = {t: ([[entry if i == d else 0 for entry in w] for i in range(3)]
                        if t == u else residue.ordinary_kernel(self.tables, t, X, P))
                   for t in range(1, self.m + 1)}
        prefix = residue.word_product(kernels, list(range(1, self.m)), P)
        last = ([self.tables[self.m][d][1] if i == d else 0 for i in range(3)]
                if u == self.m else
                [self.tables[self.m][i][1] * inv(forms[self.m][i]) % P for i in range(3)])
        actual = matvec(prefix, last)
        whole = residue.word_product(kernels, list(range(1, self.m + 1)), P)
        assert actual == [row[1] * inv(X[1]) % P for row in whole]
        cleared = {t: [[self.tables[t][i][j] * X[j] *
                        paired.product(forms[t][h] for h in range(3) if h != i) % P
                        for j in range(3)] for i in range(3)] for t in range(1, self.m + 1)}
        cleared_whole = residue.word_product(cleared, list(range(1, self.m + 1)), P)
        numerator = [row[1] * inv(X[1]) % P for row in cleared_whole]
        remaining = paired.product(forms[t][h] for t in range(1, self.m + 1) for h in range(3)
                                   if (t, h) != (u, d))
        assert actual == paired.scale(inv(remaining), numerator)
        return actual, numerator, remaining

    def old_rows(self, X):
        forms, kernels, rows = self.forms(X), self.kernels(X), []
        for kind, t, c in self.old['column_labels']:
            word = ([t] + [s for s in range(1, self.m + 1) if s != t]
                    if kind == 'H' else [s for s in range(1, self.m + 1) if s != t])
            whole = residue.word_product(kernels, word, P)
            if kind == 'H':
                rows.append([X[c] * (int(c == j) - whole[c][j]) % P for j in range(3)])
            else:
                rows.append(paired.scale(-self.tables[t][c][0] * X[c] * inv(forms[t][c]),
                                         paired.rowmul(self.v(X), whole)))
        return rows

    def response(self, kind):
        edge_values = [self.scalar(kind, X) for X in EDGES]
        constants = paired.scale(-1, paired.rowmul([self.R[1][j] * edge_values[j] % P for j in range(3)], G))
        s0, k, s2 = constants

        def lifted_row(X):
            coefficients = paired.rowmul([s0, (self.scalar(kind, X) + k) % P, s2], self.R)
            row = [(int(j == 0) * s0 * X[0] - coefficients[j] * G[j][0] * X[0]) % P
                   for j in range(3)]
            assert sum(row) % P == 0
            return row

        edge_rows = [lifted_row(X) for X in EDGES]
        assert all(edge_rows[j][j] == 0 for j in range(3))
        assert edge_rows[0] == [0, 0, 0]
        residue_values, records = [], []
        for node in self.old['node_records']:
            X = node['point']
            res_phi, polynomial_phi, remaining = self.phi_residue(node)
            res_beta = residue.dot(self.v(X), res_phi, P)
            polynomial_beta = residue.dot(self.v(X), polynomial_phi, P)
            if kind in (0, 1):
                scalar_residue = -X[kind] * res_phi[0] % P
                polynomial_residue = -X[kind] * polynomial_phi[0] * inv(remaining) % P
            else:
                Lambda = residue.dot(LAMBDA_COEFFICIENTS, X, P)
                scalar_residue = Lambda * (X[2] * (res_phi[0] - res_phi[2]) - self.k0 * res_beta) * inv(X[0]) % P
                polynomial_residue = (Lambda * (X[2] * (polynomial_phi[0] - polynomial_phi[2]) -
                                                self.k0 * polynomial_beta) * inv(X[0] * remaining)) % P
            assert scalar_residue == polynomial_residue
            row = [-scalar_residue * self.R[1][j] * G[j][0] * X[0] % P for j in range(3)]
            assert sum(row) % P == 0
            residue_values.extend(row[:2])
            records.append(dict(old_block=node['old_block'], state=node['state'], point=X,
                                phi_residue=res_phi, beta_residue=res_beta, scalar_residue=scalar_residue,
                                lifted_old_row_residue=row, polynomial_clearing_verified=True))
        alpha = matvec(self.Binverse, residue_values)
        assert matvec(self.old['matrix'], alpha) == residue_values

        def actual_old(X):
            rows = self.old_rows(X)
            return [sum(coefficient * row[j] for coefficient, row in zip(alpha, rows)) % P for j in range(3)]

        lambda_value = -actual_old(EDGES[0])[1] % P
        assert self.v(EDGES[0])[1] == 1
        headsum = [sum(alpha[i] for i, (family, t, c) in enumerate(self.old['column_labels'])
                       if family == 'H' and c == j) % P for j in range(3)]
        response = [(lambda_value * NORMAL[j] + headsum[j] - (s0 if j == 0 else 0)) % P for j in range(3)]
        controls = []
        # Clearing D_old*X0 gives degree at most 3m+2 for the row difference.
        for z in range(1, 3 * self.m + 4):
            X = [1, z, -2 - z]
            assert residue.dot(NORMAL, X, P) == 0
            phi = self.phi(X)
            whole = residue.word_product(self.kernels(X), list(range(1, self.m + 1)), P)
            assert phi == [row[1] * inv(X[1]) % P for row in whole]
            weighted_scalars = sum(NORMAL[c] * (int(c == 1) - X[c] * phi[0]) for c in range(3)) % P
            assert weighted_scalars == NORMAL[1]
            actual = actual_old(X)
            reconstructed = [(actual[j] + lambda_value * self.v(X)[j]) % P for j in range(3)]
            expected = lifted_row(X)
            assert reconstructed == expected, ('Old row reconstruction failed.', self.m, kind, z, expected, reconstructed)
            controls.append(dict(z=z, point=X, scalar=self.scalar(kind, X), lifted_old_row=expected,
                                 actual_old_paired_combination=actual, reconstructed_row=reconstructed))
        return dict(scalar_name=['t0(0)', 't1(0)', 'Lambda*chi_hat'][kind], edge_values=edge_values,
                    canonical_constants_s0_k_s2=constants, edge_lifted_rows=edge_rows,
                    residue_records=records, old_paired_coefficients=alpha, polynomial_gauge_lambda=lambda_value,
                    actual_headsum=headsum, response=response, reconstruction_controls=controls,
                    polynomial_identity_degree_bound=3 * self.m + 2,
                    distinct_control_points=3 * self.m + 3,
                    constant_scalar_M0_is_zero=True, weighted_t_scalar_identity_verified=True)

    def calculate(self):
        columns = [self.response(kind) for kind in range(3)]
        matrix = [[column['response'][j] for column in columns] for j in range(3)]
        certificate = paired.certificate(matrix)
        determinant = certificate['rank_certificate']['determinant_mod_prime']
        return dict(m=self.m, total_blocks_q=self.m + 1, sector=0, fixture=self.fixture,
                    shorter_geometry=paired.geometry_controls(self.tables), shorter_paired=self.old,
                    shorter_inverse_certificate=self.Binverse_certificate, common_inverse=self.R,
                    common_inverse_certificate=self.R_certificate, k0_record=self.k0_record,
                    Lambda_coefficients=LAMBDA_COEFFICIENTS, canceled_edge_derivative=self.edge_derivative,
                    columns=columns, coefficient_matrix=matrix, coefficient_matrix_certificate=certificate,
                    coefficient_factor_inverse_g2=inv(NORMAL[2]),
                    claimed_first_tau_determinant_coefficient=determinant * inv(NORMAL[2]) % P,
                    terminal_nodes_evaluated=False, terminal_matrix_inverted=False,
                    interpretation='This tests the precise proposed coefficient matrix. Zero is retained, and no all-length conclusion follows from a finite nonzero value.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or paired.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(scope='One fixed-old tau-coefficient diagnostic, m=1,2,3, with no terminal inversion or tau sweep.',
                  prime=P, expected_m1_coefficient_zero=True,
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for m in (1, 2, 3):
            case = Coefficient(m).calculate()
            result['cases'].append(case)
            print(json.dumps(dict(m=m, matrix=case['coefficient_matrix'],
                                  certificate=case['coefficient_matrix_certificate']['rank_certificate'],
                                  claimed_first_tau_coefficient=case['claimed_first_tau_determinant_coefficient'])), flush=True)
        result['status'] = 'PASS: prescribed coefficient matrices and all scalar/row reconstruction controls completed; zero coefficients are diagnostic results.'
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete prescribed diagnostic; no replacement fixture used.',
                      error=str(error), traceback=traceback.format_exc())
    result['elapsed_seconds'] = time.monotonic() - started
    result['maximum_rss_bytes'] = paired.maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active during writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
