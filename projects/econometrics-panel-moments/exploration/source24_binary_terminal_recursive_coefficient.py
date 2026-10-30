#!/usr/bin/env python3
"""Prescribed recursive binary-terminal coefficient diagnostic, n=2,3.

Use the shorter positive 8-power fixture, G=I+11^T, sector0, T=7.
The next old time is (1,delta,T). Only B_n and the saved 3-square W_n
are inverted; the singular enlarged B_(n+1) is never inverted.

theta=P_n*(G[:,1]/L_terminal), so phi_(n+1)=delta*theta+O(delta^2).
Normalize the three scalars (-X0*theta0,-X1*theta0,Lambda*chi_tilde)
with the reset-at-zero lift, then divide its output1 by X1. Exact dual
arithmetic handles chi's Q0 limit and this quotient's Q1 limit.

Cancel terminal scalar poles with j_c, use W_n to cancel the residual
M_n response with t_c, and normalize the resulting f. The reported
columns are (s0(f), k_f+z_1, T*s2(f)). Their determinant is the proposed
recursive first-delta coefficient; this diagnostic does not prove the
uniform coefficient identity or an arbitrary-length induction.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import time
import traceback

import source24_residue as residue
import source24_schur as schur
import source24_equal_weight_boundary as paired
import source24_binary_terminal_jet as dual
from source24_binary_terminal_response import Terminal, EDGES, NORMAL, G, P, inv, matvec


T = 7
E = [0, -1, 1]
LAMBDA = [1, 1, 2]


class Recursive:
    def __init__(self, n, saved_case, case_index):
        self.n, self.ctx, self.case_index = n, Terminal(n + 1), case_index
        assert self.ctx.m == n
        self.tables, self.R = self.ctx.tables, self.ctx.R
        assert saved_case['q'] == n + 1 and saved_case['terminal_time'] == [1, 0, T]
        assert saved_case['shorter_paired_matrix']['matrix'] == self.ctx.old['matrix']
        self.W = saved_case['response_matrix']
        assert residue.matrix_hash(self.W) == saved_case['response_certificate']['sha256']
        inverse_data = schur.invert(self.W)
        assert inverse_data is not None, 'The prescribed saved W_n is singular.'
        self.Winverse, self.Winverse_certificate = inverse_data
        theta_E = self.theta(E)
        beta_E = residue.dot(self.ctx.v(E), theta_E, P)
        self.k0 = (theta_E[0] - theta_E[2]) * inv(beta_E) % P
        self.k0_record = dict(point=E, theta=theta_E, beta_tilde=beta_E, k0_tilde=self.k0)
        self.chi_edge = self.chi_edge_derivative()
        self.old_node_data = [self.node_data(node, False) for node in self.ctx.old['node_records']]
        self.terminal_node_data = [self.node_data(node, True) for node in self.ctx.pole_records]
        self.control_points = [[1, z, -2 - z] for z in range(1, 3 * n + 8)]
        self.theta_controls = []
        for X in self.control_points:
            theta = self.theta(X)
            exact = self.direct_phi_delta(X)
            assert exact == [(0, value) for value in theta]
            self.theta_controls.append(dict(point=X, theta=theta, actual_phi_enlarged_dual=exact))

    def theta(self, X):
        whole = residue.word_product(self.ctx.kernels(X), list(range(1, self.n + 1)), P)
        L = self.ctx.terminal_forms(X)
        return matvec(whole, [G[i][1] * inv(L[i]) % P for i in range(3)])

    def theta_dual(self, X):
        kernels = {}
        for t in range(1, self.n + 1):
            A = [[dual.constant(value) for value in row] for row in self.tables[t]]
            forms = [dual.dot(row, X) for row in A]
            kernels[t] = [[dual.divide(dual.mul(A[i][j], X[j]), forms[i]) for j in range(3)] for i in range(3)]
        terminal = [[dual.constant(value) for value in row] for row in self.ctx.terminal]
        L = [dual.dot(row, X) for row in terminal]
        whole = dual.word_product(kernels, list(range(1, self.n + 1)))
        last = [dual.divide(dual.constant(G[i][1]), L[i]) for i in range(3)]
        return [dual.dot(row, last) for row in whole]

    def direct_phi_delta(self, X):
        """Actual extended word, differentiated in delta at a fixed X."""
        point = [dual.constant(value) for value in X]
        kernels = {t: [[dual.constant(value) for value in row] for row in matrix]
                   for t, matrix in self.ctx.kernels(X).items()}
        A = [[dual.mul(dual.constant(G[i][j]), [dual.ONE, (0, 1), (T, 0)][j])
              for j in range(3)] for i in range(3)]
        L = [dual.dot(row, point) for row in A]
        kernels[self.n + 1] = [[dual.divide(dual.mul(A[i][j], point[j]), L[i]) for j in range(3)]
                               for i in range(3)]
        whole = dual.word_product(kernels, list(range(1, self.n + 2)))
        return [dual.divide(row[1], point[1]) for row in whole]

    def chi_edge_derivative(self):
        X = [(0, 1), (P - 1, P - 2), (1, 0)]
        theta = self.theta_dual(X)
        v = [dual.mul(dual.constant(NORMAL[j]), X[j]) for j in range(3)]
        beta = dual.dot(v, theta)
        numerator = dual.add(dual.mul(X[2], dual.add(theta[0], dual.neg(theta[2]))),
                             dual.neg(dual.mul(dual.constant(self.k0), beta)))
        assert numerator[0] == 0
        Lambda = dual.dot([dual.constant(value) for value in LAMBDA], X)
        return dict(chart='X=(x,-2*x-1,1), at x=0.', point_and_derivative=X,
                    theta_dual=theta, beta_tilde_dual=beta, chi_numerator_dual=numerator,
                    chi_tilde_at_E=numerator[1], chi_tilde_at_Q0=-numerator[1] % P,
                    Lambda_chi_tilde_at_Q0=Lambda[0] * numerator[1] % P)

    def hhat(self, kind, X):
        theta = self.theta(X)
        if kind in (0, 1):
            return -X[kind] * theta[0] % P
        if X[0] % P == 0:
            assert residue.dot(NORMAL, X, P) == 0 and X[2] % P
            return self.chi_edge['Lambda_chi_tilde_at_Q0']
        beta = residue.dot(self.ctx.v(X), theta, P)
        numerator = X[2] * (theta[0] - theta[2]) - self.k0 * beta
        return residue.dot(LAMBDA, X, P) * numerator * inv(X[0]) % P

    def hhat_dual(self, kind, X):
        theta = self.theta_dual(X)
        if kind in (0, 1):
            return dual.neg(dual.mul(X[kind], theta[0]))
        v = [dual.mul(dual.constant(NORMAL[j]), X[j]) for j in range(3)]
        beta = dual.dot(v, theta)
        numerator = dual.add(dual.mul(X[2], dual.add(theta[0], dual.neg(theta[2]))),
                             dual.neg(dual.mul(dual.constant(self.k0), beta)))
        return dual.divide(dual.mul(dual.dot([dual.constant(value) for value in LAMBDA], X), numerator), X[0])

    def j(self, c, X):
        beta = residue.dot(self.ctx.v(X), self.ctx.z(X), P)
        return -G[c][0] * X[c] * inv(self.ctx.terminal_forms(X)[c]) * beta % P

    def direct_j(self, c, X):
        whole = residue.word_product(self.ctx.kernels(X), list(range(1, self.n + 1)), P)
        row = paired.rowmul(self.ctx.v(X), whole)
        return -G[c][0] * X[c] * inv(self.ctx.terminal_forms(X)[c] * X[1]) * row[1] % P

    def node_data(self, node, terminal):
        X = node['point']
        u = self.n + 1 if terminal else node['old_block']
        d = node['c'] if terminal else node['state']
        forms = self.ctx.old_forms(X)
        L = self.ctx.terminal_forms(X)
        kernels = {}
        for t in range(1, self.n + 1):
            if t == u:
                w = [self.tables[t][d][j] * X[j] % P for j in range(3)]
                kernels[t] = [[value if i == d else 0 for value in w] for i in range(3)]
            else:
                kernels[t] = residue.ordinary_kernel(self.tables, t, X, P)
        whole = residue.word_product(kernels, list(range(1, self.n + 1)), P)
        theta_residue = ([G[d][1] * row[d] % P for row in whole] if terminal else
                         matvec(whole, [G[i][1] * inv(L[i]) % P for i in range(3)]))
        cleared = {t: [[self.tables[t][i][j] * X[j] *
                        paired.product(forms[t][h] for h in range(3) if h != i) % P
                        for j in range(3)] for i in range(3)] for t in range(1, self.n + 1)}
        cleared_whole = residue.word_product(cleared, list(range(1, self.n + 1)), P)
        terminal_numerator = [G[i][1] * paired.product(L[h] for h in range(3) if h != i) % P
                              for i in range(3)]
        remaining = paired.product([forms[t][h] for t in range(1, self.n + 1) for h in range(3)
                                    if (t, h) != (u, d)] + [L[h] for h in range(3) if not (terminal and h == d)])
        polynomial = paired.scale(inv(remaining), matvec(cleared_whole, terminal_numerator))
        assert theta_residue == polynomial
        if terminal:
            beta = residue.dot(self.ctx.v(X), self.ctx.z(X), P)
            j_residues = [-G[c][0] * X[c] * beta % P if c == d else 0 for c in range(3)]
            assert j_residues[d]
            direct = -G[d][0] * X[d] * paired.rowmul(self.ctx.v(X), whole)[1] * inv(X[1]) % P
            assert direct == j_residues[d]
            t_residues = [0, 0, 0]
            assert node['terminal_residue_vector'][1] == 0
        else:
            phi_residue = [row[1] * inv(X[1]) % P for row in whole]
            beta_residue = residue.dot(self.ctx.v(X), phi_residue, P)
            j_residues = [-G[c][0] * X[c] * inv(L[c]) * beta_residue % P for c in range(3)]
            t_residues = [self.ctx.scalar_residue(c, node)[0] for c in range(3)]
        beta_tilde_residue = residue.dot(self.ctx.v(X), theta_residue, P)
        chi_residue = (X[2] * (theta_residue[0] - theta_residue[2]) - self.k0 * beta_tilde_residue) * inv(X[0]) % P
        hhat_residues = [-X[0] * theta_residue[0] % P, -X[1] * theta_residue[0] % P,
                         residue.dot(LAMBDA, X, P) * chi_residue % P]
        return dict(block=u, state=d, point=X, terminal_node=terminal,
                    theta_residue=theta_residue, theta_polynomial_clearing_verified=True,
                    beta_tilde_residue=beta_tilde_residue, hhat_residues=hhat_residues,
                    j_residues=j_residues, t_residues=t_residues,
                    actual_scalar_residue_controls_verified=True)

    def canonical_constants(self, scalar):
        values = [scalar(X) for X in EDGES]
        constants = paired.scale(-1, paired.rowmul([self.R[1][j] * values[j] % P for j in range(3)], G))
        return values, constants

    def response(self, scalar, scalar_residues, label):
        edge_values, constants = self.canonical_constants(scalar)
        s0, k, s2 = constants

        def lifted(X):
            coefficients = paired.rowmul([s0, (scalar(X) + k) % P, s2], self.R)
            L = self.ctx.terminal_forms(X)
            row = [(int(j == 0) * s0 * X[0] + int(j == 2) * T * s2 * X[2] - coefficients[j] * L[j]) % P
                   for j in range(3)]
            assert sum(row) % P == 0
            return row

        edge_rows = [lifted(X) for X in EDGES]
        assert all(edge_rows[j][j] == 0 for j in range(3))
        residues, residue_rows = [], []
        for value, node in zip(scalar_residues, self.ctx.old['node_records']):
            L = self.ctx.terminal_forms(node['point'])
            row = [-value * self.R[1][j] * L[j] % P for j in range(3)]
            assert sum(row) % P == 0
            residues.extend(row[:2])
            residue_rows.append(row)
        alpha = matvec(self.ctx.Binverse, residues)
        assert matvec(self.ctx.old['matrix'], alpha) == residues

        def actual_old(X):
            rows = self.ctx.old_rows(X)
            return [sum(value * row[j] for value, row in zip(alpha, rows)) % P for j in range(3)]

        lambda_value = (edge_rows[0][1] - actual_old(EDGES[0])[1]) % P
        headsum = [sum(alpha[i] for i, (family, t, c) in enumerate(self.ctx.old['column_labels'])
                       if family == 'H' and c == j) % P for j in range(3)]
        M = [(lambda_value * NORMAL[j] + headsum[j] - [s0, 0, T * s2][j]) % P for j in range(3)]
        controls = []
        for X in self.control_points:
            actual = actual_old(X)
            reconstructed = [(actual[j] + lambda_value * self.ctx.v(X)[j]) % P for j in range(3)]
            expected = lifted(X)
            assert reconstructed == expected, ('Canonical shorter-row reconstruction failed.', self.n, label, X,
                                                expected, reconstructed)
            controls.append(dict(point=X, scalar=scalar(X), lifted_old_row=expected,
                                 actual_paired_combination=actual, reconstructed_row=reconstructed))
        return dict(label=label, edge_values=edge_values, canonical_constants=constants, edge_rows=edge_rows,
                    scalar_old_residues=scalar_residues, lifted_old_row_residues=residue_rows,
                    actual_shorter_coefficients=alpha, lambda_value=lambda_value, headsum=headsum,
                    response=M, reconstruction_controls=controls,
                    cleared_denominator='D_old * product_c L_terminal,c * X0 * X1',
                    row_identity_degree_bound=3 * self.n + 6,
                    distinct_control_points=3 * self.n + 7)

    def column(self, kind):
        scalar = lambda X: self.hhat(kind, X)
        hhat_edges, reset = self.canonical_constants(scalar)
        s0, k, s2 = reset

        def reset_row(X):
            coefficients = paired.rowmul([s0, (scalar(X) + k) % P, s2], self.R)
            row = [(int(j == 0) * s0 * X[0] - coefficients[j] * G[j][0] * X[0]) % P for j in range(3)]
            assert sum(row) % P == 0
            return row

        reset_edges = [reset_row(X) for X in EDGES]
        assert all(reset_edges[j][j] == 0 for j in range(3))
        Q1_dual = [(1, 0), (0, 1), (P - 2, P - 1)]
        hhat_dual = self.hhat_dual(kind, Q1_dual)
        assert hhat_dual[0] == hhat_edges[1]
        coefficient1 = dual.total(dual.mul(value, dual.constant(self.R[i][1]))
                                  for i, value in enumerate([dual.constant(s0), dual.add(hhat_dual, dual.constant(k)), dual.constant(s2)]))
        row1_dual = dual.neg(dual.mul(dual.mul(Q1_dual[0], dual.constant(G[1][0])), coefficient1))
        assert row1_dual[0] == 0
        psi_Q1 = row1_dual[1]

        def psi(X):
            return psi_Q1 if X[1] % P == 0 else reset_row(X)[1] * inv(X[1]) % P

        def psi_residue(node):
            X = node['point']
            return -self.R[1][1] * G[1][0] * X[0] * inv(X[1]) * node['hhat_residues'][kind] % P

        a = [psi_residue(node) * inv(node['j_residues'][c]) % P
             for c, node in enumerate(self.terminal_node_data)]
        cancellations = []
        for node in self.terminal_node_data:
            remaining = (psi_residue(node) - residue.dot(a, node['j_residues'], P)) % P
            assert remaining == 0
            cancellations.append(dict(point=node['point'], state=node['state'], psi_residue=psi_residue(node),
                                      subtracted_j_residue=residue.dot(a, node['j_residues'], P), remaining=remaining))

        def h(X):
            return (psi(X) - sum(a[c] * self.j(c, X) for c in range(3))) % P

        h_residues = [(psi_residue(node) - residue.dot(a, node['j_residues'], P)) % P for node in self.old_node_data]
        Mh = self.response(h, h_residues, f'h_{kind}')
        z = matvec(self.Winverse, Mh['response'])
        assert matvec(self.W, z) == Mh['response']

        def fraw(X):
            return (-h(X) + sum(z[c] * self.ctx.scalar(c, X) for c in range(3))) % P

        fraw_edges, f_constants = self.canonical_constants(fraw)
        fs0, kf, fs2 = f_constants
        f = lambda X: (fraw(X) + kf) % P
        f_residues = [(-h_residues[i] + residue.dot(z, node['t_residues'], P)) % P
                      for i, node in enumerate(self.old_node_data)]
        Mf = self.response(f, f_residues, f'normalized_f_{kind}')
        assert Mf['response'] == [0, 0, 0], ('Normalized f has nonzero shorter response.', self.n, kind, Mf['response'])
        assert Mf['canonical_constants'] == [fs0, 0, fs2]
        b = (kf + z[1]) % P
        coefficient_column = [fs0, b, T * fs2 % P]
        controls = []
        for X in self.control_points:
            j_direct = [self.direct_j(c, X) for c in range(3)]
            t_direct = [self.ctx.direct_scalar(c, X) for c in range(3)]
            assert j_direct == [self.j(c, X) for c in range(3)]
            assert t_direct == [self.ctx.scalar(c, X) for c in range(3)]
            lhs = (psi(X) - residue.dot(a, j_direct, P) - residue.dot(z, t_direct, P) + f(X)) % P
            assert lhs == kf
            controls.append(dict(point=X, psi=psi(X), actual_j_scalars=j_direct, actual_t_scalars=t_direct,
                                 normalized_f=f(X), constant_identity_lhs=lhs, constant_identity_rhs=kf))
        return dict(kind=kind, hhat_name=['-X0*theta0', '-X1*theta0', 'Lambda*chi_tilde'][kind],
                    hhat_edge_values=hhat_edges, reset_canonical_constants=reset, reset_edge_rows=reset_edges,
                    psi_Q1_cancellation=dict(point_and_derivative=Q1_dual, hhat_dual=hhat_dual,
                                             reset_output1_dual=row1_dual, psi_edge_value=psi_Q1),
                    terminal_pole_coefficients_a=a, terminal_pole_cancellations=cancellations,
                    h_response=Mh, z=z, fraw_edge_values=fraw_edges,
                    fraw_canonical_constants_s0_kf_s2=f_constants, normalized_f_response=Mf,
                    actual_last_head1_margin_z1=z[1], b_equals_kf_plus_z1=b,
                    recursive_coefficient_column=coefficient_column,
                    constant_identity_controls=controls,
                    scalar_identity_degree_bound=3 * self.n + 5,
                    distinct_control_points=3 * self.n + 7)

    def calculate(self):
        columns = [self.column(kind) for kind in range(3)]
        matrix = [[column['recursive_coefficient_column'][j] for column in columns] for j in range(3)]
        return dict(shorter_n=self.n, enlarged_old_m=self.n + 1, terminal_T=T, sector=0,
                    fixture=self.ctx.fixture, shorter_geometry=self.ctx.geometry,
                    saved_response_case_field=f'cases[{self.case_index}]',
                    shorter_matrix_field=f'cases[{self.case_index}].shorter_paired_matrix.matrix',
                    shorter_matrix_sha256=residue.matrix_hash(self.ctx.old['matrix']),
                    shorter_inverse_certificate=self.ctx.Binverse_certificate,
                    W_field=f'cases[{self.case_index}].response_matrix', W=self.W,
                    W_sha256=residue.matrix_hash(self.W), W_inverse_certificate=self.Winverse_certificate,
                    k0_tilde_record=self.k0_record, chi_edge_derivative=self.chi_edge,
                    old_node_residue_controls=self.old_node_data, terminal_node_residue_controls=self.terminal_node_data,
                    actual_enlarged_phi_derivative_controls=self.theta_controls,
                    columns=columns, recursive_coefficient_matrix=matrix,
                    recursive_coefficient_certificate=paired.certificate(matrix),
                    singular_enlarged_matrix_inverted=False,
                    interpretation='Exact candidate recursive coefficient matrix at this finite fixture. Its identification with the full delta coefficient is a separate paper argument; no all-length claim is made.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('source24-binary-terminal-response-results.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or paired.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    raw = args.input.read_bytes()
    saved = json.loads(raw)
    assert saved['prime'] == P and saved['status'].startswith('PASS')
    result = dict(scope='One recursive coefficient diagnostic, n=2,3, fixed T=7; no delta/tau sweep or singular enlarged inverse.',
                  input_file=args.input.name, input_sha256=hashlib.sha256(raw).hexdigest(), prime=P,
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for n in (2, 3):
            index, saved_case = next((i, case) for i, case in enumerate(saved['cases']) if case['q'] == n + 1)
            case = Recursive(n, saved_case, index).calculate()
            result['cases'].append(case)
            print(json.dumps(dict(n=n, enlarged_m=n + 1, matrix=case['recursive_coefficient_matrix'],
                                  certificate=case['recursive_coefficient_certificate']['rank_certificate'])), flush=True)
        result['status'] = 'PASS: recursive coefficient matrices and all prescribed scalar/row reconstruction controls completed; zero ranks are retained.'
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
