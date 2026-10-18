#!/usr/bin/env python3
"""One finite diagnostic of the binary-terminal three-column response.

Use sector a=0, G=I+11^T, old times (1,8^s,8^(2s)), s=1,...,q-1,
and terminal time (1,0,7), for q=2,3,4 modulo 1000003. No parameter search,
full source matrix, or all-length assertion is involved. A singular response
here is a diagnostic of this degeneration, not a full paired-dependence proof.

The scalar t_c=(H_qc-rho_c J_qc)_1/X1 has its terminal pole canceled.
Its edge-normalized lift gives R_old=h_s-(s0,t_c+k,s2)G^-1 diag(Lq).
Solve its old residues in the actual paired basis, recover the polynomial
multiple lambda*v, and report M(t_c)=lambda*g+headsum-(s0,0,7*s2).
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


P = paired.P
G = paired.G
NORMAL = G[0]
TERMINAL_TIME = [1, 0, 7]
EDGES = [[0, 1, -1], [1, 0, -2], [1, -2, 0]]


def inv(value):
    assert value % P, 'A required denominator is zero at the prescribed fixture.'
    return pow(value % P, -1, P)


def matvec(matrix, vector):
    return [residue.dot(row, vector, P) for row in matrix]


def subtract(left, right):
    return [(x - y) % P for x, y in zip(left, right)]


class Terminal:
    def __init__(self, q):
        self.q, self.m = q, q - 1
        self.tables, self.fixture = paired.fixture(self.m)
        self.terminal = [[G[i][j] * TERMINAL_TIME[j] % P for j in range(3)] for i in range(3)]
        self.R, self.R_certificate = schur.invert(G)
        self.old = paired.calculate_sector(self.tables, 0)
        inverse_data = schur.invert(self.old['matrix'])
        assert inverse_data is not None, 'The prescribed shorter paired matrix is singular.'
        self.Binverse, self.Binverse_certificate = inverse_data
        self.geometry = paired.geometry_controls(self.tables)
        assert self.geometry['all_passed']
        self.ratios, self.pole_records = [], []
        for c in range(3):
            cross = residue.cross(NORMAL, self.terminal[c], P)
            X = paired.scale(inv(sum(cross)), cross)
            assert all(X)
            forms = self.terminal_forms(X)
            assert [d for d in range(3) if not forms[d]] == [c]
            kernels = self.kernels(X)
            product = residue.word_product(kernels, list(range(1, self.m + 1)), P)
            vc, v = self.vc(c, X), self.v(X)
            vp, vcp = paired.rowmul(v, product), paired.rowmul(vc, product)
            r = vcp[1] * inv(vp[1]) % P
            rho = r * inv(self.terminal[c][0]) % P
            self.ratios.append(dict(r=r, rho=rho))
            residual = paired.scale(-X[c], subtract(vcp, paired.scale(r, vp)))
            assert residual[1] == 0
            z = self.z(X)
            assert residue.dot(subtract(vc, paired.scale(r, v)), z, P) == 0
            self.pole_records.append(dict(c=c, point=X, terminal_row_forms=forms,
                                          old_row_forms=self.old_forms(X), rho=rho, r=r,
                                          terminal_residue_vector=residual,
                                          missing_output_residue_zero=True))

    def v(self, X):
        return [NORMAL[j] * X[j] % P for j in range(3)]

    def vc(self, c, X):
        return [self.terminal[c][j] * X[j] % P for j in range(3)]

    def old_forms(self, X):
        return {t: [residue.dot(row, X, P) for row in self.tables[t]]
                for t in range(1, self.m + 1)}

    def terminal_forms(self, X):
        return [residue.dot(row, X, P) for row in self.terminal]

    def kernels(self, X):
        return {t: residue.ordinary_kernel(self.tables, t, X, P) for t in range(1, self.m + 1)}

    def z(self, X):
        """Cancel X1 in P*e1 before evaluating any coordinate edge."""
        kernels = self.kernels(X)
        prefix = residue.word_product(kernels, list(range(1, self.m)), P)
        forms = self.old_forms(X)
        last = [self.tables[self.m][i][1] * inv(forms[self.m][i]) % P for i in range(3)]
        return matvec(prefix, last)

    def scalar(self, c, X):
        r = self.ratios[c]['r']
        row = subtract(self.vc(c, X), paired.scale(r, self.v(X)))
        return (int(c == 1) - X[c] * inv(self.terminal_forms(X)[c]) * residue.dot(row, self.z(X), P)) % P

    def direct_scalar(self, c, X):
        kernels = self.kernels(X)
        product = residue.word_product(kernels, list(range(1, self.m + 1)), P)
        terminal_kernel = residue.ordinary_kernel([self.terminal], 0, X, P)
        completed = residue.matmul(terminal_kernel, product, P)
        head = X[c] * (int(c == 1) - completed[c][1]) % P
        incoming = (-self.terminal[c][0] * X[c] * inv(self.terminal_forms(X)[c]) *
                    paired.rowmul(self.v(X), product)[1]) % P
        return (head - self.ratios[c]['rho'] * incoming) * inv(X[1]) % P

    def scalar_residue(self, c, node):
        u, d, X = node['old_block'], node['state'], node['point']
        forms = self.old_forms(X)
        w = [self.tables[u][d][j] * X[j] % P for j in range(3)]
        kernels = {t: ([[entry if i == d else 0 for entry in w] for i in range(3)]
                        if t == u else residue.ordinary_kernel(self.tables, t, X, P))
                   for t in range(1, self.m + 1)}
        prefix = residue.word_product(kernels, list(range(1, self.m)), P)
        last = ([self.tables[self.m][d][1] if i == d else 0 for i in range(3)]
                if u == self.m else
                [self.tables[self.m][i][1] * inv(forms[self.m][i]) % P for i in range(3)])
        res_z = matvec(prefix, last)
        product = residue.word_product(kernels, list(range(1, self.m + 1)), P)
        assert res_z == [row[1] * inv(X[1]) % P for row in product]
        cleared = {t: [[self.tables[t][i][j] * X[j] *
                        paired.product(forms[t][h] for h in range(3) if h != i) % P
                        for j in range(3)] for i in range(3)] for t in range(1, self.m + 1)}
        cleared_product = residue.word_product(cleared, list(range(1, self.m + 1)), P)
        remaining = paired.product(forms[t][h] for t in range(1, self.m + 1) for h in range(3)
                                   if (t, h) != (u, d))
        polynomial_res_z = [row[1] * inv(remaining * X[1]) % P for row in cleared_product]
        assert polynomial_res_z == res_z
        terminal_forms = self.terminal_forms(X)
        assert all(terminal_forms)
        r, rho = self.ratios[c]['r'], self.ratios[c]['rho']
        row = subtract(self.vc(c, X), paired.scale(r, self.v(X)))
        actual = -X[c] * inv(terminal_forms[c]) * residue.dot(row, res_z, P) % P
        terminal_kernel = residue.ordinary_kernel([self.terminal], 0, X, P)
        completed = residue.matmul(terminal_kernel, product, P)
        head_residue = -X[c] * completed[c][1] % P
        incoming_residue = (-self.terminal[c][0] * X[c] * inv(terminal_forms[c]) *
                            paired.rowmul(self.v(X), product)[1]) % P
        direct = (head_residue - rho * incoming_residue) * inv(X[1]) % P
        assert actual == direct
        return actual, dict(old_block=u, state=d, point=X, scalar_residue=actual,
                            z_residue=res_z, polynomial_clearing_verified=True,
                            actual_H_minus_rho_J_scalar_residue_verified=True)

    def old_rows(self, X):
        kernels, rows = self.kernels(X), []
        forms = self.old_forms(X)
        for kind, t, c in self.old['column_labels']:
            word = ([t] + [s for s in range(1, self.m + 1) if s != t]
                    if kind == 'H' else [s for s in range(1, self.m + 1) if s != t])
            product = residue.word_product(kernels, word, P)
            if kind == 'H':
                rows.append([X[c] * (int(c == j) - product[c][j]) % P for j in range(3)])
            else:
                factor = -self.tables[t][c][0] * X[c] * inv(forms[t][c]) % P
                rows.append(paired.scale(factor, paired.rowmul(self.v(X), product)))
        return rows

    def response(self, c):
        edge_scalars = [self.scalar(c, X) for X in EDGES]
        constants = paired.scale(-1, paired.rowmul([self.R[1][j] * edge_scalars[j] % P
                                                    for j in range(3)], G))
        s0, k, s2 = constants
        removed_head = [s0, 0, 7 * s2 % P]

        def lifted_row(X):
            f = (self.scalar(c, X) + k) % P
            coefficients = paired.rowmul([s0, f, s2], self.R)
            L = self.terminal_forms(X)
            C = [coefficients[j] * L[j] % P for j in range(3)]
            h = [s0 * X[0] % P, 0, 7 * s2 * X[2] % P]
            row = subtract(h, C)
            assert sum(row) % P == 0
            return row

        edge_rows = [lifted_row(X) for X in EDGES]
        assert all(edge_rows[j][j] == 0 for j in range(3))
        residues, records = [], []
        for node in self.old['node_records']:
            scalar_residue, record = self.scalar_residue(c, node)
            L = self.terminal_forms(node['point'])
            row = [-scalar_residue * self.R[1][j] * L[j] % P for j in range(3)]
            assert sum(row) % P == 0
            residues.extend(row[:2])
            record['lifted_old_row_residue'] = row
            records.append(record)
        alpha = matvec(self.Binverse, residues)
        assert matvec(self.old['matrix'], alpha) == residues

        def actual_old(X):
            rows = self.old_rows(X)
            return [sum(coefficient * row[j] for coefficient, row in zip(alpha, rows)) % P
                    for j in range(3)]

        lambda_value = (edge_rows[0][1] - actual_old(EDGES[0])[1]) % P
        assert self.v(EDGES[0])[1] == 1
        headsum = [sum(alpha[i] for i, (kind, t, state) in enumerate(self.old['column_labels'])
                       if kind == 'H' and state == j) % P for j in range(3)]
        response = subtract([(lambda_value * NORMAL[j] + headsum[j]) % P for j in range(3)],
                            removed_head)
        controls = []
        # After multiplying by D_old*L_qc, each coordinate has degree at most
        # 3m+2 on this line. The 3m+3 distinct points certify the row identity.
        for z in range(1, 3 * self.m + 4):
            X = [1, z, -2 - z]
            assert residue.dot(NORMAL, X, P) == 0
            assert self.scalar(c, X) == self.direct_scalar(c, X)
            product = residue.word_product(self.kernels(X), list(range(1, self.m + 1)), P)
            assert self.z(X) == [row[1] * inv(X[1]) % P for row in product]
            actual = actual_old(X)
            reconstructed = [(actual[j] + lambda_value * self.v(X)[j]) % P for j in range(3)]
            expected = lifted_row(X)
            assert reconstructed == expected, ('Old row reconstruction failed.', self.q, c, z,
                                                expected, reconstructed)
            controls.append(dict(z=z, point=X, scalar=self.scalar(c, X), lifted_old_row=expected,
                                 actual_old_paired_combination=actual, reconstructed_row=reconstructed))
        return dict(c=c, edge_scalars=edge_scalars, canonical_constants_s0_k_s2=constants,
                    edge_lifted_rows=edge_rows, scalar_and_lifted_residues=records,
                    old_paired_coefficients=alpha, polynomial_gauge_lambda=lambda_value,
                    actual_headsum=headsum, removed_head=removed_head, response=response,
                    old_residue_solve_verified=True, reconstruction_controls=controls,
                    polynomial_identity_degree_bound=3 * self.m + 2,
                    distinct_control_points=3 * self.m + 3)

    def calculate(self):
        columns = [self.response(c) for c in range(3)]
        matrix = [[column['response'][j] for column in columns] for j in range(3)]
        return dict(q=self.q, shorter_old_blocks=self.m, sector=0,
                    fixture=self.fixture, terminal_time=TERMINAL_TIME,
                    terminal_table=self.terminal, common_matrix_inverse=self.R,
                    common_inverse_certificate=self.R_certificate,
                    shorter_geometry=self.geometry, shorter_paired_matrix=self.old,
                    shorter_inverse_certificate=self.Binverse_certificate,
                    terminal_pole_cancellations=self.pole_records,
                    coordinate_edges=EDGES, columns=columns,
                    response_matrix=matrix, response_certificate=paired.certificate(matrix))


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
    result = dict(scope='One prescribed binary-terminal specialization, sector0, q=2,3,4; no search or full-source conclusion.',
                  interpretation='Singular M only diagnoses this terminal degeneration; it does not prove full paired dependence.',
                  prime=P, resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2), cases=[])
    failure = None
    try:
        for q in (2, 3, 4):
            case = Terminal(q).calculate()
            result['cases'].append(case)
            print(json.dumps(dict(q=q, matrix=case['response_matrix'],
                                  certificate=case['response_certificate']['rank_certificate'])), flush=True)
        result['status'] = 'PASS: all prescribed scalar-residue and actual-old-row reconstruction checks completed.'
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
