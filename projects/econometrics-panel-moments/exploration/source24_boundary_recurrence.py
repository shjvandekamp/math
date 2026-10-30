#!/usr/bin/env python3
"""One-sector exact checks of LC94--LC102 at two nested saved fixtures.

Use sector a=0, old q=2 and q=3, from the saved weighted total-block3/4
source matrices. No full source matrix is regenerated. Strip X_a from
every circle residue and A_circle(a,b) from each head, reconstruct the
physical residue row, and normalize its projective representative onto
X0+X1+X2=1. All observation changes and source corrections remain explicit.

The q=1 shorter base is constructed directly from its two exclusive raw
paired-pole vectors. Ordinary actual-word controls retain the transported
head correction. The q=3 check also constructs LC99's interpolant and
tests LC98 and the plus-sign feedback in LC102. This is finite-field
regression at one prescribed sector/fixture, not a uniform rank theorem.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

import source24_residue as residue
import source24_schur as schur


P = 1000003
SECTOR = 0


def inv(x):
    assert x % P, 'A required denominator is zero.'
    return pow(x % P, -1, P)


def add(x, y):
    return [(a + b) % P for a, b in zip(x, y)]


def sub(x, y):
    return [(a - b) % P for a, b in zip(x, y)]


def scale(c, row):
    return [c * x % P for x in row]


def rowmul(row, matrix):
    return [sum(row[i] * matrix[i][j] for i in range(3)) % P for j in range(3)]


def combine(coefficients, rows):
    return [sum(c * row[j] for c, row in zip(coefficients, rows)) % P for j in range(3)]


def cert(matrix):
    return dict(shape=[len(matrix), len(matrix[0])], sha256=residue.matrix_hash(matrix),
                rank_certificate=residue.modular_rank(matrix, P))


def invert(matrix):
    result = schur.invert(matrix)
    assert result is not None, 'Prescribed finite matrix is singular.'
    return result


def maximum_rss_bytes():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return rss if sys.platform == 'darwin' else rss * 1024


class Sector:
    def __init__(self, tables, saved=None):
        self.tables, self.q = tables, len(tables) - 1
        self.normal = tables[0][SECTOR]
        n0, n1, n2 = self.normal
        x10, x11 = -n0 * inv(n1 - n0) % P, -(n2 - n0) * inv(n1 - n0) % P
        self.origin, self.direction = [(1 - x10) % P, x10, 0], [(-1 - x11) % P, x11, 1]
        assert all(self.direction)
        self.edges = [-self.origin[j] * inv(self.direction[j]) % P for j in range(3)]
        assert len(set(self.edges)) == 3
        self.labels = [['H', s, b] for s in range(1, self.q + 1) for b in range(3)]
        self.labels += [['J', t, c] for t in range(1, self.q + 1) for c in range(3)]
        self.inverses = {t: invert(tables[t])[0] for t in range(1, self.q + 1)}
        self.nodes = []
        for t in range(1, self.q + 1):
            for c in range(3):
                cross = residue.cross(self.normal, tables[t][c], P)
                normalization = inv(sum(cross))
                X = scale(normalization, cross)
                assert all(X) and X == self.point(X[2])
                forms = [[residue.dot(row, X, P) for row in table] for table in tables]
                assert [(u, a) for u in range(self.q + 1) for a in range(3) if not forms[u][a]] == [(0, SECTOR), (t, c)]
                slope = residue.dot(tables[t][c], self.direction, P)
                assert slope
                self.nodes.append(dict(block=t, state=c, point=X, z=X[2],
                                       original_cross=cross, projective_scale=normalization,
                                       line_slope=slope, row_forms=forms))
        self.B, self.normalization = self.read_matrix(saved)
        self.Binverse, self.Binverse_certificate = invert(self.B)
        self.Bcertificate = cert(self.B)

    def point(self, z):
        return [(x + z * y) % P for x, y in zip(self.origin, self.direction)]

    def v(self, X):
        return [self.normal[j] * X[j] % P for j in range(3)]

    def read_matrix(self, saved):
        output, records = [], []
        if saved is not None:
            assert saved['q'] == self.q + 1 and saved['prime'] == P
            matrix = saved['matrix']
            assert residue.matrix_hash(matrix) == saved['matrix_sha256']
            assert saved['fixture']['actual_coefficient_tables_mod_prime'] == self.tables
            assert all(saved['strong_geometry'].values())
            row_index = {tuple(label): i for i, label in enumerate(saved['row_labels'])}
            column_index = {tuple(label): i for i, label in enumerate(saved['column_labels'])}
            raw_columns = [[0, t, SECTOR, c] if kind == 'H' else [t, 0, c, SECTOR]
                           for kind, t, c in self.labels]
            column_ids = [column_index[tuple(label)] for label in raw_columns]
        for node in self.nodes:
            t, c, X = node['block'], node['state'], node['point']
            vectors = []
            if saved is None:
                assert self.q == 1
                old = [self.tables[t][c][j] * X[j] % P for j in range(3)]
                for kind, _, state in self.labels:
                    vectors.append(([0, 0, 0] if state != c else
                                    scale(-X[c], old) if kind == 'H' else
                                    scale(-self.tables[t][c][SECTOR] * X[c], self.v(X))))
            else:
                cross = node['original_cross']
                U = [self.normal[j] * cross[j] % P for j in range(3)]
                V = [self.tables[t][c][j] * cross[j] % P for j in range(3)]
                rr = [row_index[(0, t, SECTOR, c, coord)] for coord in ('alpha', 'beta')]
                common = inv(cross[SECTOR]) * node['projective_scale'] ** 2 % P
                factors = []
                for label, column in zip(self.labels, column_ids):
                    factor = common * (inv(self.normal[label[2]]) if label[0] == 'H' else 1) % P
                    factors.append(factor)
                    vectors.append(scale(factor, add(scale(matrix[rr[0]][column], U),
                                                    scale(matrix[rr[1]][column], V))))
                records.append(dict(saved_rows=rr, saved_columns=column_ids,
                                    raw_residue_basis=[U, V], vector_normalization_factors=factors))
            assert all(sum(vector) % P == 0 for vector in vectors)
            output += [[vector[j] for vector in vectors] for j in (0, 1)]
        return output, dict(source=('Saved actual double residues.' if saved else 'Direct exclusive two-block paired residues.'),
                            convention='Res_L Y at normalized X=cross/sum(cross), components0,1; component2 is minus their sum.',
                            records=records)

    def matrices(self, X, conjugated=False):
        matrices = {}
        for t in range(1, self.q + 1):
            table = self.tables[t]
            denominators = [residue.dot(row, X, P) for row in table]
            assert all(denominators)
            matrices[t] = [[table[i][j] * (X[i] if conjugated else X[j]) * inv(denominators[i]) % P
                            for j in range(3)] for i in range(3)]
        return matrices

    def values(self, X, divided=False):
        matrices, result = self.matrices(X, conjugated=True), []
        for kind, t, c in self.labels:
            word = ([t] + [s for s in range(1, self.q + 1) if s != t] if kind == 'H' else
                    [s for s in range(1, self.q + 1) if s != t])
            product = residue.word_product(matrices, word, P)
            if kind == 'H':
                ratios = [(int(c == j) - product[c][j]) % P for j in range(3)]
            else:
                g = self.tables[t][c][SECTOR] * X[c] * inv(residue.dot(self.tables[t][c], X, P)) % P
                ratios = scale(-g, rowmul(self.normal, product))
            result.append(ratios if divided else [ratios[j] * X[j] % P for j in range(3)])
        return result

    def direct_values(self, X):
        matrices, result = self.matrices(X), []
        for kind, t, c in self.labels:
            word = ([t] + [s for s in range(1, self.q + 1) if s != t] if kind == 'H' else
                    [s for s in range(1, self.q + 1) if s != t])
            product = residue.word_product(matrices, word, P)
            if kind == 'H':
                result.append([X[c] * (int(c == j) - product[c][j]) % P for j in range(3)])
            else:
                g = self.tables[t][c][SECTOR] * X[c] * inv(residue.dot(self.tables[t][c], X, P)) % P
                result.append(scale(-g, rowmul(self.v(X), product)))
        return result

    def inverse_kernel(self, X):
        L = [residue.dot(row, X, P) for row in self.tables[self.q]]
        return [[inv(X[i]) * self.inverses[self.q][i][j] * L[j] % P for j in range(3)] for i in range(3)]

    def head_correction(self, X, b):
        L = [residue.dot(row, X, P) for row in self.tables[self.q]]
        return [(self.inverses[self.q][b][j] * L[j] - int(b == j) * X[b]) % P for j in range(3)]

    def good_parameters(self, count):
        values, z = [], 1
        while len(values) < count:
            X = self.point(z)
            if all(X) and all(residue.dot(row, X, P) for table in self.tables[1:] for row in table):
                values.append(z)
            z += 1
            assert z < P
        return values


def transformed_observations(ctx):
    q, n = ctx.q, 6 * ctx.q
    transform = [[0] * n for _ in range(n)]
    records = []
    for node_index, node in enumerate(ctx.nodes):
        X, d = node['point'], node['state']
        V = ctx.inverse_kernel(X)
        basis = ([1, 0, -1], [0, 1, -1])
        transformed = [rowmul(row, V) for row in basis]
        if node['block'] < q:
            target_rows = [2 * node_index, 2 * node_index + 1]
            local = [[row[j] for row in transformed] for j in (0, 1)]
        else:
            j = (d + 1) % 3
            target_rows = [6 * (q - 1) + d, 6 * (q - 1) + 3 + d]
            functional = [inv(X[i]) * ctx.inverses[q][i][d] % P for i in range(3)]
            local = [[row[j] for row in transformed], [residue.dot(row, functional, P) for row in basis]]
        inverse, inverse_certificate = invert(local)
        for i in range(2):
            for j in range(2):
                transform[target_rows[i]][2 * node_index + j] = local[i][j]
        for column in range(n):
            original = [ctx.B[2 * node_index + j][column] for j in range(2)]
            observed = [residue.dot(row, original, P) for row in local]
            recovered = [residue.dot(row, observed, P) for row in inverse]
            assert recovered == original
        records.append(dict(block=node['block'], state=d, target_rows=target_rows,
                            local_matrix=local, local_inverse_certificate=inverse_certificate))
    return transform, schur.matrix_product(transform, ctx.B), records


def recursion(ctx, shorter):
    q, k, n = ctx.q, shorter.q, 6 * ctx.q
    assert k == q - 1 and ctx.tables[:-1] == shorter.tables
    transform, observed, changes = transformed_observations(ctx)
    earlier, active, canceled = list(range(6 * k)), list(range(6 * k, 6 * k + 3)), list(range(6 * k + 3, n))
    head = [ctx.labels.index(['H', q, d]) for d in range(3)]
    incoming = [ctx.labels.index(['J', q, d]) for d in range(3)]
    inherited = [ctx.labels.index(label) for label in shorter.labels]
    assert [[observed[i][j] for j in inherited] for i in earlier] == shorter.B
    assert all(not observed[i][j] for i in active for j in inherited)
    last_data, ratios, pivots = [], [], []
    for d in range(3):
        node = ctx.nodes[3 * (q - 1) + d]
        X, j, V = node['point'], (d + 1) % 3, ctx.inverse_kernel(node['point'])
        old_matrices = shorter.matrices(X)
        product = residue.word_product(old_matrices, list(range(1, q)), P)
        tail = residue.matmul(product, V, P)
        vq = [ctx.tables[q][d][i] * X[i] % P for i in range(3)]
        xi, eta = rowmul(vq, tail)[j], rowmul(ctx.v(X), tail)[j]
        assert xi
        ratio = ctx.tables[q][d][SECTOR] * eta * inv(xi) % P
        pivot = -X[d] * xi % P
        assert observed[active[d]][head[d]] == pivot
        assert observed[active[d]][incoming[d]] == -ctx.tables[q][d][SECTOR] * X[d] * eta % P
        assert all(not observed[active[c]][head[d]] and not observed[active[c]][incoming[d]] for c in range(3) if c != d)
        ratios.append(ratio)
        pivots.append(pivot)
        last_data.append(dict(state=d, active_component=j, xi=xi, eta=eta,
                              head_pivot=pivot, incoming_head_coefficient=ratio))
    combined = [[(observed[i][incoming[d]] - ratios[d] * observed[i][head[d]]) % P for d in range(3)] for i in range(n)]
    assert all(not any(combined[i]) for i in active)
    bdata = [combined[i] for i in earlier]
    alpha = schur.matrix_product(shorter.Binverse, bdata)
    assert schur.matrix_product(shorter.B, alpha) == bdata
    inherited_values = []
    for c in range(3):
        X = ctx.nodes[3 * (q - 1) + c]['point']
        values = shorter.direct_values(X)
        assert values == shorter.values(X)
        values = [add(row, ctx.head_correction(X, label[2])) if label[0] == 'H' else row
                  for label, row in zip(shorter.labels, values)]
        actual = [row[c] for row in values]
        assert actual == [observed[canceled[c]][i] for i in inherited]
        inherited_values.append(actual)
    canceled_C = [combined[i] for i in canceled]
    S = schur.matrix_difference(canceled_C, schur.matrix_product(inherited_values, alpha))
    Scertificate = cert(S)
    assert Scertificate['rank_certificate']['rank'] == 3
    row_order, col_order = active + earlier + canceled, head + inherited + incoming
    permuted = [[observed[i][j] for j in col_order] for i in row_order]
    determinant = cert(permuted)['rank_certificate']['determinant_mod_prime']
    factors = (pivots[0] * pivots[1] * pivots[2] * shorter.Bcertificate['rank_certificate']['determinant_mod_prime'] *
               Scertificate['rank_certificate']['determinant_mod_prime']) % P
    assert determinant == factors
    sign = schur.permutation_sign(row_order) * schur.permutation_sign(col_order)
    transform_certificate = cert(transform)
    assert determinant == (sign * transform_certificate['rank_certificate']['determinant_mod_prime'] *
                           ctx.Bcertificate['rank_certificate']['determinant_mod_prime']) % P

    parameters = ctx.good_parameters(3 * q + 2)
    controls, transported_checks = [], 0
    for z in parameters:
        X, V = ctx.point(z), ctx.inverse_kernel(ctx.point(z))
        full_values = ctx.direct_values(X)
        assert full_values == ctx.values(X)
        transported = [rowmul(row, V) for row in full_values]
        old_values = shorter.direct_values(X)
        assert old_values == shorter.values(X)
        old_transported = [add(row, ctx.head_correction(X, label[2])) if label[0] == 'H' else row
                           for label, row in zip(shorter.labels, old_values)]
        assert [transported[i] for i in inherited] == old_transported
        transported_checks += 3 * len(inherited)
        remainder = []
        for d in range(3):
            C = sub(transported[incoming[d]], scale(ratios[d], transported[head[d]]))
            remainder.append(sub(C, combine([row[d] for row in alpha], old_transported)))
        controls.append(dict(z=z, point=X, remainder_columns=remainder))
    z0, z1 = parameters[:2]
    slopes = [scale(inv(z1 - z0), sub(controls[1]['remainder_columns'][d], controls[0]['remainder_columns'][d])) for d in range(3)]
    constants = [sub(controls[0]['remainder_columns'][d], scale(z0, slopes[d])) for d in range(3)]
    for record in controls:
        assert record['remainder_columns'] == [add(constants[d], scale(record['z'], slopes[d])) for d in range(3)]
    for c in range(3):
        z = ctx.nodes[3 * (q - 1) + c]['z']
        assert [add(constants[d], scale(z, slopes[d]))[c] for d in range(3)] == S[c]
    record = dict(old_blocks=q, sector=SECTOR, normalized_B=ctx.B,
                  normalized_B_certificate=ctx.Bcertificate, normalization=ctx.normalization,
                  column_labels=ctx.labels, nodes=ctx.nodes,
                  observation_change_matrix=transform, observation_change_certificate=transform_certificate,
                  observation_changes=changes, transformed_observation_matrix=observed,
                  transformed_row_groups=dict(earlier=earlier, active_residue=active, canceled_value=canceled),
                  last_pivots=last_data, inherited_column_indices=inherited,
                  shorter_data_matrix=bdata, shorter_preimage_coefficients=alpha,
                  shorter_column_labels=shorter.labels, shorter_matrix_certificate=shorter.Bcertificate,
                  transported_shorter_canceled_values=inherited_values, canceled_C_values=canceled_C,
                  S_matrix=S, S_certificate=Scertificate,
                  determinant_identity=dict(row_permutation=row_order, column_permutation=col_order,
                                            permutation_sign=sign, permuted_determinant=determinant,
                                            pivot_shorter_S_product=factors, verified=True),
                  actual_word_controls=dict(points=controls, inherited_transport_component_checks=transported_checks,
                                            polynomial_constants=constants, polynomial_slopes=slopes,
                                            cleared_difference_degree_bound=3 * q + 1,
                                            argument='Every divided actual row times A_q^-1 diag(L_q) is cleared by the old product of3q row forms, with degree<=3q+1. These3q+2 distinct unit points certify the displayed affine remainder identity over this finite field.',
                                            canceled_values_match_polynomial=True))
    return record, dict(transform=transform, observed=observed, alpha=alpha, bdata=bdata,
                        last_data=last_data, S=S, canceled_C=canceled_C)


class Interpolant:
    def __init__(self, ctx, data):
        self.ctx, self.residues, self.coefficients = ctx, [], []
        for index, node in enumerate(ctx.nodes):
            vectors = [[data[2 * index][d], data[2 * index + 1][d],
                        -(data[2 * index][d] + data[2 * index + 1][d]) % P] for d in range(3)]
            self.residues.append([scale(inv(node['line_slope']), row) for row in vectors])
        for d in range(3):
            C = sum(self.residues[i][d][j] * inv(node['z'] - ctx.edges[j])
                    for i, node in enumerate(ctx.nodes) for j in range(3)) % P
            c0 = C * inv(ctx.edges[0] - ctx.edges[1]) % P
            self.coefficients.append([c0, -c0 % P, 0])

    def ratios(self, z, d):
        result = []
        for j in range(3):
            value = self.coefficients[d][j]
            for i, node in enumerate(self.ctx.nodes):
                value += self.residues[i][d][j] * inv(node['z'] - self.ctx.edges[j]) * inv(z - node['z'])
            result.append(value * inv(self.ctx.direction[j]) % P)
        return result

    def value(self, z, d):
        ratios, X = self.ratios(z, d), self.ctx.point(z)
        result = [ratios[j] * X[j] % P for j in range(3)]
        assert sum(result) % P == 0
        return result


def endpoint_feedback(current, shorter, current_runtime, shorter_runtime):
    k, q = shorter.q, current.q
    assert (k, q) == (2, 3)
    weights = [inv(r) for r in (2, 3, 5)]
    Sweight = (1 + sum(weights)) % P
    eta = {}
    for t in range(1, k + 1):
        eta[t] = [[0] * 3 for _ in range(3)]
        times = [1, 8 ** (t + 1) % P, 8 ** (2 * (t + 1)) % P]
        for b in range(3):
            active = [i for i in range(3) if i != b]
            A = shorter.tables[t]
            inverse, _ = invert([[A[i][j] for j in active] for i in active])
            solved = [sum(row[j] * A[active[j]][b] for j in range(2)) % P for row in inverse]
            for i, value in zip(active, solved):
                expected = times[b] * inv(times[i]) * weights[i] * inv(Sweight - weights[b]) % P
                assert value == expected
                eta[t][b][i] = value
    L = [[1 if b == i else -eta[k][b][i] % P for i in range(3)] for b in range(3)]
    Linverse, Lcertificate = invert(L)
    assert Lcertificate['determinant_mod_prime'] == Sweight ** 2 * inv(
        (Sweight - weights[0]) * (Sweight - weights[1]) * (Sweight - weights[2])) % P

    def phi(ratio_function):
        return [(lambda values: (values[b] - sum(eta[k][b][i] * values[i] for i in range(3) if i != b)) % P)(
            ratio_function(shorter.edges[b])) for b in range(3)]

    def psi(ratio_function):
        return [sum((eta[k - 1][b][i] - eta[k][b][i]) * ratio_function(shorter.edges[b])[i]
                    for i in range(3) if i != b) % P for b in range(3)]

    def completed(z, c, incoming):
        X = shorter.point(z)
        matrices = shorter.matrices(X, conjugated=True)
        product = residue.word_product(matrices, list(range(1, k)), P)
        if incoming:
            g = shorter.tables[k][c][SECTOR] * X[c] * inv(residue.dot(shorter.tables[k][c], X, P)) % P
            return scale(g, rowmul(shorter.normal, product))
        return residue.matmul(matrices[k], product, P)[c]

    Ccols, Dcols = [], []
    for c, datum in enumerate(shorter_runtime['last_data']):
        U = lambda z, c=c: completed(z, c, False)
        Vrow = lambda z, c=c: completed(z, c, True)
        Ccols.append(scale(inv(datum['xi']), psi(U)))
        Dcols.append(psi(lambda z, U=U, Vrow=Vrow, datum=datum:
                         sub(Vrow(z), scale(datum['incoming_head_coefficient'], U(z)))))
    C, D = [list(row) for row in zip(*Ccols)], [list(row) for row in zip(*Dcols)]
    alpha, bdata = current_runtime['alpha'], current_runtime['bdata']
    sigma = [[sum(alpha[i][d] for i, label in enumerate(shorter.labels) if label[0] == 'H' and label[2] == b) % P
              for d in range(3)] for b in range(3)]
    last_x = [alpha[shorter.labels.index(['H', k, c])] for c in range(3)]
    last_y = [alpha[shorter.labels.index(['J', k, c])] for c in range(3)]
    transformed_data = schur.matrix_product(shorter_runtime['transform'], bdata)
    rho = [[-transformed_data[6 * (k - 1) + c][d] * inv(shorter.nodes[3 * (k - 1) + c]['point'][c]) % P
            for d in range(3)] for c in range(3)]
    for c, datum in enumerate(shorter_runtime['last_data']):
        assert rho[c] == [(datum['xi'] * last_x[c][d] + shorter.tables[k][c][SECTOR] * datum['eta'] * last_y[c][d]) % P for d in range(3)]
    interpolant = Interpolant(shorter, bdata)
    phi_actual, phi_canonical, gauge = [], [], []
    for d in range(3):
        coefficients = [row[d] for row in alpha]
        actual_ratios = lambda z, coefficients=coefficients: combine(coefficients, shorter.values(shorter.point(z), divided=True))
        phi_actual.append(phi(actual_ratios))
        phi_canonical.append(phi(lambda z, d=d: interpolant.ratios(z, d)))
        points = shorter.good_parameters(3 * k + 2)
        z0 = points[0]
        difference = sub(combine(coefficients, shorter.direct_values(shorter.point(z0))), interpolant.value(z0, d))
        scalar = difference[0] * inv(shorter.v(shorter.point(z0))[0]) % P
        for z in points:
            actual = combine(coefficients, shorter.direct_values(shorter.point(z)))
            assert sub(actual, interpolant.value(z, d)) == scale(scalar, shorter.v(shorter.point(z)))
        gauge.append(scalar)
    phi_actual, phi_canonical = [list(row) for row in zip(*phi_actual)], [list(row) for row in zip(*phi_canonical)]
    Crho, Dy = schur.matrix_product(C, rho), schur.matrix_product(D, last_y)
    rhs = [[(phi_actual[i][d] + Crho[i][d] + Dy[i][d]) % P for d in range(3)] for i in range(3)]
    assert schur.matrix_product(L, sigma) == rhs
    Adata = schur.matrix_product(Linverse, [[(phi_canonical[i][d] + Crho[i][d]) % P for d in range(3)] for i in range(3)])
    Dbar = schur.matrix_product(Linverse, D)
    feedback_coefficients = schur.matrix_product(Dbar, last_y)
    assert sigma == [[(Adata[i][d] + feedback_coefficients[i][d] + gauge[d] * shorter.normal[i]) % P for d in range(3)] for i in range(3)]
    local, feedback = [], []
    for c in range(3):
        node = current.nodes[3 * (q - 1) + c]
        X, z = node['point'], node['z']
        local.append([(current_runtime['canceled_C'][c][d] - interpolant.value(z, d)[c] + X[c] * Adata[c][d]) % P for d in range(3)])
        feedback.append([X[c] * feedback_coefficients[c][d] % P for d in range(3)])
    assert current_runtime['S'] == [[(local[c][d] + feedback[c][d]) % P for d in range(3)] for c in range(3)]
    return dict(shorter_old_blocks=k, endpoint_eta=eta, endpoint_L=L, endpoint_L_inverse_certificate=Lcertificate,
                C_matrix=C, D_matrix=D, Dbar_matrix=Dbar, rho_matrix=rho,
                actual_last_incoming_coefficients=last_y, actual_head_sums=sigma,
                phi_actual=phi_actual, phi_canonical=phi_canonical, A_times_b=Adata,
                canonical_affine_residues=interpolant.residues, canonical_polynomial_coefficients=interpolant.coefficients,
                representative_gauge_scalars=gauge, gauge_control_parameters=shorter.good_parameters(3 * k + 2),
                gauge_cleared_degree_bound=3 * k + 1,
                LC98_verified=True, S_local=local, S_feedback=feedback,
                feedback_has_nonzero_entry=any(x for row in feedback for x in row), LC102_plus_sign_verified=True,
                endpoint_coordinate_cancellation='Divided actual rows are evaluated through J=diag(X/L)A; no coordinate-zero quotient is evaluated.',
                ordinary_residue_conversion='Res_z Y=(Res_L Y)/dL(X(z))/dz, after normalizing all saved projective points to sum(X)=1.')


def calculate(input_path):
    raw = input_path.read_bytes()
    data = json.loads(raw)
    cases = {case['q']: case for case in data['cases']}
    assert set(cases) >= {3, 4}
    tables = cases[4]['fixture']['actual_coefficient_tables_mod_prime']
    assert tables[:-1] == cases[3]['fixture']['actual_coefficient_tables_mod_prime']
    assert cases[4]['fixture']['r'] == [2, 3, 5]
    contexts = {1: Sector(tables[:2]), 2: Sector(tables[:3], cases[3]), 3: Sector(tables, cases[4])}
    records, runtime = {}, {}
    for q in (2, 3):
        records[q], runtime[q] = recursion(contexts[q], contexts[q - 1])
    feedback = endpoint_feedback(contexts[3], contexts[2], runtime[3], runtime[2])
    return dict(input_file=input_path.name, input_sha256=hashlib.sha256(raw).hexdigest(),
                saved_matrix_hashes={q: cases[q]['matrix_sha256'] for q in (3, 4)},
                fixture=cases[4]['fixture'], sector=SECTOR, full_source_matrices_regenerated=False,
                chart=dict(equation='sum(X)=1 on the circle line, parameter z=X2',
                           origin=contexts[3].origin, direction=contexts[3].direction, edge_parameters=contexts[3].edges),
                shorter_base=dict(B_matrix=contexts[1].B, certificate=contexts[1].Bcertificate,
                                  column_labels=contexts[1].labels, nodes=contexts[1].nodes),
                recursive_cases=[records[q] for q in (2, 3)], endpoint_feedback=feedback,
                limitations='One sector of one prescribed finite-field fixture. LC103--LC105 collision derivatives are not tested here; no uniform nonvanishing, old-source Schur conclusion, or all-period source independence is asserted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('source24-weighted-source-base-results.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second /95MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = dict(prime=P, scope='Sector0 only, old q=2,3 at nested saved weighted fixtures.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2))
    failure = None
    try:
        result['case'] = calculate(args.input)
        result['status'] = 'PASS: actual recursive S matrices, transported corrections, LC94/95 and LC98/102 controls.'
    except Exception as error:
        failure = error
        result.update(status='FAILED or incomplete fixed-fixture recurrence check.', error=str(error), traceback=traceback.format_exc())
    result['elapsed_seconds'], result['maximum_rss_bytes'] = time.monotonic() - started, maximum_rss_bytes()
    result['resource_measurement_scope'] = 'Calculation before JSON serialization; guard remains active while writing.'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps({key: result[key] for key in ('status', 'elapsed_seconds', 'maximum_rss_bytes')}), flush=True)
    if failure is not None:
        print(result['traceback'], flush=True)
        raise SystemExit(1)
    print(json.dumps([dict(old_blocks=case['old_blocks'], S=case['S_matrix'],
                           determinant=case['S_certificate']['rank_certificate']['determinant_mod_prime'])
                      for case in result['case']['recursive_cases']]), flush=True)


if __name__ == '__main__':
    main()
