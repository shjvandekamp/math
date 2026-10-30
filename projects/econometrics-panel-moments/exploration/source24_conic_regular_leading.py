#!/usr/bin/env python3
"""Locally reconstruct the proposed odd conic regular leading coefficient.

The n=5 calculation uses actual prescribed words and raw pair-residue
components 0,1 at P_ij=(r_i*r_j,-r_i-r_j,1), never U/V frame coefficients.
It computes Hlead=U O^-1 D Z0, with Z0=E0-Bbar0*Lambda0.  Division by the
matching entry coordinate and the final output coordinate in U is performed
algebraically before X0=0.  A separate actual-K dual calculation checks that
regularization, and the old U/V implementation independently checks O and DZ0.

This is a finite modular reconstruction of the proposed coefficient, not a
proof of its asymptotic interpretation, a full-source theorem, or an all-n
nonvanishing statement.  No external code is downloaded or executed.
"""

import argparse
from contextlib import contextmanager
import itertools
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming
import source24_conic_transverse_jet as transverse


P = incoming.P
residue, schur, dual, regular = incoming.residue, incoming.schur, incoming.dual, incoming.regular
ALPHA = (1, 2, 3)
TIMES = (1, 5, 25, 125, 625)
G = tuple((1, a, a*a) for a in ALPHA)


def scale(c, row):
    return [c*x % P for x in row]


def row_product(row, matrix):
    return schur.matrix_product([row], matrix)[0]


@contextmanager
def common_matrix():
    previous = incoming.G
    incoming.G = G
    try:
        yield
    finally:
        incoming.G = previous


class Fixture:
    def __init__(self, n):
        assert n == 5, 'This bounded task only runs the specified nonsingular n=5 fixture.'
        self.n = n
        self.old = list(range(2, n+2))
        self.nodes = {t: [a*TIMES[t-2] for a in ALPHA] for t in self.old}
        self.A = [[list(row) for row in G] for _ in range(n+2)]
        for t in self.old:
            self.A[t] = [[1, r, r*r] for r in self.nodes[t]]
        self.old_columns = [(t, s, a, b) for t in self.old for s in self.old if t != s
                            for a in range(3) for b in range(3)]
        self.incoming_columns = [(t, a, c) for t in self.old for a in range(3) for c in range(3)]
        self.outgoing_columns = [(c, s, j) for c in range(3) for s in self.old for j in range(3)]
        self.first = {t: min(s for s in self.old if s != t) for t in self.old}
        Ginv, _ = schur.invert([list(row) for row in G])
        self.ell2 = Ginv[2]
        assert sum(self.ell2) % P == 0
        self.pairs = []
        for u, v in itertools.combinations(self.old, 2):
            for a, b in itertools.product(range(3), repeat=2):
                x, y = self.nodes[u][a], self.nodes[v][b]
                self.pairs.append(dict(u=u, v=v, a=a, b=b, x=x, y=y,
                                       point=[x*y % P, -(x+y) % P, 1]))
        flat = [(t, a, self.nodes[t][a]) for t in self.old for a in range(3)]
        assert len({r for _, _, r in flat}) == 3*n
        for (u, a, x), (v, b, y) in itertools.combinations(flat, 2):
            X = [x*y % P, -(x+y) % P, 1]
            assert all(X)
            for t, c, z in flat:
                value = residue.dot(self.A[t][c], X, P)
                assert value == (z-x)*(z-y) % P
                assert (value == 0) == ((t, c) in ((u, a), (v, b)))

    def word(self, t, s):
        return [s]+[u for u in self.old if u not in (t, s)]

    def pair_kernels(self, pair):
        u, v, a, b, X = (pair[k] for k in ('u', 'v', 'a', 'b', 'point'))
        result = {}
        for t in self.old:
            if t in (u, v):
                state = a if t == u else b
                vector = [self.A[t][state][c]*X[c] % P for c in range(3)]
                result[t] = [vector[:] if c == state else [0]*3 for c in range(3)]
            else:
                result[t] = residue.ordinary_kernel(self.A, t, X, P)
        return result

    def pair_prefactor(self, pair, t, a):
        u, v, cu, cv, X = (pair[k] for k in ('u', 'v', 'a', 'b', 'point'))
        if (t == u and a != cu) or (t == v and a != cv):
            return 0
        return X[a] if t in (u, v) else X[a]*pow(residue.dot(self.A[t][a], X, P), -1, P) % P

    def pair_matrices(self):
        O, E, Bbar = [], [], []
        for pair in self.pairs:
            X = pair['point']
            kernels = self.pair_kernels(pair)
            completed = {(t, s): residue.word_product(kernels, self.word(t, s), P)
                         for t in self.old for s in self.old if t != s}
            omitted = {t: residue.word_product(kernels, [u for u in self.old if u != t], P)
                       for t in self.old}
            moved = {s: residue.word_product(kernels, residue.ordered_word(self.old, s), P)
                     for s in self.old}
            old_vectors, incoming_vectors, outgoing_vectors = [], [], []
            for t, s, a, b in self.old_columns:
                f = -self.pair_prefactor(pair, t, a)*self.A[t][a][b]*X[b] % P
                old_vectors.append(scale(f, completed[t, s][b]))
            for t, a, c in self.incoming_columns:
                # The e_c term has at most one old pole and no double residue.
                f = -self.pair_prefactor(pair, t, a)*pow(self.nodes[t][a], c, P)*X[c] % P
                incoming_vectors.append(scale(f, omitted[t][0]))
            for c, s, j in self.outgoing_columns:
                # The identity term likewise has no double old residue.
                f = -X[c]*X[j]*pow(X[0], -1, P) % P
                outgoing_vectors.append(scale(f, moved[s][j]))
            assert all(sum(v) % P == 0 for v in old_vectors+incoming_vectors+outgoing_vectors)
            for c in range(2):
                O.append([v[c] for v in old_vectors])
                E.append([v[c] for v in incoming_vectors])
                Bbar.append([v[c] for v in outgoing_vectors])
        return O, E, Bbar

    def raw_components(self, uv):
        """Undo the existing cross-point/U,V convention, including its scale."""
        answer = []
        for k, pair in enumerate(self.pairs):
            u, v, a, b, X = (pair[key] for key in ('u', 'v', 'a', 'b', 'point'))
            cross = residue.cross(self.A[u][a], self.A[v][b], P)
            factor = (pair['y']-pair['x']) % P
            assert cross == scale(factor, X)
            inv = pow(factor*factor % P, -1, P)
            U = [self.A[u][a][c]*X[c] % P for c in range(3)]
            V = [self.A[v][b][c]*X[c] % P for c in range(3)]
            for c in range(2):
                answer.append([(x*U[c]+y*V[c])*inv % P for x, y in zip(uv[2*k], uv[2*k+1])])
        return answer

    def lambda0(self):
        cvalues = {}
        for t in self.old:
            s = self.first[t]
            y = self.nodes[s][0]
            X = (0, -y % P, 1)
            beta, gamma = self.nodes[t][1:]
            d = y*(beta-gamma)*pow((beta-y)*(gamma-y) % P, -1, P) % P
            K = residue.ordinary_kernel(self.A, t, X, P)
            assert d == (K[1][1]*K[2][2]-K[1][2]*K[2][1]) % P and d
            for a in range(3):
                cvalues[t, a] = X[a]*pow(residue.dot(self.A[t][a], X, P)*d % P, -1, P) % P
        matrix = [[pow(self.nodes[t][a], incoming_state, P)*cvalues[t, a] % P
                   if (c, s, j) == (incoming_state, self.first[t], 0) else 0
                   for t, a, incoming_state in self.incoming_columns]
                  for c, s, j in self.outgoing_columns]
        assert all(cvalues[t, 0] == 0 for t in self.old)
        return matrix, cvalues

    def divided_U(self):
        U, row_labels, marginal_checks, physical_checks = [], [], 0, 0
        for u in self.old:
            for a in range(3):
                r = self.nodes[u][a]
                X = (0, -r % P, 1)
                J = {t: [[X[d]*self.A[t][d][c]*pow(residue.dot(self.A[t][d], X, P), -1, P) % P
                          for c in range(3)] for d in range(3)] for t in self.old if t != u}
                cache = {(): residue.identity()}

                def product(word):
                    key = tuple(word)
                    if key not in cache:
                        cache[key] = residue.word_product(J, word, P)
                    return cache[key]

                vectors = []
                for t, s, Astate, b in self.old_columns:
                    word = self.word(t, s)
                    if t == u:
                        value = scale(self.A[u][a][b], product(word)[b]) if Astate == a else [0]*3
                    else:
                        position = word.index(u)
                        before, after = product(word[:position]), product(word[position+1:])
                        f = X[Astate]*self.A[t][Astate][b]*pow(residue.dot(self.A[t][Astate], X, P), -1, P) % P
                        value = scale(f*before[b][a], row_product(self.A[u][a], after))
                    expected = r*r*(int(b == 2)-int(b == 1))*int((u, a) == (t, Astate)) % P
                    assert (-r*value[1]+value[2]) % P == expected
                    marginal_checks += 1
                    vectors.append(value)
                # Independent actual-K residue calculation with final output
                # factor canceled, then the removable matching X_a divided.
                Xjet = ((0, 1), (-r % P, -pow(r, -1, P) % P), (1, 0))
                regular.geometry_at_point(self.A, (u, a), Xjet)
                normal = {t: regular.kernel_or_residue(self.A, t, (u, a), Xjet, False) for t in self.old}
                stripped = {t: regular.kernel_or_residue(self.A, t, (u, a), Xjet, True) for t in self.old}
                words = {}
                for t in self.old:
                    for s in self.old:
                        if t == s:
                            continue
                        word, value = self.word(t, s), dual.identity()
                        for pos, block in enumerate(word):
                            value = dual.mmul(value, stripped[block] if pos == len(word)-1 else normal[block])
                        words[t, s] = value
                for label, expected in zip(self.old_columns, vectors):
                    t, s, Astate, b = label
                    if t == u and Astate != a:
                        value = [dual.ZERO]*3
                    else:
                        f = dual.scale(self.A[t][Astate][b], dual.mul(Xjet[Astate], Xjet[b]))
                        if t != u:
                            f = dual.mul(f, dual.inverse(regular.dot(self.A[t][Astate], Xjet)))
                        value = [dual.mul(f, entry) for entry in words[t, s][b]]
                    if a == 0:
                        assert all(x[0] == 0 for x in value)
                        actual = [x[1] for x in value]
                    else:
                        actual = [x[0]*pow(X[a], -1, P) % P for x in value]
                    assert actual == expected, ('Divided U mismatch', (u, a), label)
                    physical_checks += 3
                for c in range(3):
                    U.append([v[c] for v in vectors])
                    row_labels.append((u, a, c))
        return U, row_labels, marginal_checks, physical_checks

    def outgoing_M0(self):
        nodes = [self.nodes[t] for t in self.old]
        matrix = []
        for u in range(self.n):
            for a, y in enumerate(nodes[u]):
                kernels = [transverse.kernel(nodes, t, y, (u, a)) for t in range(self.n)]
                row = []
                for s in range(self.n):
                    row.extend(x[0] for x in transverse.scalar_columns(
                        transverse.product(kernels, transverse.word(self.n, s)), y))
                # Separate scalar kernel construction at x=0: ordinary-y
                # residue of 1/L_i is -1/r_i, not an L_i-residue.
                X, ordinary = (0, -y % P, 1), {}
                for t in self.old:
                    if t == u+2:
                        v = [-self.A[t][a][c]*X[c]*pow(y, -1, P) % P for c in range(3)]
                        ordinary[t] = [v[:] if state == a else [0]*3 for state in range(3)]
                    else:
                        ordinary[t] = residue.ordinary_kernel(self.A, t, X, P)
                direct = []
                for s in self.old:
                    product = residue.word_product(ordinary, residue.ordered_word(self.old, s), P)
                    direct.extend(((-y*y)*product[0][2] % P,
                                   y*y*product[1][2] % P, -y*product[2][2] % P))
                assert direct == row
                matrix.append(row)
        return matrix


def calculate():
    fixture = Fixture(5)
    O, E0, Bbar0 = fixture.pair_matrices()
    old_uv, geometry = residue.residue_matrix(fixture.n+2, fixture.A, P)
    assert fixture.raw_components(old_uv) == O
    Lambda0, cvalues = fixture.lambda0()
    Z0 = schur.matrix_difference(E0, schur.matrix_product(Bbar0, Lambda0))
    DZ0 = []
    for k, pair in enumerate(fixture.pairs):
        z2 = [(-x-y) % P for x, y in zip(Z0[2*k], Z0[2*k+1])]
        for c in range(2):
            DZ0.append(scale(pair['x']*pair['y']*fixture.ell2[c], z2))
    # Earlier independently implemented odd incoming formula, in its original
    # cross-point U/V coordinates; convert, rather than silently mix frames.
    with common_matrix():
        prior_DZ0, _, prior_cvalues = incoming.incoming_coefficients(fixture.n, fixture.A)
    assert prior_cvalues == cvalues
    assert fixture.raw_components(prior_DZ0) == DZ0

    U, Ulabels, marginal_checks, physical_checks = fixture.divided_U()
    M0 = fixture.outgoing_M0()
    M_certificate = incoming.matrix_certificate(M0)
    Y, solve_certificate = incoming.solve_old_source(O, DZ0)
    result = dict(n=fixture.n, prime=P, alpha=ALPHA, times=TIMES,
                  nodes=fixture.nodes, common_G=G, ell2=fixture.ell2,
                  coordinate_convention='Each old pair uses P=(r_i*r_j,-r_i-r_j,1); rows are actual residue components 0,1. Cross-point U/V coordinates are converted using cross=(r_j-r_i)P and the square inverse scale.',
                  old_pair_labels=fixture.pairs,
                  old_pair_row_order='For each listed pair, component 0 then component 1.',
                  old_source_column_labels=fixture.old_columns,
                  incoming_column_labels=fixture.incoming_columns,
                  outgoing_column_labels=fixture.outgoing_columns,
                  U_row_labels=Ulabels,
                  U_definition='Res_(L_ua)(Qhat_old)_c/(X_a*X_c) at X=(0,-r_ua,1), with both factors canceled before evaluation.',
                  D_definition='On each pair vector z, return r_i*r_j*z_2*ell2, z_2=-z_0-z_1; retain components 0,1.',
                  old_geometry=geometry, all_conic_pair_geometry_verified=True,
                  raw_O_matches_existing_UV_residues=True,
                  DZ0_matches_independent_odd_incoming_formula=True,
                  lambda_scalar_values=[dict(t=t, a=a, value=v) for (t, a), v in sorted(cvalues.items())],
                  lambda_nonzero_entries=[dict(row=i, column=j, value=x) for i, row in enumerate(Lambda0)
                                          for j, x in enumerate(row) if x],
                  U_marginal_checks=marginal_checks,
                  U_actual_K_regularization_component_checks=physical_checks,
                  outgoing_M0=M0, outgoing_M0_certificate=M_certificate,
                  outgoing_M0_row_order='(old block,state), block first; old blocks use the listed order.',
                  outgoing_M0_column_order='(move-first old block,j), block first.',
                  outgoing_M0_normalization='Ordinary-y residues at y=r_ua of y*e0*P_s*h_x, -(x+y)*e1*P_s*h_x, e2*P_s*h_x at x=0; h_x=(x,0,-y).',
                  outgoing_M0_independent_component_checks=len(M0)**2,
                  matrix_hashes={name: residue.matrix_hash(matrix) for name, matrix in
                                 (('O', O), ('U', U), ('E0', E0), ('Bbar0', Bbar0),
                                  ('Lambda0', Lambda0), ('Z0', Z0), ('DZ0', DZ0))},
                  old_source_solve=solve_certificate)
    if Y is None:
        result['limitation'] = 'Old source matrix is singular at this fixture; Hlead was not formed.'
        return result
    Hlead = schur.matrix_product(U, Y)
    H_certificate = incoming.matrix_certificate(Hlead)
    kappa = pow(pow(ALPHA[0], 9, P)*pow(ALPHA[1], 6, P)*pow(ALPHA[2], 3, P) % P, fixture.n, P)
    for b in TIMES:
        kappa = kappa*pow(b, 12, P) % P
    determinant = H_certificate['rank_certificate']['determinant_mod_prime']
    actual = dict(O=solve_certificate['determinant_mod_prime'],
                  M0=M_certificate['rank_certificate']['determinant_mod_prime'],
                  Hlead=determinant, kappa=kappa, leading_coefficient=kappa*determinant % P)
    claimed = dict(O=969253, M0=155046, Hlead=214966, kappa=528352, leading_coefficient=375301)
    result.update(Hlead=Hlead, Hlead_certificate=H_certificate,
                  Hlead_definition='U * solve(O,DZ0), with the exact O*Y=DZ0 equation verified.',
                  kappa_definition='(alpha0^9*alpha1^6*alpha2^3)^n * product_t b_t^12.',
                  determinants_and_coefficient=actual, external_claims=claimed,
                  claimed_values_match={name: actual[name] == value for name, value in claimed.items()},
                  limitation='Only the locally reconstructed finite coefficient is checked. Its asymptotic interpretation is a separate paper audit; no full source or uniform-n conclusion is made.')
    print(json.dumps(dict(n=fixture.n, **actual, all_claims_match=actual == claimed)), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, case, limitation = time.monotonic(), None, None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        case = calculate()
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Independent local finite reconstruction of the proposed n=5 conic regular leading coefficient.',
                  scope='Actual ordered words and raw pair-residue coordinates; no external downloaded code, no n=3 inverse, and no uniform rank claim.',
                  elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(), bounded_limitation=limitation, case=case)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('elapsed_seconds', 'maximum_rss_bytes', 'bounded_limitation')}), flush=True)


if __name__ == '__main__':
    main()
