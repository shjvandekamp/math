#!/usr/bin/env python3
"""Actual adjacent-edge first jets, separated by channel and pole order.

For q=3,4 the coefficient domain is the direct sum of the actual 15-dimensional
ker M_k in RQ35--RQ40 of SOURCE24_RAW_QUOTIENT.md.  The old time directions are
(t,t^2), so different edges retain their different increments (1,2k+1).
Every reported quotient uses the SAME 18 common leading columns.  In particular,
new-pole and axis ranks are not added after separate leading-image quotients.

On a new line the scalar restrictions have only the three old poles, order at
most q, and polynomial remainder of degree at most two: the divided residue is
multiplied by A_N^-1 diag(L_N).  On an axis C is bounded at infinity, with old
poles of order at most q and fixed new poles of order at most one.  Thus exact
principal coefficients and a quadratic/constant remainder determine these
rational functions.  The remainder is fitted at three/one ordinary points and
reconstructed at three further points against a separate actual-word dual
evaluator.  Laurent cutoffs are tracked, never interpreted as exact zero tails.

The profiles are finite-field diagnostics of these fixtures, not a uniform
injectivity theorem or a real/generic upper bound inferred from a zero minor.
"""

import argparse
from contextlib import contextmanager
import json
from pathlib import Path
import signal
import time

import source24_raw_coalescent_jet as jet
import source24_regular_laurent as laurent


quotient, P, G = jet.quotient, jet.P, jet.G
dual, incoming, schur = jet.dual, jet.incoming, jet.schur
residue = quotient.residue
ZERO, ONE = dual.ZERO, dual.ONE


def mmul(a, b):
    return schur.matrix_product(a, b)


def msub(a, b):
    return [[(x-y) % P for x, y in zip(u, v)] for u, v in zip(a, b)]


def rowmul(row, matrix):
    return mmul([row], matrix)[0]


def rowscale(c, row):
    return [c*x % P for x in row]


def rank(matrix):
    return residue.modular_rank(matrix, P)['rank'] if matrix else 0


@contextmanager
def precision(q):
    previous = laurent.RELATIVE_PRECISION
    laurent.RELATIVE_PRECISION = q+6
    laurent.inverse_series.cache_clear()
    try:
        yield
    finally:
        laurent.RELATIVE_PRECISION = previous
        laurent.inverse_series.cache_clear()


class Fixture:
    def __init__(self, q):
        self.q, self.r, self.N = q, q-1, q+2
        self.blocks = list(range(2, q+3))
        self.A0 = [[list(row) for row in G] for _ in range(q+3)]
        self.A0[self.N] = [[row[0], 2*row[1], 3*row[2]] for row in G]
        self.AN = self.A0[self.N]
        self.ANinv, _ = schur.invert(self.AN)
        _, self.columns = quotient.raw.labels(q)
        self.index = {(x['t'], x['s'], x['a'], x['b']): i
                      for i, x in enumerate(self.columns)}
        self.common = [self.index[self.N, 2, a, b] for a in range(3) for b in range(3)]
        self.common += [self.index[2, self.N, a, b] for a in range(3) for b in range(3)]
        self.eta = jet.coalesced_matching(self.A0, self.ANinv, self.columns)
        self.edges = []
        for k in range(1, q):
            pairs = [(self.index[self.N, k+2, a, b], self.index[self.N, k+1, a, b])
                     for a in range(3) for b in range(3)]
            pairs += [(self.index[k+2, self.N, a, b], self.index[k+1, self.N, a, b])
                      for a in range(3) for b in range(3)]
            image = [[(row[p]-row[n]) % P for p, n in pairs] for row in self.eta]
            M = image[3*k:3*k+3]
            assert rank(M) == 3
            assert image == [[(-int(u == k-1)+int(u == k))*x % P for x in M[c]]
                             for u in range(q) for c in range(3)]
            pivots, free, kernel = dual.rref_kernel(M)
            assert len(kernel) == 15
            self.edges.append(dict(k=k, pairs=pairs, M=M, pivots=pivots,
                                   free=free, kernel=kernel))
        self.width = 18+15*self.r
        self.minimum_cutoff = float('inf')
        self.word_checks = 0
        self.reconstruction_checks = 0
        self.excess_pole_checks = 0
        self.fixed_direction = {}

    def compress(self, row):
        result = list(row[:18])
        for i, edge in enumerate(self.edges):
            block = row[18+18*i:18+18*(i+1)]
            result.extend(sum(x*y for x, y in zip(block, v)) % P for v in edge['kernel'])
        assert len(result) == self.width
        return result

    def chart(self, channel, state, z):
        if channel == 'new':
            return (-(self.AN[state][1]+self.AN[state][2]*z) % P, 1, z)
        active = [i for i in range(3) if i != state]
        X = [0, 0, 0]
        X[active[0]], X[active[1]] = 1, z
        return tuple(X)

    def root(self, channel, state, row):
        a = residue.dot(row, self.chart(channel, state, 0), P)
        b = (residue.dot(row, self.chart(channel, state, 1), P)-a) % P
        assert b
        return -a*pow(b, -1, P) % P

    def analytic(self, X, channel, state):
        """RQ39 in the conjugated J convention; works over scalars or Laurent."""
        L = [residue.dot(row, X, P) for row in G]
        Li = [pow(x, -1, P) for x in L]
        H = [[X[a]*Li[a]*G[a][b] % P for b in range(3)] for a in range(3)]
        powers = [residue.identity()]
        for _ in range(self.q):
            powers.append(mmul(powers[-1], H))
        LN = [residue.dot(row, X, P) for row in self.AN]
        if channel == 'new':
            tail = [[self.ANinv[a][b]*LN[b] % P for b in range(3)] for a in range(3)]
            JN = None
        else:
            tail = self.ANinv
            JN = [[X[a]*pow(LN[a], -1, P)*self.AN[a][b] % P
                   for b in range(3)] for a in range(3)]

        def outgoing(matrix):
            answer = []
            stripped = mmul(matrix, tail)
            for a in range(3):
                for b in range(3):
                    f = (X[a]*self.AN[a][b] if a == state else 0) if channel == 'new' else (
                        X[a]*self.AN[a][b]*pow(LN[a], -1, P))
                    answer.append(rowscale(f, stripped[b]))
            return answer

        def incoming_rows(matrix, prefix_derivative=None):
            answer = []
            left = [rowmul(self.AN[state], matrix)] if channel == 'new' else mmul(JN, matrix)
            stripped = mmul(left, tail)
            for a in range(3):
                for b in range(3):
                    f = X[a]*G[a][b]*Li[a] % P
                    if prefix_derivative is not None:
                        delta, dl = prefix_derivative
                        f = (X[a]*delta[a][b]*Li[a]-f*dl[a]*Li[a]) % P
                    if channel == 'new':
                        answer.append(rowscale(f*X[state] % P, stripped[0]) if b == state else [0]*3)
                    else:
                        answer.append(rowscale(f, stripped[b]))
            return answer

        result = outgoing(powers[self.q])+incoming_rows(powers[self.r])
        direction_matrices = []
        for k in range(1, self.q):
            delta = [[G[a][b]*(0, 1, 2*k+1)[b] % P for b in range(3)] for a in range(3)]
            dl = [residue.dot(row, X, P) for row in delta]
            D = [[(X[a]*Li[a]*delta[a][b]-dl[a]*Li[a]*H[a][b]) % P
                  for b in range(3)] for a in range(3)]
            direction_matrices.append(D)
            moved = msub(mmul(D, powers[self.r]), mmul(mmul(powers[k], D), powers[self.r-k]))
            omitted = mmul(mmul(powers[k-1], D), powers[self.r-k])
            outgoing_jet = outgoing(moved)
            first = incoming_rows(powers[self.r], (delta, dl))
            second = incoming_rows(omitted)
            result += outgoing_jet+msub(first, second)

        controls = []
        D = direction_matrices[0]  # fixed (1,3), not the varying actual increments
        commutator = msub(mmul(D, H), mmul(H, D))
        for k in range(1, self.q-1):
            exact = mmul(mmul(powers[k], commutator), powers[self.q-2-k])
            left = msub(mmul(D, powers[self.r]), mmul(mmul(powers[k+1], D), powers[self.r-k-1]))
            right = msub(mmul(D, powers[self.r]), mmul(mmul(powers[k], D), powers[self.r-k]))
            difference = msub(left, right)
            for row, target in zip(difference, exact):
                for x, y in zip(row, target):
                    error = laurent.Laurent.cast(x-y)
                    assert not error.terms  # congruence through the tracked cutoff
            controls.append((k, outgoing(exact)))
        return result, controls

    def direct(self, X, channel, state):
        """Independent first-order products in the actual prescribed words."""
        A = {t: [[(G[a][j] % P, G[a][j]*(0, t-1, (t-1)**2)[j] % P)
                  for j in range(3)] for a in range(3)] for t in self.blocks if t != self.N}
        A[self.N] = jet.const(self.AN)
        J, denominators = {}, {}
        for t in self.blocks:
            if channel == 'new' and t == self.N:
                continue
            denominators[t], J[t] = [], []
            for a in range(3):
                den = ZERO
                for j in range(3):
                    den = dual.add(den, dual.scale(X[j], A[t][a][j]))
                denominators[t].append(den)
                J[t].append(jet.scale(dual.scale(X[a], dual.inverse(den)), A[t][a]))
        cache = {(): dual.identity()}

        def product(word):
            key = tuple(word)
            if key not in cache:
                value = dual.identity()
                for t in word:
                    value = dual.mmul(value, J[t])
                cache[key] = value
            return cache[key]

        LN = [residue.dot(row, X, P) for row in self.AN]
        tail = jet.const([[self.ANinv[i][j]*(LN[j] if channel == 'new' else 1) % P
                           for j in range(3)] for i in range(3)])
        result = []
        for label in self.columns:
            t, s, a, b = (label[k] for k in ('t', 's', 'a', 'b'))
            if channel == 'axis':
                f = dual.mul(dual.scale(X[a], A[t][a][b]), dual.inverse(denominators[t][a]))
                B = jet.scale(f, product(quotient.order(self.blocks, t, s))[b])
            elif t == self.N:
                B = jet.scale((X[a]*self.AN[a][b] % P, 0),
                              product(quotient.order(self.blocks, t, s))[b]) if a == state else [ZERO]*3
            elif b == state:
                f = dual.mul(dual.scale(X[a]*X[b], A[t][a][b]), dual.inverse(denominators[t][a]))
                B = jet.scale(f, jet.row_product(A[self.N][b], product(
                    [u for u in self.blocks if u not in (t, self.N)])))
            else:
                B = [ZERO]*3
            result.append(jet.row_product(B, tail))
        return result

    def coefficient(self, value, exponent):
        value = laurent.Laurent.cast(value)
        self.minimum_cutoff = min(self.minimum_cutoff, value.precision)
        return value.coefficient(exponent)

    def verify_ordinary(self, z, channel, state):
        X = self.chart(channel, state, z)
        analytic, _ = self.analytic(X, channel, state)
        direct = self.direct(X, channel, state)
        outputs = [d for d in range(3) if d != state] if channel == 'new' else [state]
        result = {}
        for d in outputs:
            expected = [direct[j][d][0] for j in self.common]
            for edge in self.edges:
                expected += [(direct[p][d][1]-direct[n][d][1]) % P for p, n in edge['pairs']]
            actual = [row[d] for row in analytic]
            assert actual == expected, ('RQ39 actual-word mismatch', self.q, channel, state, z, d)
            self.word_checks += len(actual)
            result[d] = self.compress(actual)
        return result

    def restrictions(self):
        rows, labels, chart_records = [], [], []
        for channel in ('new', 'axis'):
            for state in range(3):
                outputs = [d for d in range(3) if d != state] if channel == 'new' else [state]
                old_roots = [self.root(channel, state, row) for row in G]
                new_roots = [self.root(channel, state, row) for row in self.AN] if channel == 'axis' else []
                assert len(set(old_roots+new_roots)) == len(old_roots+new_roots)
                principal = {d: [] for d in outputs}
                for kind, roots in (('old', old_roots), ('new', new_roots)):
                    for pole_state, root in enumerate(roots):
                        z = laurent.Laurent.cast(root)+laurent.monomial(1)
                        values, controls = self.analytic(self.chart(channel, state, z), channel, state)
                        max_order = self.q if kind == 'old' else 1
                        for d in outputs:
                            excessive = [self.coefficient(row[d], -max_order-1) for row in values]
                            assert not any(excessive), ('Excess pole', channel, state, kind, pole_state)
                            self.excess_pole_checks += len(excessive)
                            coefficients = {}
                            for order in range(max_order, 0, -1):
                                raw = [self.coefficient(row[d], -order) for row in values]
                                if channel == 'axis' and pole_state == state:
                                    assert not any(raw), 'The matching-coordinate row must cancel on its axis.'
                                value = self.compress(raw)
                                coefficients[order] = value
                                rows.append(value)
                                labels.append(dict(channel=channel, state=state, output=d,
                                                   kind=kind, pole_state=pole_state,
                                                   root=root, pole_order=order))
                            principal[d].append((root, coefficients))
                        if kind == 'old':
                            for k, control in controls:
                                bound = max(k, self.q-2-k)+2
                                for d in outputs:
                                    coefficients = {order: [self.coefficient(row[d], -order) for row in control]
                                                    for order in range(self.q+1, 0, -1)}
                                    assert all(not any(row) for order, row in coefficients.items() if order > bound)
                                    key = (k, channel)
                                    record = self.fixed_direction.setdefault(key, dict(
                                        consecutive_edges=[k, k+1], fixed_increment=[1, 3],
                                        predicted_order_bound=bound, observed_maximum_order=0,
                                        checked_output_poles=0))
                                    record['observed_maximum_order'] = max(record['observed_maximum_order'],
                                        max((order for order, row in coefficients.items() if any(row)), default=0))
                                    record['checked_output_poles'] += 1

                def partial(z, d):
                    value = [0]*self.width
                    for root, coefficients in principal[d]:
                        inv = pow((z-root) % P, -1, P)
                        for order, vector in coefficients.items():
                            multiplier = pow(inv, order, P)
                            value = [(x+multiplier*y) % P for x, y in zip(value, vector)]
                    return value

                needed = (3 if channel == 'new' else 1)+3
                ordinary = []
                z = 1
                while len(ordinary) < needed:
                    X = self.chart(channel, state, z)
                    if z not in old_roots+new_roots and (channel == 'axis' or all(X)):
                        ordinary.append(z)
                    z += 1
                fit_count = 3 if channel == 'new' else 1
                evaluated = {z: self.verify_ordinary(z, channel, state) for z in ordinary}
                inverse_vandermonde, _ = schur.invert([[pow(z, degree, P) for degree in range(fit_count)]
                                                       for z in ordinary[:fit_count]])
                polynomial = {}
                for d in outputs:
                    remainders = [[(x-y) % P for x, y in zip(evaluated[z][d], partial(z, d))]
                                  for z in ordinary[:fit_count]]
                    polynomial[d] = mmul(inverse_vandermonde, remainders)
                    for degree, row in enumerate(polynomial[d]):
                        rows.append(row)
                        labels.append(dict(channel=channel, state=state, output=d,
                                           kind='polynomial', degree=degree))
                    for z in ordinary[fit_count:]:
                        restored = partial(z, d)
                        for degree, vector in enumerate(polynomial[d]):
                            restored = [(x+pow(z, degree, P)*y) % P for x, y in zip(restored, vector)]
                        assert restored == evaluated[z][d], ('Rational reconstruction mismatch', channel, state, d, z)
                        self.reconstruction_checks += self.width
                chart_records.append(dict(channel=channel, state=state, old_roots=old_roots,
                                          new_roots=new_roots, fit_parameters=ordinary[:fit_count],
                                          independent_reconstruction_parameters=ordinary[fit_count:]))
        return rows, labels, chart_records


def profile(rows, edge_count):
    B = [row[:18] for row in rows]
    base_rank = rank(B)
    cache = {}

    def visible(edges):
        key = tuple(edges)
        if key not in cache:
            columns = list(range(18))
            for k in key:
                columns += list(range(18+15*k, 18+15*(k+1)))
            cache[key] = rank([[row[j] for j in columns] for row in rows])-base_rank
        return cache[key]

    single = [visible([k]) for k in range(edge_count)]
    forward = [visible(range(k+1)) for k in range(edge_count)]
    reverse = [visible(range(edge_count-1, k-1, -1)) for k in range(edge_count-1, -1, -1)]
    total = forward[-1]
    return dict(observation_rows=len(rows), common_leading_rank=base_rank,
                per_edge_visible_rank=single, forward_cumulative_rank=forward,
                reverse_cumulative_rank=reverse, combined_visible_rank=total,
                coupled_nullity=sum(single)-total,
                full_domain_nullity=15*edge_count-total,
                interpretation='coupled_nullity is the kernel dimension beyond the sum of the individual edge kernels; all images use the same restricted leading columns.')


def calculate(q):
    started = time.monotonic()
    fixture = Fixture(q)
    with precision(q):
        rows, labels, charts = fixture.restrictions()
    B = [row[:18] for row in rows]
    assert rank(B) == 18
    # Each leading original outgoing/incoming column equals its common label.
    A0 = [[row[(0 if label['t'] == fixture.N else 9)+3*label['a']+label['b']]
           for label in fixture.columns] for row in B]
    _, _, joint_kernel = dual.rref_kernel(A0+fixture.eta)
    embedded = []
    for edge in fixture.edges:
        for vector in edge['kernel']:
            v = [0]*len(fixture.columns)
            for coefficient, (p, n) in zip(vector, edge['pairs']):
                v[p], v[n] = (v[p]+coefficient) % P, (v[n]-coefficient) % P
            embedded.append(v)
    assert len(joint_kernel) == len(embedded) == 15*(q-1)
    assert rank(embedded) == len(embedded)
    assert not any(sum(x*y for x, y in zip(row, v)) % P
                   for row in A0+fixture.eta for v in embedded)

    layers = []
    for minimum in range(q, 0, -1):
        item = dict(minimum_old_pole_order=minimum)
        for channel in ('new', 'axis', 'combined'):
            selected = [row for row, label in zip(rows, labels)
                        if label['kind'] == 'old' and label['pole_order'] >= minimum
                        and (channel == 'combined' or label['channel'] == channel)]
            item[channel] = profile(selected, q-1)
            if channel == 'combined':
                item['combined_certificate'] = incoming.matrix_certificate(selected)
        layers.append(item)
    completed = {}
    for channel in ('new', 'axis', 'combined'):
        selected = [row for row, label in zip(rows, labels)
                    if channel == 'combined' or label['channel'] == channel]
        completed[channel] = profile(selected, q-1)
    fixed_new_poles = profile([row for row, label in zip(rows, labels)
                               if label['kind'] != 'polynomial'], q-1)
    full = incoming.matrix_certificate(rows)
    assert completed['combined']['combined_visible_rank'] == 15*(q-1)
    result = dict(q=q, prime=P, G=G, new_factors=[2, 3],
                  old_directions=[[t, t*t] for t in range(1, q+1)],
                  edge_increments=[[1, 2*k+1] for k in range(1, q)],
                  actual_column_labels=fixture.columns,
                  common_leading_column_indices=fixture.common,
                  edge_kernels=fixture.edges,
                  joint_kernel_dimension=len(joint_kernel),
                  embedded_edge_kernel_hash=residue.matrix_hash(embedded),
                  exact_incidence_and_joint_kernel_coverage_verified=True,
                  coefficient_row_labels=labels, coefficient_matrix=rows,
                  coefficient_column_order='18 common leading columns, then 15 kernel-basis columns for each edge in increasing order.',
                  complete_coefficient_certificate=full, charts=charts,
                  old_pole_filtration=layers,
                  old_and_fixed_new_poles=fixed_new_poles,
                  complete_channel_profiles=completed,
                  fixed_direction_consecutive_outgoing_controls=[dict(channel=channel, **record)
                      for (k, channel), record in sorted(fixture.fixed_direction.items())],
                  minimum_certified_Laurent_cutoff=fixture.minimum_cutoff,
                  actual_word_component_checks=fixture.word_checks,
                  rational_reconstruction_component_checks=fixture.reconstruction_checks,
                  excessive_pole_coefficient_checks=fixture.excess_pole_checks,
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q, old_pole_layers=[dict(order=x['minimum_old_pole_order'],
                          per_edge=x['combined']['per_edge_visible_rank'],
                          new=x['new']['combined_visible_rank'], axis=x['axis']['combined_visible_rank'],
                          combined=x['combined']['combined_visible_rank'],
                          coupled_nullity=x['combined']['coupled_nullity']) for x in layers],
                          complete={c: p['combined_visible_rank'] for c, p in completed.items()},
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases, limitation = time.monotonic(), [], None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for q in (3, 4):
            cases.append(calculate(q))
    except (TimeoutError, laurent.PrecisionFailure) as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Finite exact pole-order filtration of actual adjacent-edge joint-kernel first jets.',
                  scope='No uniform injectivity, triangularity theorem, or real/generic upper bound is claimed. Zero coefficients and ranks refer to the recorded finite-field fixtures.',
                  quotient='Each profile is rank[B|D]-rank(B) with the same actual 18 leading columns; combined profiles preserve cross-channel coupling.',
                  remainder_bounds='New-line residues have degree-at-most-two polynomial remainder; axis C has a constant remainder. The fixed new-axis poles are also retained.',
                  elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(), bounded_limitation=limitation,
                  cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
