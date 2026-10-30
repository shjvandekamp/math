#!/usr/bin/env python3
"""Exact finite tests of two proposed terminal-pole margin duals.

Uses the actual ordered outgoing/incoming boundary functions. Their cleared
restrictions are binary forms of degree 3m-1, so 3m distinct ordinary chart
points determine their entire coefficient row space. A target row increasing
the rank proves that the proposed margin cannot be recovered from this map.
This is a finite-length certificate, not an all-length source-rank theorem.
"""

import argparse
import json
from pathlib import Path
import resource
import signal
import sys
import time

import source24_residue as residue
import source24_schur as schur


P, G = schur.P, schur.G


def check(q, c):
    m = q - 1
    factors = [(pow(8, t, P), pow(8, 2 * t, P)) for t in range(1, q + 1)]
    tables = [[[G[a][b] * (1, u, v)[b] % P for b in range(3)]
               for a in range(3)] for u, v in factors]
    A = tables[-1]
    inverse_A, _ = schur.invert(A)
    j, ell = [k for k in range(3) if k != c]
    labels = [('outgoing', s, e) for s in range(m) for e in range(3)]
    labels += [('incoming', t, d) for t in range(m) for d in range(3)]
    points, rows = [], []
    for z in range(1, 1000):
        X = [-(A[c][1] + A[c][2] * z) * pow(A[c][0], -1, P) % P, 1, z]
        old_forms = [[residue.dot(tables[t][a], X, P) for a in range(3)] for t in range(m)]
        last_forms = [residue.dot(A[a], X, P) for a in range(3)]
        if not all(X) or not all(x for row in old_forms for x in row) or not last_forms[ell]:
            continue
        assert last_forms[c] == 0
        kernels = [residue.ordinary_kernel(tables, t, X, P) for t in range(m)]
        right = [[pow(X[a], -1, P) * inverse_A[a][b] % P for b in range(3)] for a in range(3)]
        v = [A[c][a] * X[a] % P for a in range(3)]
        values = []
        for s in range(m):
            word = residue.word_product(kernels, [s] + [t for t in range(m) if t != s], P)
            output = residue.matmul(word, right, P)
            for e in range(3):
                values.append(A[c][e] * (inverse_A[e][j] - X[e] * output[e][j]) % P)
        for t in range(m):
            word = residue.word_product(kernels, [s for s in range(m) if s != t], P)
            output = residue.matmul(residue.matmul([v], word, P), right, P)[0]
            for d in range(3):
                values.append(-tables[t][d][c] * X[d] * pow(old_forms[t][d], -1, P) * output[j] % P)
        denominator = 1
        for row in old_forms:
            for value in row:
                denominator = denominator * value % P
        factor = denominator * pow(last_forms[ell], -1, P) % P
        rows.append([factor * value % P for value in values])
        points.append(X)
        if len(rows) == 3 * m:
            break
    assert len(rows) == 3 * m
    certificate = residue.modular_rank(rows, P)
    targets = {
        'last_pair_diagonal_margin': [int(state == c and t == m - 1) for _, t, state in labels],
        'total_boundary_diagonal_margin': [int(state == c) for _, _, state in labels],
    }
    tests = {name: dict(target_row=target, augmented_certificate=residue.modular_rank(rows + [target], P))
             for name, target in targets.items()}
    return dict(q=q, state=c, chosen_output=j, third_state=ell, prime=P, G=G,
                time_factors=factors, coefficient_tables=tables, chart_points=points,
                polynomial_degree=3 * m - 1, column_labels=labels, matrix=rows,
                matrix_sha256=residue.matrix_hash(rows), certificate=certificate, targets=tests)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('28-second cap')))
    signal.alarm(28)
    start = time.monotonic()
    cases = [check(q, c) for q in (4, 5, 6) for c in range(3)]
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if sys.platform != 'darwin':
        rss *= 1024
    assert rss <= 95 * 1024 * 1024
    args.output.write_text(json.dumps(dict(schema_version=1,
        status='external exact finite-field certificate',
        scope='terminal-pole boundary duals at q=4,5,6 only; no all-length rank inference',
        cases=cases, elapsed_seconds=time.monotonic() - start, maximum_rss_bytes=rss), indent=2) + '\n')
    for case in cases:
        print('q', case['q'], 'state', case['state'], 'rank', case['certificate']['rank'],
              'with margins', [test['augmented_certificate']['rank'] for test in case['targets'].values()])


if __name__ == '__main__':
    main()
