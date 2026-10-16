#!/usr/bin/env python3
"""One fixed-fixture check of terminal edge pivots; not a uniform rank claim.

For t=2,3 and sector a=0, compute Z=E^-1 e((J_tc-r_tc U_tc)K_t^-1),
U_tc=H_tc-H_1c, e(F)_j=F_j(Q_j). These are undivided edge values.
Cancel output coordinates first: Y K_t^-1=(Y/diag(X)) A_t^-1 diag(L_t).
The saved recurrence supplies the exact pole ratios; no source matrix is rebuilt.
"""
import argparse
import hashlib
import json
from pathlib import Path
import signal
import time

import source24_residue as residue
import source24_schur as schur
from source24_boundary_recurrence import P, inv, rowmul, scale, sub, cert, invert, maximum_rss_bytes


def calculate(case, t):
    tables, chart = case['fixture']['actual_coefficient_tables_mod_prime'][:t + 1], case['chart']
    normal = tables[0][0]
    record = next(row for row in case['recursive_cases'] if row['old_blocks'] == t)
    ratios = [row['incoming_head_coefficient'] for row in record['last_pivots']]
    Ainv, Acertificate = invert(tables[t])

    def point(z):
        return [(a + z * b) % P for a, b in zip(chart['origin'], chart['direction'])]

    def evaluate(X, divided):
        L = {s: [residue.dot(row, X, P) for row in tables[s]] for s in range(1, t + 1)}
        assert all(value for rows in L.values() for value in rows)
        matrices = {s: [[tables[s][i][j] * (X[i] if divided else X[j]) * inv(L[s][i]) % P
                         for j in range(3)] for i in range(3)] for s in L}
        older = residue.word_product(matrices, list(range(1, t)), P)
        terminal = residue.word_product(matrices, [t] + list(range(1, t)), P)
        first = residue.word_product(matrices, list(range(1, t + 1)), P)
        v = normal if divided else [normal[j] * X[j] % P for j in range(3)]
        rows = []
        for c in range(3):
            J = scale(-tables[t][c][0] * X[c] * inv(L[t][c]), rowmul(v, older))
            U = scale(1 if divided else X[c], sub(first[c], terminal[c]))
            rows.append(sub(J, scale(ratios[c], U)))
        return rows, L

    E, e, edge_records = [], [], []
    for j, z in enumerate(chart['edge_parameters']):
        X = point(z)
        assert X[j] == 0 and all(X[i] for i in range(3) if i != j)
        assert residue.dot(normal, X, P) == 0
        rows, L = evaluate(X, True)
        E.append([L[t][j] * Ainv[b][j] % P for b in range(3)])
        e.append([L[t][j] * rowmul(row, Ainv)[j] % P for row in rows])
        edge_records.append(dict(output=j, z=z, point=X, row_forms=L, divided_Y_columns=rows))
    Einverse, Ecertificate = invert(E)
    Z = schur.matrix_product(Einverse, e)
    assert schur.matrix_product(E, Z) == e
    controls = []
    for z in (1, 2):
        X = point(z)
        assert all(X)
        divided, L = evaluate(X, True)
        direct, _ = evaluate(X, False)
        assert direct == [[row[j] * X[j] % P for j in range(3)] for row in divided]
        V = [[inv(X[i]) * Ainv[i][j] * L[t][j] % P for j in range(3)] for i in range(3)]
        canceled = [[rowmul(row, Ainv)[j] * L[t][j] % P for j in range(3)] for row in divided]
        assert canceled == [rowmul(row, V) for row in direct]
        controls.append(dict(z=z, point=X, transported_columns=canceled))
    return dict(old_blocks=t, sector=0, pole_ratios=ratios, terminal_table_certificate=Acertificate,
                edge_records=edge_records, E_matrix=E, E_certificate=Ecertificate,
                e_matrix=e, Z_matrix=Z, Z_certificate=cert(Z), reconstruction_verified=True,
                ordinary_actual_kernel_controls=controls, column_labels=[['J-r*(H-H1)', t, c] for c in range(3)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('source24-boundary-recurrence-results.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28 or maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('28-second /95MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    raw = args.input.read_bytes()
    saved = json.loads(raw)
    assert saved['prime'] == P and saved['status'].startswith('PASS')
    result = dict(prime=P, input_file=args.input.name, input_sha256=hashlib.sha256(raw).hexdigest(),
                  fixture=saved['case']['fixture'], chart=saved['case']['chart'],
                  cases=[calculate(saved['case'], t) for t in (2, 3)],
                  scope='Sector0, one saved fixture, t=2,3 only. Sampled singularity would not prove an identically singular family.',
                  resource_limits=dict(seconds=28, maximum_rss_bytes=95 * 1024 ** 2))
    result.update(elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=maximum_rss_bytes())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps([dict(t=row['old_blocks'], certificate=row['Z_certificate']['rank_certificate'])
                      for row in result['cases']]), flush=True)
    print(json.dumps({key: result[key] for key in ('elapsed_seconds', 'maximum_rss_bytes')}), flush=True)


if __name__ == '__main__':
    main()
