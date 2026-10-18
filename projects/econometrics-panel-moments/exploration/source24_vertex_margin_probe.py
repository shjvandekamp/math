#!/usr/bin/env python3
"""Check the six vertex observations from the saved leading-prefix identities.

Reads the certified q=4,5 rational preimages; does not refit them. Compares
the observed actual prefix matrix with the independently computed known
vertex part plus nine actual diagonal-state endpoint margins per column.
This is an external finite-field check, not an all-q nonvanishing proof.
"""

import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal
import time

import source24_residue as residue
import source24_schur as schur


ROOT = Path(__file__).resolve().parent


def det3(a, p):
    return sum(a[0][j] * (a[1][(j + 1) % 3] * a[2][(j + 2) % 3]
                         - a[1][(j + 2) % 3] * a[2][(j + 1) % 3])
               for j in range(3)) % p


def check_case(case):
    q, p = case['q'], case['prime']
    assert p == schur.P
    A, G = case['coefficient_tables'], case['G']
    cols = case['defect_column_labels']
    obs = [(k, j) for k in range(3) for j in range(3) if k != j]
    M = {tuple(label): row for label, row in
         zip(case['prefix_defect']['row_labels'], case['prefix_defect']['matrix'])}
    inv = lambda x: pow(x, -1, p)
    kappa = lambda t, k, j: A[t][k][j] * inv(A[t][k][k]) % p
    OM = [[sum(M[t, k, j][c] * inv(A[t][k][k])
               - M[t, j, j][c] * inv(A[t][j][j]) for t in range(q)) % p
           for c in range(6)] for k, j in obs]
    # Margins are indexed by (actual terminal time, diagonal state, column).
    S = {ell: [[0] * 6 for _ in range(3)] for ell in (q - 3, q - 2, q - 1)}
    for label, coefficients in zip(case['source_column_labels'],
                                   case['source_coefficient_matrix']):
        if label[0] != 'F':
            continue
        _, t, s, d, e = label
        if d == e:
            ell = max(x for x in range(q) if x not in (t, s))
            for c in range(6):
                S[ell][d][c] = (S[ell][d][c] + coefficients[c]) % p
    sigma = [[sum(S[ell][k][c] for ell in S) % p for c in range(6)] for k in range(3)]
    TS = [[(sum(kappa(ell, k, j) * S[ell][k][c] for ell in S)
            - sigma[j][c]) % p for c in range(6)] for k, j in obs]
    h = {}
    source_count = len(case['source_column_labels'])
    for system in case['systems']:
        for local, c in enumerate(system['defect_column_indices']):
            h[c] = {tuple(label): row[local] for label, row in
                    zip(system['h_labels'], system['solution'][source_count:])}

    def h_vertex(c, k):
        return (h[c].get(('constant',), 0) +
                sum(h[c].get(('pole', t, k), 0) * inv(A[t][k][k])
                    for t in range(q))) % p

    def h_derivative(c, i, k):
        return sum(h[c].get(('pole', t, i), 0) * inv(A[t][i][k])
                   - h[c].get(('pole', t, k), 0) * A[t][k][i]
                   * inv(A[t][k][k]) ** 2 for t in range(q)) % p

    inverse_A, _ = schur.invert(A[-1])
    zeta = []
    for k in range(3):
        w = [x * inv(A[-2][k][k]) % p for x in A[-2][k]]
        wA = residue.matmul([w], inverse_A, p)[0]
        zeta.append([(int(j == k) - wA[j] * A[-1][j][k]) % p for j in range(3)])
    B = [[0] * 6 for _ in obs]
    for c, (a, b) in enumerate(cols):
        i = next(k for k in range(3) if k not in (a, b))
        assert h_vertex(c, a) == h_vertex(c, b) == 0
        B[obs.index((a, b))][c] = kappa(q - 1, a, b) * zeta[a][b] % p
        B[obs.index((b, a))][c] = zeta[b][a]
        for k in (a, b):
            B[obs.index((k, i))][c] = (A[-1][i][i] * h_vertex(c, i)
                                      - A[-1][i][k] * h_derivative(c, i, k)) % p
    assert OM == [[(x + y) % p for x, y in zip(br, tr)] for br, tr in zip(B, TS)]

    # Six boundary margins with the three totals held fixed.
    correction = [[0] * 6 for _ in obs]
    for row, (k, j) in enumerate(obs):
        for slot, ell in enumerate((q - 3, q - 2)):
            correction[row][2 * k + slot] = (kappa(ell, k, j)
                                            - kappa(q - 1, k, j)) % p
    last_factors = [[1, *pair] for pair in case['time_factors'][-3:]]
    delta = det3(last_factors, p)
    predicted = -delta ** 3
    for k in range(3):
        for j in range(3):
            if k != j:
                predicted = predicted * G[k][j] % p
        predicted = predicted * inv(G[k][k]) ** 2 % p
    for _, u, v in last_factors:
        predicted = predicted * inv(u * v % p) % p
    correction_certificate = residue.modular_rank(correction, p)
    assert correction_certificate['determinant_mod_prime'] == predicted % p != 0
    pair_blocks = []
    for a in range(3):
        for b in range(a + 1, 3):
            rr = [obs.index((a, b)), obs.index((b, a))]
            cc = [cols.index([a, b]), cols.index([b, a])]
            block = [[B[r][c] for c in cc] for r in rr]
            determinant = (block[0][0] * block[1][1] - block[0][1] * block[1][0]) % p
            predicted_pair = (zeta[a][b] * zeta[b][a] *
                              (G[a][b] * G[b][a] * inv(G[a][a] * G[b][b] % p) - 1)) % p
            assert determinant == predicted_pair != 0
            pair_blocks.append(dict(states=[a, b], determinant_mod_prime=determinant))
    return dict(q=q, prime=p, observation_rows=obs, columns=cols,
                observed_prefix=OM, observed_prefix_certificate=residue.modular_rank(OM, p),
                known_part=B, known_part_certificate=residue.modular_rank(B, p),
                endpoint_correction=TS, endpoint_margins=S, diagonal_totals=sigma,
                identity_checks=36, actual_h_vertex_zero_checks=12,
                fixed_total_correction=correction,
                fixed_total_correction_certificate=correction_certificate,
                predicted_correction_determinant=predicted % p,
                known_pair_blocks=pair_blocks,
                source_coefficient_hash=case['source_coefficients_sha256'],
                pole_prefix_hash=case['prefix_defect']['certificate']['sha256'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('28-second cap')))
    signal.alarm(28)
    start = time.monotonic()
    source = ROOT / 'source24-leading-prefix-probe-results.json'
    data = json.loads(source.read_text())
    cases = [check_case(case) for case in data['cases']]
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert rss <= 95 * 1024 * 1024, '95 MiB RSS cap exceeded (macOS byte units).'
    result = dict(schema_version=1, status='external exact finite-field check',
                  source_file=source.name, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  scope='Saved q=4,5 actual rational preimages; no uniform rank theorem.',
                  cases=cases, elapsed_seconds=time.monotonic() - start,
                  maximum_rss_bytes=rss)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    for case in cases:
        print('q', case['q'], 'observed rank', case['observed_prefix_certificate']['rank'],
              'det', case['observed_prefix_certificate']['determinant_mod_prime'],
              'known-part rank', case['known_part_certificate']['rank'])


if __name__ == '__main__':
    main()
