#!/usr/bin/env python3
"""Bounded exact diagnostic for a Vandermonde/conic common-G subfamily.

Finite ranks do not prove an all-length theorem or a generic deficiency.
The direct matrix uses the first two raw residue components at the explicit
conic intersection; it is compared entrywise with the existing residue code.
"""

import itertools
import json
from pathlib import Path
import resource
import signal
import time

import source24_residue as residue

P = 1000003


def alarm_handler(*_):
    raise TimeoutError("28-second research limit")


def case(alpha, times):
    m = len(times)
    q = {t: [a * times[t - 2] % P for a in alpha] for t in range(2, m + 2)}
    A = [[[1, a, a * a % P] for a in alpha] for _ in range(m + 2)]
    for t in q:
        A[t] = [[1, x, x * x % P] for x in q[t]]
    labels = [(t, a) for t in q for a in range(3)]
    for i, j in itertools.combinations(labels, 2):
        x, y = q[i[0]][i[1]], q[j[0]][j[1]]
        assert x != y
        point = [x * y % P, -(x + y) % P, 1]
        assert all(point)
        for k in labels:
            z = q[k[0]][k[1]]
            assert residue.dot(A[k[0]][k[1]], point, P) == (z - x) * (z - y) % P
            assert (residue.dot(A[k[0]][k[1]], point, P) == 0) == (k in (i, j))

    columns = [(t, s, a, b) for t in q for s in q if t != s
               for a in range(3) for b in range(3)]
    direct, transformed = [], []
    old_matrix, geometry = residue.residue_matrix(m + 2, A, P)
    row = 0
    for u, v in itertools.combinations(q, 2):
        for c, d in itertools.product(range(3), repeat=2):
            x, y = q[u][c], q[v][d]
            point = [x * y % P, -(x + y) % P, 1]
            numerator = {t: [[point[0], z * point[1] % P, z * z % P]
                             for z in q[t]] for t in q}
            kernels = {}
            for t in q:
                if t in (u, v):
                    state = c if t == u else d
                    kernels[t] = [numerator[t][a] if a == state else [0, 0, 0]
                                  for a in range(3)]
                else:
                    kernels[t] = [[value * pow((z - x) * (z - y) % P, -1, P) % P
                                   for value in numerator[t][a]] for a, z in enumerate(q[t])]
            products = {(t, s): residue.word_product(kernels, [s] + [k for k in q if k not in (t, s)], P)
                        for t in q for s in q if t != s}
            rows = [[], []]
            for t, s, a, b in columns:
                scalar = -point[a] * A[t][a][b] * point[b] % P
                if t == u and a != c or t == v and a != d:
                    scalar = 0
                elif t not in (u, v):
                    scalar = scalar * pow((q[t][a] - x) * (q[t][a] - y) % P, -1, P) % P
                vector = [scalar * value % P for value in products[t, s][b]]
                assert sum(vector) % P == 0
                for k in range(2):
                    rows[k].append(vector[k])
            direct.extend(rows)
            # Existing coordinates use cross(L(x),L(y))=(y-x)*point.
            # A cubic raw residue divided by its degree-one basis scales by
            # (y-x)^2, so convert those coordinates back at the chosen point.
            scale_inverse = pow((y - x) ** 2 % P, -1, P)
            for k in range(2):
                transformed.append([(a * numerator[u][c][k] + b * numerator[v][d][k]) * scale_inverse % P
                                    for a, b in zip(old_matrix[row], old_matrix[row + 1])])
            row += 2
    assert direct == transformed
    extreme = [j for j, (_, _, a, b) in enumerate(columns) if a in (0, 2) and b in (0, 2)]
    extreme_certificate = residue.modular_rank([[row[j] for j in extreme] for row in direct], P) if m == 3 else None
    zero_H_certificate = None
    if m == 3:
        index = {label: j for j, label in enumerate(columns)}
        pairs = []
        for t, s in itertools.combinations(q, 2):
            for a, b in itertools.product((0, 2), repeat=2):
                forward = pow(A[t][a][b] * A[s][b][1] % P, -1, P)
                reverse = pow(A[t][a][1] * A[s][b][a] % P, -1, P)
                pairs.append((index[t, s, a, b], forward, index[s, t, b, a], reverse))
        zero_H = [[(row[i] * f - row[j] * g) % P for i, f, j, g in pairs] for row in direct]
        zero_H_certificate = residue.modular_rank(zero_H, P)
    return dict(alpha=list(alpha), times=list(times), m=m, dimension=len(columns),
                prime=P, geometry=geometry, all_pair_conic_geometry_checked=True,
                independent_residue_coordinates_match=True,
                matrix_sha256=residue.matrix_hash(direct),
                rank_certificate=residue.modular_rank(direct, P),
                extreme_shared_and_divergent_columns=extreme if m == 3 else None,
                extreme_column_rank_certificate=extreme_certificate,
                antisymmetric_zero_H_rank_certificate=zero_H_certificate)


def main():
    signal.signal(signal.SIGALRM, alarm_handler)
    signal.alarm(28)
    started = time.monotonic()
    cases = [case((1, 2, 3), (2, 5, 11, 23, 47)[:m]) for m in range(2, 6)]
    cases += [case((1, 2, 4), (8, 64, 512)), case((2, 5, 9), (2, 7, 19))]
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert rss < 95 * 1024 * 1024  # macOS reports bytes.
    result = dict(scope="Finite-field diagnostics only; no all-length or deficiency theorem.",
                  elapsed_seconds=time.monotonic() - started, max_rss_bytes=rss, cases=cases)
    output = Path(__file__).with_name("source24-conic-results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(output), "ranks": [(c["m"], c["rank_certificate"]["rank"], c["dimension"]) for c in cases],
                      "elapsed_seconds": result["elapsed_seconds"], "max_rss_bytes": rss}))


if __name__ == "__main__":
    main()
