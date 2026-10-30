#!/usr/bin/env python3
"""One exact three-block quintic interpolation certificate, not source rank.

Reproduce: nice -n 19 python3 exploration/source24_triple_quintic.py \
  --output exploration/source24-triple-quintic-results.json
"""
import argparse
import json
from pathlib import Path
import signal
import time

import source24_path_component as path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started > 28:
            raise TimeoutError('28-second bound')
        if path.incoming.maximum_rss_bytes() > 95 * 1024 ** 2:
            raise TimeoutError('95 MiB bound')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        times = path.sparse.factors(3, 'economic')
        tables = path.sparse.coefficient_tables(path.G, times)
        A = [[list(row) for row in path.G] for _ in range(2)] + tables
        geometry = path.differences.check_geometry(3, A)
        points, labels = path.basepoints(tables)
        exponents = path.monomials(5)
        evaluation = [path.monomial_values(exponents, X) for X in points]
        certificate = path.incoming.matrix_certificate(evaluation)
        assert certificate['rank_certificate']['rank'] == 18
        for X, label in zip(points, labels):
            table = tables[label['t'] - 2]
            assert sum(a * b for a, b in zip(table[label['a']], X)) % path.P == 0
            if label['kind'] == 'matching_coordinate':
                assert X[label['a']] == 0
            else:
                assert sum(a * b for a, b in zip(table[label['b']], X)) % path.P == 0
        result = dict(
            status='Exact finite three-block quintic interpolation certificate.',
            scope='Ambient interpolation only; no actual source-spanning or residual-determinant claim.',
            m=3, degree=5, prime=path.P, G=path.G, time_factors=times,
            coefficient_tables=tables, geometry=geometry,
            point_labels=labels, points=points, monomial_exponents=exponents,
            evaluation_matrix=evaluation, evaluation=certificate,
            all_defining_point_incidents_checked=True,
            elapsed_seconds=time.monotonic()-started,
            maximum_rss_bytes=path.incoming.maximum_rss_bytes(),
            limits=dict(seconds=28, maximum_rss_bytes=95*1024**2))
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(dict(rank=18, minor=certificate['rank_certificate']['nonzero_minor'],
                             elapsed_seconds=result['elapsed_seconds'],
                             maximum_rss_bytes=result['maximum_rss_bytes'])))
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    main()
