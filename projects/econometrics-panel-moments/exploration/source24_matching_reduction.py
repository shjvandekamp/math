#!/usr/bin/env python3
"""Exact finite tests of the specified MP25 matching-first quotient minor.

Uses the 18q+9 explicit quotient coordinates, not oversampled evaluation
rows: 9q new/old residues, six row-sum coordinates, 6q+3 axis coordinates,
and 3q matching values. All column corrections in MP21 are retained.
"""
import argparse
import json
from pathlib import Path
import signal
import time
import source24_raw_quotient as quotient

P, raw, schur, residue = quotient.P, quotient.raw, quotient.schur, quotient.residue


def residue_B(A, X, poles, columns):
    """Actual conjugated words after multiplying by each specified line."""
    blocks = list(range(2, len(A)))
    J = {}
    for t in blocks:
        if t in poles:
            c = poles[t]
            assert residue.dot(A[t][c], X, P) == 0
            J[t] = [[X[c] * A[t][c][j] % P for j in range(3)] if a == c else [0]*3
                    for a in range(3)]
        else:
            J[t] = [[X[a] * A[t][a][j] * quotient.inverse(residue.dot(A[t][a], X, P)) % P
                     for j in range(3)] for a in range(3)]
    product = quotient.cached_product(J)
    result = []
    for col in columns:
        t, s, a, b = (col[k] for k in ('t', 's', 'a', 'b'))
        if t in poles:
            scalar = X[a] * A[t][a][b] if a == poles[t] else 0
        else:
            scalar = X[a] * A[t][a][b] * quotient.inverse(residue.dot(A[t][a], X, P))
        result.append(raw.row_scale(scalar, product(quotient.order(blocks, t, s))[b]))
    return result


def actual_double_check(A, X, poles, ANinv, columns, expected):
    N, blocks = len(A)-1, list(range(2, len(A)))
    K = {}
    for t in blocks:
        if t in poles:
            c = poles[t]
            K[t] = [[A[t][c][j] * X[j] % P for j in range(3)] if a == c else [0]*3
                    for a in range(3)]
        else:
            K[t] = residue.ordinary_kernel(A, t, X, P)
    product = quotient.cached_product(K)
    LN = [residue.dot(row, X, P) for row in A[N]]
    tail = [[quotient.inverse(X[i]) * ANinv[i][j] * LN[j] % P for j in range(3)]
            for i in range(3)]
    for col, value in zip(columns, expected):
        t, s, a, b = (col[k] for k in ('t', 's', 'a', 'b'))
        H = raw.row_scale(X[a] * K[t][a][b], product(quotient.order(blocks, t, s))[b])
        assert quotient.row_product(H, tail) == value
    return 3 * len(columns)


def select(matrix, indices):
    return [[row[j] for j in indices] for row in matrix]


def calculate(q):
    N = q+2
    times = quotient.sparse.factors(q+1, 'economic')
    A = [[list(row) for row in quotient.G] for _ in range(2)] + quotient.sparse.coefficient_tables(quotient.G, times)
    geometry = raw.differences.check_geometry(q+1, A)
    ANinv, _ = schur.invert(A[N])
    _, columns = raw.labels(q)
    S = [[int(col['t'] == N and col['a'] == c) *
          (int(col['b'] == k) - int(col['b'] == 0)) % P for col in columns]
         for c in range(3) for k in (1, 2)]
    U, Ulabels, eta, etalabels = [], [], [], []
    checks = 0
    for t in range(2, N):
        for a in range(3):
            for c in range(3):
                X = residue.cross(A[t][a], A[N][c], P)
                assert all(X)
                LN = [residue.dot(row, X, P) for row in A[N]]
                tail = [[ANinv[i][j] * LN[j] % P for j in range(3)] for i in range(3)]
                values = [quotient.row_product(B, tail) for B in residue_B(A, X, {t:a, N:c}, columns)]
                assert all(v[c] == 0 and sum(v) % P == 0 for v in values)
                if q == 2:
                    checks += actual_double_check(A, X, {t:a, N:c}, ANinv, columns, values)
                d = next(j for j in range(3) if j != c)
                U.append([v[d] for v in values])
                Ulabels.append(dict(kind='new_old', old_block=t, old_state=a, new_state=c, output=d, point=X))
    for d in range(3):
        for t in range(2, N):
            for c in range(3):
                if c == d:
                    continue
                X = residue.cross(A[t][c], [int(i == d) for i in range(3)], P)
                values = [quotient.row_product(B, ANinv) for B in residue_B(A, X, {t:c}, columns)]
                U.append([v[d] for v in values])
                Ulabels.append(dict(kind='axis_residue', axis=d, old_block=t, old_state=c, point=X))
        X = quotient.axis_points(A, d, 1)[0][0]
        U.append([v[d] for v in quotient.boundary_C(A, ANinv, X, columns)])
        Ulabels.append(dict(kind='axis_value', axis=d, point=X))
    for t in range(2, N):
        for a in range(3):
            Xjet = quotient.regular.edge_point(A, (t,a), a)
            X = tuple(v[0] for v in Xjet)
            eta.append(quotient.matching_values(A, ANinv, (t,a), X, columns))
            etalabels.append(dict(old_block=t, old_state=a, point=X))
    Zids = [i for i,c in enumerate(columns) if c['s'] == N and c['b'] == (c['a']+1)%3]
    Cids = [i for i,c in enumerate(columns) if c['t'] == N and c['s'] == N-1 and c['b'] in (1,2)]
    Bids = [i for i in range(len(columns)) if i not in Zids+Cids]
    assert select(S,Cids) == [[int(i==j) for j in range(6)] for i in range(6)]
    assert not any(x for row in select(S,Zids) for x in row)
    J = select(eta,Zids)
    Jinv, Jcert = schur.invert(J)
    observations = eta+S+U
    B0 = schur.matrix_difference(select(observations,Bids), schur.matrix_product(select(observations,Cids),select(S,Bids)))
    correction = schur.matrix_product(Jinv,B0[:3*q])
    Bsharp = schur.matrix_difference(B0,schur.matrix_product(select(observations,Zids),correction))
    assert not any(x for row in Bsharp[:3*q+6] for x in row)
    R = Bsharp[3*q+6:]
    assert len(R) == 15*q+3 and len(R[0]) == 15*q-6
    I = [i for i,row in enumerate(Ulabels) if row['kind'] != 'new_old' or row['old_block'] != N-1]
    candidate = [R[i] for i in I]
    fullcert = quotient.incoming.matrix_certificate(observations)
    Rcert = quotient.incoming.matrix_certificate(R)
    candidatecert = quotient.incoming.matrix_certificate(candidate)
    assert fullcert['rank_certificate']['rank'] == 3*q+6+Rcert['rank_certificate']['rank']
    bordered = [J[i]+B0[i] for i in range(3*q)] + [select(U,Zids)[i]+B0[3*q+6+i] for i in I]
    bordercert = quotient.incoming.matrix_certificate(bordered)
    # For a full candidate, use an independent inverse/determinant computation
    # to check the literal MP25 bordered identity, with its original row order.
    determinant_check = None
    if candidatecert['rank_certificate']['rank'] == len(candidate):
        _, candidate_det = schur.invert(candidate)
        _, border_det = schur.invert(bordered)
        assert candidate_det['determinant_mod_prime'] * Jcert['determinant_mod_prime'] % P == border_det['determinant_mod_prime']
        determinant_check = dict(candidate=candidate_det['determinant_mod_prime'], bordered=border_det['determinant_mod_prime'], matching=Jcert['determinant_mod_prime'], identity_verified=True)
    result = dict(q=q, prime=P, G=quotient.G, time_factors=times, geometry=geometry,
                  boundary_columns=columns, matching_rows=etalabels, remaining_rows=Ulabels,
                  matching_columns=Zids, row_sum_columns=Cids, remaining_columns=Bids,
                  candidate_rows=I, full_quotient=fullcert, matching_inverse=Jcert,
                  reduced=Rcert, candidate=candidatecert, bordered=bordercert,
                  determinant_identity=determinant_check, actual_K_double_residue_component_checks=checks)
    print(json.dumps(dict(q=q,full_rank=fullcert['rank_certificate']['rank'],reduced_rank=Rcert['rank_certificate']['rank'],candidate_rank=candidatecert['rank_certificate']['rank'],candidate_size=len(candidate),determinants=determinant_check)),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.monotonic(); cases=[]; limitation=None
    def guard(_s,_f):
        if time.monotonic()-start >= 28 or quotient.incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')
    signal.signal(signal.SIGALRM,guard); signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for q in (2,3,4,5,6):
            cases.append(calculate(q))
    except TimeoutError as error:
        limitation=str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result=dict(status='Exact finite matching-first reduction and specified-minor diagnostic; no uniform full-rank claim.',
                elapsed_seconds=time.monotonic()-start, maximum_rss_bytes=quotient.incoming.maximum_rss_bytes(), bounded_limitation=limitation,cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':
    main()
