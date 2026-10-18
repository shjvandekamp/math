#!/usr/bin/env python3
"""Finite exact outgoing-pole reduction of the specified matching-first minor.

The observations are exactly those of source24_matching_reduction: stripped
new/old residues, analytically divided matching values, and the same axis
residues and ordinary axis values.  Pi omits the nine new/old coordinates
incident to the final old block.  No alternative observation is substituted.

On actual raw boundary columns, write D_t^{cb}=O_t^{cb}-O_q^{cb},
V_c=sum_b O_q^{cb}, W_c=(V_c,I_t^{ac}:t,a), and C_ck=O_q^{ck}.
After the six row-sum pivots, eliminate M=Pi(D) to form
T=E(W)-E(D) M^-1 Pi(W).  The candidate claim is that the three diagonal
blocks of T vanish.  We test that claim and the literal determinant identity
against the original square observation matrix and saved matching-first
determinants, retaining the exact permutation signs.

Only q=2,...,6 at the existing economic fixtures are checked.  These finite
certificates are not an all-q theorem or an asymptotic calculation.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_matching_reduction as matching


quotient = matching.quotient
P, raw, schur, residue = matching.P, matching.raw, matching.schur, matching.residue
incoming, sparse, G = quotient.incoming, quotient.sparse, quotient.G
HERE = Path(__file__).resolve().parent


def combine(matrix, terms):
    """Columns are explicit constant combinations of original raw columns."""
    return [[sum(coefficient*row[j] for j, coefficient in column) % P
             for column in terms] for row in matrix]


def coefficient_matrix(size, terms):
    result = [[0]*len(terms) for _ in range(size)]
    for j, column in enumerate(terms):
        for i, coefficient in column:
            result[i][j] = (result[i][j]+coefficient) % P
    return result


def row_key(label):
    return json.dumps(label, sort_keys=True)


def observations(q, A, ANinv, columns):
    """Rebuild the original coordinates using the existing actual-word helpers."""
    N = q+2
    S = [[int(col['t'] == N and col['a'] == c) *
          (int(col['b'] == k)-int(col['b'] == 0)) % P for col in columns]
         for c in range(3) for k in (1, 2)]
    Slabels = [dict(kind='row_sum', new_state=c, output=k)
               for c in range(3) for k in (1, 2)]
    U, Ulabels, eta, etalabels = [], [], [], []
    checks = dict(actual_K_double_residue_components=0,
                  actual_K_matching_first_jets=0, actual_K_ordinary_components=0)
    for t in range(2, N):
        for a in range(3):
            for c in range(3):
                X = residue.cross(A[t][a], A[N][c], P)
                assert all(X)
                LN = [residue.dot(row, X, P) for row in A[N]]
                tail = [[ANinv[i][j]*LN[j] % P for j in range(3)] for i in range(3)]
                values = [quotient.row_product(B, tail)
                          for B in matching.residue_B(A, X, {t:a, N:c}, columns)]
                assert all(v[c] == 0 and sum(v) % P == 0 for v in values)
                if q == 2:
                    checks['actual_K_double_residue_components'] += matching.actual_double_check(
                        A, X, {t:a, N:c}, ANinv, columns, values)
                d = next(j for j in range(3) if j != c)
                U.append([v[d] for v in values])
                Ulabels.append(dict(kind='new_old', old_block=t, old_state=a,
                                    new_state=c, output=d, point=X))
    for d in range(3):
        for t in range(2, N):
            for c in range(3):
                if c == d:
                    continue
                X = residue.cross(A[t][c], [int(i == d) for i in range(3)], P)
                values = [quotient.row_product(B, ANinv)
                          for B in matching.residue_B(A, X, {t:c}, columns)]
                U.append([v[d] for v in values])
                Ulabels.append(dict(kind='axis_residue', axis=d, old_block=t,
                                    old_state=c, point=X))
        X = quotient.axis_points(A, d, 1)[0][0]
        U.append([v[d] for v in quotient.boundary_C(A, ANinv, X, columns)])
        Ulabels.append(dict(kind='axis_value', axis=d, point=X))
    for t in range(2, N):
        for a in range(3):
            Xjet = quotient.regular.edge_point(A, (t,a), a)
            X = tuple(v[0] for v in Xjet)
            values = quotient.matching_values(A, ANinv, (t,a), X, columns)
            eta.append(values)
            etalabels.append(dict(kind='matching', old_block=t, old_state=a, point=X))
            if q == 2:
                checks['actual_K_matching_first_jets'] += quotient.matching_jet_check(
                    A, ANinv, (t,a), Xjet, columns, values)
    if q == 2:
        X = (1, 2, 3)
        frame, _ = raw.labels(q)
        actual, _ = raw.evaluate(q, A, X, frame, columns)
        expected = quotient.boundary_C(A, ANinv, X, columns)
        for H, C in zip(actual[len(frame):], expected):
            divided = [H[d]*quotient.inverse(X[d]) % P for d in range(3)]
            assert quotient.row_product(divided, ANinv) == C
            checks['actual_K_ordinary_components'] += 3
    return S, Slabels, U, Ulabels, eta, etalabels, checks


def calculate(q, saved):
    started, N = time.monotonic(), q+2
    old, last = list(range(2, N)), N-1
    times = sparse.factors(q+1, 'economic')
    A = [[list(row) for row in G] for _ in range(2)]+sparse.coefficient_tables(G, times)
    geometry = raw.differences.check_geometry(q+1, A)
    ANinv, ANcertificate = schur.invert(A[N])
    _, columns = raw.labels(q)
    S, Slabels, U, Ulabels, eta, etalabels, checks = observations(q, A, ANinv, columns)
    assert saved['q'] == q and saved['prime'] == P
    assert saved['G'] == [list(row) for row in G]
    assert saved['time_factors'] == [list(pair) for pair in times]
    assert saved['boundary_columns'] == columns
    assert json.loads(json.dumps(Ulabels)) == saved['remaining_rows']
    assert residue.matrix_hash(eta+S+U) == saved['full_quotient']['sha256']

    index = {(c['t'], c['s'], c['a'], c['b']): i for i, c in enumerate(columns)}
    Cterms = [[(index[N,last,c,k], 1)] for c in range(3) for k in (1, 2)]
    Clabels = [dict(kind='C', new_state=c, output=k, old_block=last)
               for c in range(3) for k in (1, 2)]
    Dterms = [[(index[N,t,c,b], 1), (index[N,last,c,b], -1)]
              for c in range(3) for t in old[:-1] for b in range(3)]
    Dlabels = [dict(kind='D', new_state=c, first_old=t, reference_old=last, output=b)
               for c in range(3) for t in old[:-1] for b in range(3)]
    Wterms, Wlabels = [], []
    for c in range(3):
        Wterms.append([(index[N,last,c,b], 1) for b in range(3)])
        Wlabels.append(dict(kind='V', new_state=c, first_old=last))
        for t in old:
            for a in range(3):
                Wterms.append([(index[t,N,a,c], 1)])
                Wlabels.append(dict(kind='I', old_block=t, old_state=a, new_state=c))
    assert combine(S, Cterms) == [[int(i == j) for j in range(6)] for i in range(6)]
    assert not any(x for row in combine(S, Dterms+Wterms) for x in row)

    Piids = sorted((i for i, label in enumerate(Ulabels)
                    if label['kind'] == 'new_old' and label['old_block'] != last),
                   key=lambda i: (Ulabels[i]['new_state'], Ulabels[i]['old_block'], Ulabels[i]['old_state']))
    Pi, Pilabels = [U[i] for i in Piids], [Ulabels[i] for i in Piids]
    E, Elabels = [], []
    for c in range(3):
        for row, label in zip(eta, etalabels):
            if label['old_state'] == c:
                E.append(row)
                Elabels.append(label)
        for row, label in zip(U, Ulabels):
            if label.get('axis') == c:
                E.append(row)
                Elabels.append(label)
    sizeD, sizeW, blockD, blockW = 9*(q-1), 9*q+3, 3*(q-1), 3*q+1
    assert len(Pi) == len(Dterms) == sizeD
    assert len(E) == len(Wterms) == sizeW
    M, PiW = combine(Pi, Dterms), combine(Pi, Wterms)
    ED, EW = combine(E, Dterms), combine(E, Wterms)
    Mcertificate = incoming.matrix_certificate(M)
    off_blocks = [(i,j,M[i][j]) for i in range(sizeD) for j in range(sizeD)
                  if i//blockD != j//blockD and M[i][j]]
    result = dict(q=q, prime=P, G=G, time_fixture='economic', time_factors=times,
                  geometry=geometry, new_table_inverse=ANcertificate,
                  original_boundary_columns=columns,
                  C_column_labels=Clabels, D_column_labels=Dlabels, W_column_labels=Wlabels,
                  C_source_terms=Cterms, D_source_terms=Dterms, W_source_terms=Wterms,
                  Pi_row_labels=Pilabels, E_row_labels=Elabels,
                  M=M, M_certificate=Mcertificate,
                  M_state_block_size=blockD, M_off_diagonal_nonzero_entries=off_blocks,
                  M_is_state_block_diagonal=not off_blocks,
                  Pi_W=PiW, E_D=ED, E_W=EW,
                  row_sum_identity_and_zero_columns_verified=True,
                  saved_observation_matrix_hash_matches=True,
                  actual_K_controls=checks)
    inverted = schur.invert(M)
    if inverted is None:
        result.update(status='M is singular at this finite fixture; no generic refutation is asserted.',
                      elapsed_seconds=time.monotonic()-started)
        print(json.dumps(dict(q=q, M_rank=Mcertificate['rank_certificate']['rank'], M_size=sizeD,
                              status=result['status'])), flush=True)
        return result
    Minv, Minvcertificate = inverted
    assert Minvcertificate['determinant_mod_prime'] == Mcertificate['rank_certificate']['determinant_mod_prime']
    correction = schur.matrix_product(Minv, PiW)
    T = schur.matrix_difference(EW, schur.matrix_product(ED, correction))
    Tcertificate = incoming.matrix_certificate(T)
    diagonal_blocks = []
    for c in range(3):
        indices = range(c*blockW, (c+1)*blockW)
        nonzero = [(i-c*blockW,j-c*blockW,T[i][j]) for i in indices for j in indices if T[i][j]]
        diagonal_blocks.append(dict(state=c, size=blockW, zero=not nonzero, nonzero_entries=nonzero))
    off_diagonal_blocks, blocks = [], {}
    for c in range(3):
        for d in range(3):
            if c == d:
                continue
            block = [row[d*blockW:(d+1)*blockW] for row in T[c*blockW:(c+1)*blockW]]
            blocks[c,d] = block
            off_diagonal_blocks.append(dict(row_state=c, column_state=d,
                                            certificate=incoming.matrix_certificate(block)))
    cyclic_inverses = {pair: schur.invert(blocks[pair]) for pair in ((0,1), (1,2), (2,0))}
    cyclic_reduction = dict(cyclic_pairs=[[0,1], [1,2], [2,0]],
                            singular_pairs=[list(pair) for pair, value in cyclic_inverses.items() if value is None])
    if not cyclic_reduction['singular_pairs'] and all(block['zero'] for block in diagonal_blocks):
        factors = [cyclic_inverses[1,2][0], blocks[1,0], cyclic_inverses[2,0][0],
                   blocks[2,1], cyclic_inverses[0,1][0], blocks[0,2]]
        product = factors[0]
        for factor in factors[1:]:
            product = schur.matrix_product(product, factor)
        final = [[(value+int(i == j)) % P for j, value in enumerate(row)]
                 for i, row in enumerate(product)]
        final_certificate = incoming.matrix_certificate(final)
        cycle_determinant = 1
        for inverse_data in cyclic_inverses.values():
            cycle_determinant = cycle_determinant*inverse_data[1]['determinant_mod_prime'] % P
        assert (cycle_determinant*final_certificate['rank_certificate']['determinant_mod_prime'] % P
                == Tcertificate['rank_certificate']['determinant_mod_prime'])
        cyclic_reduction.update(formula='det T = det T01 det T12 det T20 det(I + T12^-1 T10 T20^-1 T21 T01^-1 T02)',
                                cyclic_inverse_certificates=[dict(row_state=c, column_state=d, certificate=data[1])
                                                             for (c,d), data in cyclic_inverses.items()],
                                final_matrix=final, final_certificate=final_certificate,
                                cyclic_determinant_product=cycle_determinant, identity_verified=True)

    original = S+Pi+E
    original_labels = Slabels+Pilabels+Elabels
    L = coefficient_matrix(18*q, Cterms+Dterms+Wterms)
    Lcertificate = incoming.matrix_certificate(L)
    detL = Lcertificate['rank_certificate']['determinant_mod_prime']
    assert detL in (1, P-1)
    transformed = combine(original, Cterms+Dterms+Wterms)
    assert transformed == schur.matrix_product(original, L)
    assert [row[6:6+sizeD] for row in transformed[6:6+sizeD]] == M
    assert [row[6+sizeD:] for row in transformed[6+sizeD:]] == EW
    original_certificate = incoming.matrix_certificate(original)
    original_inverse = schur.invert(original)
    original_determinant = original_certificate['rank_certificate']['determinant_mod_prime']
    if original_inverse is not None:
        assert original_inverse[1]['determinant_mod_prime'] == original_determinant
    detM = Mcertificate['rank_certificate']['determinant_mod_prime']
    detT = Tcertificate['rank_certificate']['determinant_mod_prime']
    assert original_determinant*detL % P == detM*detT % P

    # Matching-first uses rows [eta;S;candidate U] and columns [Z;C;B].
    # Both permutations are explicit; all eliminated-column additions have determinant 1.
    I = [i for i, label in enumerate(Ulabels)
         if label['kind'] != 'new_old' or label['old_block'] != last]
    assert saved['candidate_rows'] == I
    matching_labels = etalabels+Slabels+[Ulabels[i] for i in I]
    original_row_index = {row_key(label): i for i, label in enumerate(original_labels)}
    row_permutation = [original_row_index[row_key(label)] for label in matching_labels]
    Zids = [i for i,c in enumerate(columns) if c['s'] == N and c['b'] == (c['a']+1)%3]
    Cids = [terms[0][0] for terms in Cterms]
    Bids = [i for i in range(18*q) if i not in Zids+Cids]
    assert (Zids, Cids, Bids) == (saved['matching_columns'], saved['row_sum_columns'], saved['remaining_columns'])
    column_permutation = Zids+Cids+Bids
    row_sign, column_sign = schur.permutation_sign(row_permutation), schur.permutation_sign(column_permutation)
    J = matching.select(eta, Zids)
    Jcertificate = incoming.matrix_certificate(J)
    detJ = Jcertificate['rank_certificate']['determinant_mod_prime']
    saved_detR = saved['determinant_identity']['candidate']
    assert detJ == saved['determinant_identity']['matching']
    assert row_sign*column_sign*original_determinant % P == detJ*saved_detR % P
    sign = row_sign*column_sign*(1 if detL == 1 else -1)
    assert saved_detR == sign*detM*quotient.inverse(detJ)*detT % P
    result.update(status='Finite outgoing-pole Schur reduction completed.',
                  M_inverse_certificate=Minvcertificate, M_inverse_Pi_W=correction,
                  T=T, T_certificate=Tcertificate, T_state_block_size=blockW,
                  T_diagonal_blocks=diagonal_blocks,
                  T_off_diagonal_blocks=off_diagonal_blocks, cyclic_block_reduction=cyclic_reduction,
                  all_three_T_diagonal_blocks_zero=all(block['zero'] for block in diagonal_blocks),
                  original_square_row_labels=original_labels,
                  original_square_matrix=original, original_square_certificate=original_certificate,
                  original_square_independent_inverse_certificate=(original_inverse[1] if original_inverse else None),
                  original_to_C_D_W_matrix=L, column_change_certificate=Lcertificate,
                  matching_J_certificate=Jcertificate,
                  matching_row_permutation=row_permutation, matching_column_permutation=column_permutation,
                  determinant_identity=dict(original=original_determinant, column_change=detL,
                                            M=detM, T=detT, matching_J=detJ, saved_matching_R=saved_detR,
                                            row_permutation_sign=row_sign, column_permutation_sign=column_sign,
                                            exact_sign=sign,
                                            original_times_column_change_equals_M_times_T=True,
                                            matching_R_equals_sign_times_M_times_T_over_J=True),
                  saved_matching_result_reference='source24-matching-reduction-results.json',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q, M_rank=Mcertificate['rank_certificate']['rank'], M_size=sizeD,
                          T_rank=Tcertificate['rank_certificate']['rank'], T_size=sizeW,
                          zero_diagonal_blocks=result['all_three_T_diagonal_blocks_zero'],
                          determinant_identity=result['determinant_identity'], elapsed_seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-matching-reduction-results.json').read_text())
    started, cases, limitation = time.monotonic(), [], None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        for q in (2, 3, 4, 5, 6):
            prior = next(case for case in saved['cases'] if case['q'] == q)
            cases.append(calculate(q, prior))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Exact finite outgoing-pole reduction of the specified matching-first quotient minor.',
                  scope='Only q=2,...,6 at the existing economic fixtures. No all-q nonvanishing or near-diagonal asymptotic statement is asserted.',
                  elapsed_seconds=time.monotonic()-started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation, cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('elapsed_seconds', 'maximum_rss_bytes', 'bounded_limitation')}), flush=True)


if __name__ == '__main__':
    main()
