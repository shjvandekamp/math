#!/usr/bin/env python3
"""Finite actual-source reconstruction of conic seed compression SC1--SC16.

Only the established nonsingular n=5 fixture is used.  O contains actual F
double residues, with the negative raw-tail sign; U contains divided simple
residues of positive raw Qhat.  Source coefficients construct E,V,lambda,Y
independently of O inverse.  An explicit 85-column source kernel and a
95-column complement determine Xi from the left nullspace of O K0.

The compression is checked as UC (Xi OC)^-1 Xi O = U on all 180 source
coordinates.  No inverse of O is computed.  The three mixed-coordinate
sectors are reconstructed before compression and compared with the saved
45-by-45 actual leading matrix, with all permutations and right scalings.
This finite normalization check is not an all-n determinant theorem and
does not implement the even-parity correction.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import signal
import time

import source24_conic_regular_leading as leading


P, incoming = leading.P, leading.incoming
residue, schur, dual = leading.residue, leading.schur, leading.dual
HERE = Path(__file__).resolve().parent


def select(matrix, ids):
    return [[row[j] for j in ids] for row in matrix]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def embedding(size, ids):
    return [[int(i == j) for j in ids] for i in range(size)]


def add_columns(left, right):
    return [a+b for a,b in zip(left,right)]


def fraction_data(value):
    return dict(numerator=value.numerator, denominator=value.denominator,
                sign=(1 if value > 0 else -1 if value < 0 else 0),
                modulo_prime=value.numerator*pow(value.denominator % P,-1,P) % P)


def seed_coefficients(fixture):
    d = len(fixture.old_columns)
    labels = [(t,a) for t in fixture.old for a in range(3)]
    index = {label:i for i,label in enumerate(fixture.old_columns)}
    E = [[0]*len(labels) for _ in range(d)]
    V = [[0]*len(labels) for _ in range(d)]
    for j,(t,a) in enumerate(labels):
        E[index[t,fixture.first[t],a,0]][j] = 1
        for b in range(3):
            V[index[t,fixture.first[t],a,b]][j] = 1
    chi, scalar_details = {}, []
    for t,a in labels:
        y = fixture.nodes[fixture.first[t]][0]
        X = (0,-y,1)
        beta,gamma = fixture.nodes[t][1:]
        determinant = y*(beta-gamma)*pow((beta-y)*(gamma-y) % P,-1,P) % P
        line_value = residue.dot(fixture.A[t][a],X,P)
        h = X[a]*pow(line_value,-1,P) % P
        chi[t,a] = h*pow(determinant,-1,P) % P
        scalar_details.append(dict(t=t,a=a,matching_point=X,h=h,binary_determinant=determinant,
                                   line_denominator=line_value,chi=chi[t,a]))
    lam = [[chi[t,a] if (s,j) == (fixture.first[t],0) else 0 for t,a in labels]
           for s,j in labels]
    Y = schur.matrix_difference(E,schur.matrix_product(V,lam))
    return labels,E,V,lam,Y,chi,scalar_details


def source_word_controls(fixture, labels, E, V, lam, Y):
    controls, count = [], 0
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        K = {t: residue.ordinary_kernel(fixture.A,t,X,P) for t in fixture.old}
        completed = {(t,s): residue.word_product(K,fixture.word(t,s),P)
                     for t in fixture.old for s in fixture.old if t != s}
        raw, source = [], []
        for t,s,a,b in fixture.old_columns:
            scalar = X[a]*K[t][a][b] % P
            raw.append([scalar*entry % P for entry in completed[t,s][b]])
            source.append([scalar*(int(b == c)-completed[t,s][b][c]) % P for c in range(3)])
        rawE, rawV = schur.matrix_product(transpose(raw),E), schur.matrix_product(transpose(raw),V)
        sourceE, sourceV = schur.matrix_product(transpose(source),E), schur.matrix_product(transpose(source),V)
        for i,(t,a) in enumerate(labels):
            omitted = residue.word_product(K,[u for u in fixture.old if u != t],P)
            moved = residue.word_product(K,residue.ordered_word(fixture.old,t),P)
            h = X[a]*pow(residue.dot(fixture.A[t][a],X,P),-1,P) % P
            for c in range(3):
                assert rawE[c][i] == X[0]*h*omitted[0][c] % P
                assert sourceE[c][i] == X[0]*h*(int(c == 0)-omitted[0][c]) % P
                assert rawV[c][i] == X[a]*moved[a][c] % P
                assert sourceV[c][i] == X[a]*(K[t][a][c]-moved[a][c]) % P
                count += 4
        sourceY = schur.matrix_product(transpose(source),Y)
        assert sourceY == schur.matrix_difference(sourceE,schur.matrix_product(sourceV,lam))
        controls.append(dict(point=X,actual_seed_source_values=sourceY))
    return dict(SC2_actual_word_component_checks=count,points=controls,
                actual_source_seed_identity_verified=True)


def compression_basis(fixture, U, Ulabels, O):
    n, d = fixture.n, len(fixture.old_columns)
    C0ids = [i for i,(_,_,a,b) in enumerate(fixture.old_columns) if a == 0 or b == 0]
    binids = [i for i,(_,_,a,b) in enumerate(fixture.old_columns) if a in (1,2) and b in (1,2)]
    row0 = [i for i,(_,a,_) in enumerate(Ulabels) if a == 0]
    rowbin = [i for i,(_,a,_) in enumerate(Ulabels) if a != 0]
    assert len(C0ids) == 5*n*(n-1) and len(binids) == 4*n*(n-1)
    assert len(row0) == 3*n and len(rowbin) == 6*n
    UC0 = select(U,C0ids)
    assert not any(x for i in rowbin for x in UC0[i])
    UC0certificate = incoming.matrix_certificate(UC0)
    assert UC0certificate['rank_certificate']['rank'] == 3*n
    source_index = {label:i for i,label in enumerate(fixture.old_columns)}
    Urow_index = {label:i for i,label in enumerate(Ulabels)}
    R0 = [[0]*(3*n) for _ in range(d)]
    anchors, selected_ids = [], []
    for block_index,t in enumerate(fixture.old):
        k,l = sorted((s for s in fixture.old if s != t),reverse=True)[:2]
        candidates = [source_index[t,s,0,b] for s in (k,l) for b in (1,2)]
        rows = [Urow_index[t,0,c] for c in range(3)]
        candidate_matrix = [[U[i][j] for j in candidates] for i in rows]
        certificate = incoming.matrix_certificate(candidate_matrix)
        assert certificate['rank_certificate']['rank'] == 3
        selected = [candidates[j] for j in certificate['rank_certificate']['nonzero_minor']['columns']]
        assert len(selected) == 3
        block = [[U[i][j] for j in selected] for i in rows]
        block_inverse, inverse_certificate = schur.invert(block)
        for a,j in enumerate(selected):
            for c in range(3):
                R0[j][3*block_index+c] = block_inverse[a][c]
        selected_ids += selected
        anchors.append(dict(old_block=t,old_row_indices=rows,candidate_source_indices=candidates,
                            candidate_source_labels=[fixture.old_columns[i] for i in candidates],
                            candidate_matrix=candidate_matrix,candidate_certificate=certificate,
                            selected_source_indices=selected,selected_inverse_certificate=inverse_certificate))
    U0 = [U[i] for i in row0]
    UR0 = schur.matrix_product(U,R0)
    iota0 = [[int(i == row0[j]) for j in range(3*n)] for i in range(len(U))]
    assert UR0 == iota0
    assert not any(x for i in binids for x in R0[i])
    free = [i for i in C0ids if i not in selected_ids]
    K0 = schur.matrix_difference(embedding(d,free),schur.matrix_product(R0,select(U0,free)))
    assert len(free) == n*(5*n-8) == 85
    assert [K0[i] for i in free] == [[int(i == j) for j in range(len(free))] for i in range(len(free))]
    assert not any(x for row in schur.matrix_product(U,K0) for x in row)
    corrected_bin = schur.matrix_difference(embedding(d,binids),schur.matrix_product(R0,select(U0,binids)))
    C = add_columns(R0,corrected_bin)
    assert len(C[0]) == n*(4*n-1) == 95
    source_basis_certificate = incoming.matrix_certificate(add_columns(K0,C))
    assert source_basis_certificate['rank_certificate']['rank'] == d
    UC = schur.matrix_product(U,C)
    expected = [iota0[i]+([0]*len(binids) if i in row0 else [U[i][j] for j in binids]) for i in range(len(U))]
    assert UC == expected
    OK0 = schur.matrix_product(O,K0)
    pivots, free_residue, Xi = dual.rref_kernel(transpose(OK0))
    assert len(pivots) == 85 and len(Xi) == 95
    assert not any(x for row in schur.matrix_product(Xi,OK0) for x in row)
    Xicertificate = incoming.matrix_certificate(Xi)
    assert Xicertificate['rank_certificate']['rank'] == 95
    OC = schur.matrix_product(O,C)
    Ohat = schur.matrix_product(Xi,OC)
    Ohatcertificate = incoming.matrix_certificate(Ohat)
    Ohatinv, Ohatinverse_certificate = schur.invert(Ohat)
    assert Ohatcertificate['rank_certificate']['rank'] == 95
    assert Ohatinverse_certificate['determinant_mod_prime'] == Ohatcertificate['rank_certificate']['determinant_mod_prime']
    compressed = schur.matrix_product(schur.matrix_product(UC,Ohatinv),Xi)
    assert schur.matrix_product(compressed,O) == U
    result = dict(C0_source_indices=C0ids,binary_source_indices=binids,
                  state_zero_U_rows=row0,binary_U_rows=rowbin,
                  U_C0_state_zero_matrix=[UC0[i] for i in row0],U_C0_certificate=UC0certificate,
                  C0_has_only_state_zero_observations=True,
                  right_inverse_anchor_choices=anchors,R0=R0,UR0_equals_state_zero_inclusion=True,
                  K0_free_source_indices=free,K0=K0,K0_dimension=len(free),
                  K0_free_coordinate_identity_verified=True,UK0_zero_verified=True,
                  complement_C=C,complement_dimension=len(C[0]),
                  full_source_basis_certificate=source_basis_certificate,UC=UC,
                  UC_block_diagonal_identity_verified=True,
                  O_K0=OK0,O_K0_certificate=incoming.matrix_certificate(OK0),
                  Xi=Xi,Xi_certificate=Xicertificate,
                  Xi_nullspace_pivots=pivots,Xi_free_residue_coordinates=free_residue,
                  Xi_O_K0_zero_verified=True,
                  compressed_O=Ohat,compressed_O_certificate=Ohatcertificate,
                  compressed_O_inverse_certificate=Ohatinverse_certificate,
                  compressed_operator=compressed,
                  exact_compression_equation='UC (Xi OC)^-1 Xi O = U',
                  exact_compression_equation_verified=True,
                  full_O_inverse_computed=False)
    return result,compressed,Xi


def eta_check(fixture, labels, Ulabels, U, Y, XiOY):
    y = fixture.nodes[fixture.old[0]][0]
    middle = []
    product = Fraction(1)
    for t in fixture.old[1:-1]:
        beta,gamma = fixture.nodes[t][1:]
        value = Fraction(y*(beta-gamma),(beta-y)*(gamma-y))
        product *= value
        middle.append(dict(old_block=t,value=fraction_data(value)))
    taus = []
    for t in fixture.old[-2:]:
        beta,gamma = fixture.nodes[t][1:]
        taus.append(Fraction(beta+gamma-y,beta*gamma))
    gap = taus[0]-taus[1]
    assert gap > 0
    eta, entries = [0]*len(labels), []
    last = fixture.old[-1]
    for a in (1,2):
        r = fixture.nodes[last][a]
        h = Fraction(-y if a == 1 else 1,r*(r-y))
        value = h*y*product*gap
        modular = fraction_data(value)['modulo_prime']
        eta[labels.index((last,a))] = modular
        entries.append(dict(label=(last,a),h=fraction_data(h),eta=fraction_data(value)))
    row = Ulabels.index((fixture.old[0],0,0))
    UY = schur.matrix_product(U,Y)
    expected = [eta[:] if i == row else [0]*len(labels) for i in range(len(U))]
    assert UY == expected
    Ycertificate, UYcertificate, XiOYcertificate = [incoming.matrix_certificate(matrix) for matrix in (Y,UY,XiOY)]
    assert Ycertificate['rank_certificate']['rank'] == 3*fixture.n
    assert UYcertificate['rank_certificate']['rank'] == XiOYcertificate['rank_certificate']['rank'] == 1
    return dict(y_star=y,middle_binary_determinants=middle,product_binary_determinants=fraction_data(product),
                penultimate_tau=fraction_data(taus[0]),terminal_tau=fraction_data(taus[1]),
                tau_difference=fraction_data(gap),supported_entries=entries,
                SC16_sign='h * y_star * product(d_j) * (tau_penultimate - tau_terminal), with a plus sign.',
                eta=eta,nonzero_U_row_index=row,nonzero_U_row_label=Ulabels[row],
                UY=UY,seed_rank_certificate=Ycertificate,UY_certificate=UYcertificate,
                Xi_OY=XiOY,Xi_OY_certificate=XiOYcertificate,
                exact_sparse_terminal_defect_verified=True)


def calculate(prior):
    fixture = leading.Fixture(5)
    labels,E,V,lam,Y,chi,scalar_details = seed_coefficients(fixture)
    O,E0,Bbar0 = fixture.pair_matrices()
    Lambda0,prior_chi = fixture.lambda0()
    assert chi == prior_chi
    label_index = {label:i for i,label in enumerate(labels)}
    independently_expanded_lambda = [[lam[label_index[s,j]][label_index[t,a]]*pow(fixture.nodes[t][a],c,P) % P
                                     if c == incoming_state else 0 for t,a,incoming_state in fixture.incoming_columns]
                                    for c,s,j in fixture.outgoing_columns]
    assert independently_expanded_lambda == Lambda0
    Z0 = schur.matrix_difference(E0,schur.matrix_product(Bbar0,Lambda0))
    U,Ulabels,marginal_checks,physical_checks = fixture.divided_U()
    for name,matrix in (('O',O),('U',U),('E0',E0),('Bbar0',Bbar0),('Lambda0',Lambda0),('Z0',Z0)):
        assert residue.matrix_hash(matrix) == prior['matrix_hashes'][name]
    Ocertificate = incoming.matrix_certificate(O)
    assert Ocertificate['rank_certificate']['rank'] == 180
    assert Ocertificate['rank_certificate']['determinant_mod_prime'] == 969253
    assert not any(Y[i][j] for i,(_,_,a,b) in enumerate(fixture.old_columns) if a != 0 and b != 0 for j in range(len(labels)))
    OY = schur.matrix_product(O,Y)
    reconstructed_Z = [[0]*len(fixture.incoming_columns) for _ in range(len(O))]
    row_scales = []
    for k,pair in enumerate(fixture.pairs):
        X = pair['point']
        scales = [x*pow(X[0],-1,P) % P for x in X]
        row_scales.append(scales)
        for r in (2*k,2*k+1):
            for j,(t,a,c) in enumerate(fixture.incoming_columns):
                reconstructed_Z[r][j] = scales[c]*OY[r][label_index[t,a]]*pow(fixture.nodes[t][a],c,P) % P
    assert reconstructed_Z == Z0
    word_controls = source_word_controls(fixture,labels,E,V,lam,Y)
    compression,operator,Xi = compression_basis(fixture,U,Ulabels,O)
    XiOY = schur.matrix_product(Xi,OY)
    eta = eta_check(fixture,labels,Ulabels,U,Y,XiOY)

    # Grouped columns are (new state c, seed i).  Mixed operators act BEFORE Xi.
    mixed, DZ0 = [], []
    for k,pair in enumerate(fixture.pairs):
        X = pair['point']
        seed2 = [(-a-b) % P for a,b in zip(OY[2*k],OY[2*k+1])]
        z2 = [(-a-b) % P for a,b in zip(Z0[2*k],Z0[2*k+1])]
        for d in range(2):
            mixed.append([X[c]*fixture.ell2[d]*value % P for c in range(3) for value in seed2])
            DZ0.append([X[0]*fixture.ell2[d]*value % P for value in z2])
    assert residue.matrix_hash(DZ0) == prior['matrix_hashes']['DZ0']
    Htilde = schur.matrix_product(operator,mixed)
    sector_labels = [(t,a,c) for c in range(3) for t,a in labels]
    scales = [pow(fixture.nodes[t][a],c,P) for t,a,c in sector_labels]
    Hgroup = [[value*factor % P for value,factor in zip(row,scales)] for row in Htilde]
    sector_index = {label:i for i,label in enumerate(sector_labels)}
    original_order = [sector_index[label] for label in fixture.incoming_columns]
    Hlead = select(Hgroup,original_order)
    assert Hlead == schur.matrix_product(operator,DZ0)
    assert Hlead == prior['Hlead']
    Hcertificate = incoming.matrix_certificate(Hlead)
    tilde_certificate = incoming.matrix_certificate(Htilde)
    group_certificate = incoming.matrix_certificate(Hgroup)
    detR = 1
    for t,a in labels:
        detR = detR*fixture.nodes[t][a] % P
    right_scaling = pow(detR,3,P)
    permutation_sign = schur.permutation_sign(original_order)
    assert group_certificate['rank_certificate']['determinant_mod_prime'] == right_scaling*tilde_certificate['rank_certificate']['determinant_mod_prime'] % P
    assert Hcertificate['rank_certificate']['determinant_mod_prime'] == permutation_sign*group_certificate['rank_certificate']['determinant_mod_prime'] % P == 214966
    result = dict(n=5,prime=P,alpha=leading.ALPHA,times=leading.TIMES,common_G=leading.G,
                  nodes=fixture.nodes,ell2=fixture.ell2,old_source_column_labels=fixture.old_columns,
                  old_pair_labels=fixture.pairs,old_pair_row_order='For each pair: actual residue component 0, then 1.',
                  U_row_labels=Ulabels,seed_column_labels=labels,
                  O_sign='Actual F double residues, equal to the negative raw-tail residues.',
                  U_sign='Divided simple residues of positive raw Qhat.',
                  E=E,V=V,lambda_scalar=lam,Y=Y,lambda_scalar_details=scalar_details,
                  expanded_sector_lambda_matches=True,source_word_controls=word_controls,
                  OY=OY,SC4_pair_sector_multipliers=row_scales,
                  SC4_all_actual_sector_entries_verified=True,
                  saved_original_matrix_hashes_verified=True,
                  matrix_hashes={name:residue.matrix_hash(matrix) for name,matrix in
                                 (('O',O),('U',U),('E0',E0),('Bbar0',Bbar0),('Lambda0',Lambda0),
                                  ('Z0',Z0),('DZ0',DZ0),('OY',OY),('mixed_unscaled_sectors',mixed))},
                  old_O_certificate=Ocertificate,
                  U_marginal_checks=marginal_checks,U_actual_K_regularization_component_checks=physical_checks,
                  compression=compression,sparse_seed_terminal_defect=eta,
                  unscaled_sector_column_labels=sector_labels,unscaled_mixed_sector_matrix=mixed,
                  compressed_Htilde=Htilde,Htilde_certificate=tilde_certificate,
                  sector_right_scales=scales,sector_grouped_H_certificate=group_certificate,
                  original_incoming_column_order=fixture.incoming_columns,
                  original_order_from_grouped_permutation=original_order,
                  original_order_permutation_sign=permutation_sign,
                  det_R=detR,det_R_cubed=right_scaling,
                  compressed_original_Hlead=Hlead,Hlead_certificate=Hcertificate,
                  compressed_Hlead_matches_saved_actual_matrix=True,
                  saved_result_reference='source24-conic-regular-leading-results.json',
                  scope='A single n=5 conic fixture. No n=3 inverse, no even correction, and no uniform nonvanishing claim.')
    print(json.dumps(dict(n=5,C0_image_rank=15,kernel_dimension=85,complement_dimension=95,
                          compressed_O_determinant=compression['compressed_O_certificate']['rank_certificate']['determinant_mod_prime'],
                          seed_rank=15,UY_rank=1,Xi_OY_rank=1,
                          eta_entries=eta['supported_entries'],
                          Hlead_determinant=214966,Htilde_determinant=tilde_certificate['rank_certificate']['determinant_mod_prime'],
                          original_order_permutation_sign=permutation_sign,all_compression_checks_passed=True)),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    prior = json.loads((HERE/'source24-conic-regular-leading-results.json').read_text())['case']
    started,case,limitation = time.monotonic(),None,None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        case = calculate(prior)
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Finite actual-source seed and kernel compression reconstruction.',
                  case=case,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
