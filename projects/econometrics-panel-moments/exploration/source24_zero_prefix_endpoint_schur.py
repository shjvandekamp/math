#!/usr/bin/env python3
"""Finite endpoint Schur test with the prescribed conditional scalar basis.

Use q=4,5, old times (7^(t-1),3^(t-1)), positive new times (7^q,3^q),
and the one auxiliary parameter w=5.  The scalar basis consists of the
saved independent old subset, the accepted 6q+3 new columns, and 3q
appended old scalar-kernel vectors selected by their exact D_q f trace.
No arbitrary full-new scalar column pivots replace this construction.

Project the specified 3q body columns and three endpoint columns through
that same scalar inverse.  Observe B_w on 3n auxiliary-line points and
check the remaining 3-by-3 Schur matrix after the same body correction.
All ranks and source coefficients are finite-field data at fixed fixtures;
no uniform endpoint theorem is inferred.
"""

import argparse
import json
from pathlib import Path
import random
import signal
import time

import source24_zero_prefix_projected_body as projected
import source24_zero_prefix_joint_boundary as joint


source,boundary,split = projected.source,projected.boundary,projected.split
P,G = source.P,source.G
incoming,residue,schur,dual = source.incoming,source.residue,source.schur,source.dual
HERE = Path(__file__).resolve().parent


def determinant_product(denominators):
    value = 1
    for line in denominators:
        for x in line:
            value = value*x % P
    return value


def line_points(tables,w,count,seed):
    def permitted(x):
        return x != 0 and all(residue.dot(row,(-w,x,1),P)
                              for table in tables.values() for row in table)
    xs,rejected,x = [],[],0
    while len(xs) < count:
        x += 1
        if permitted(x):
            xs.append(x)
        else:
            rejected.append(x)
    rng = random.Random(seed)
    while len(xs) < count+6:
        x = rng.randrange(1,P)
        if x not in xs and permitted(x):
            xs.append(x)
    return xs,rejected


def source_selectors(columns,n):
    q = n-1
    axis,matching12,_ = projected.seed_indices(columns,n)
    C = {(c['label']['t'],c['label']['s'],c['label']['a'],c['label']['b']):i
         for i,c in enumerate(columns) if c['label']['kind'] == 'C'}
    body_ids = axis+matching12[:-1]+[C[2,n,1,1]]
    endpoint_ids = [C[n,q,1,1],C[n,q,0,1],C[n,q-2,1,1]]
    assert len(body_ids) == 3*q and len(set(body_ids+endpoint_ids)) == 3*q+3
    return body_ids,endpoint_ids


def calculate(reference):
    started,q,n,w = time.monotonic(),reference['q'],reference['n'],5
    assert q in (4,5) and n == q+1
    boundary_times = reference['time_factors']
    assert boundary_times == [[7**(t-1),3**(t-1)] for t in range(1,n)]+[[0,3**q]]
    old_times = boundary_times[:-1]
    times = old_times+[[7**q,3**q]]
    old_tables,tables = source.tables_at(old_times),source.tables_at(times)
    old_columns,_ = source.larger_columns(q)
    columns,_ = source.larger_columns(n)
    original_index = {json.dumps(c,sort_keys=True):i for i,c in enumerate(columns)}
    inherited_ids = [original_index[json.dumps(c,sort_keys=True)] for c in old_columns]
    old_dimension,scalar_target = 9*q*(q-1)//2+3*q,9*n*(n-1)//2+3*n
    geometry = split.field_geometry(boundary_times)
    # All n positive blocks also satisfy the old scheme conditions.  The
    # appended zero-u block below is only a geometry checker with tilde=10;
    # it does not enter any source word or rank calculation.
    positive_geometry = split.field_geometry(times+[[0,w]])
    requested = reference['observation_points']
    points = [X for X in requested if X[2] % P and
              all(residue.dot(row,X,P) for table in tables.values() for row in table)]
    rejected = len(requested)-len(points)
    if rejected:
        replacements,_ = source.points_off_poles([tables],len(requested)+rejected)
        for X in replacements:
            if list(X) not in [list(Y) for Y in points]:
                points.append(X)
            if len(points) == len(requested):
                break
    assert len(points) == len(requested)
    old_rows,scalar_rows = [],[]
    for X in points:
        evaluate_old,_,_,_ = source.evaluator(old_tables,X)
        evaluate,_,_,_ = source.evaluator(tables,X)
        old_rows.append([R[2]*source.inverse(X[2]) % P for R in evaluate_old(old_columns)])
        scalar_rows.append([R[2]*source.inverse(X[2]) % P for R in evaluate(columns)])
    old_certificate = incoming.matrix_certificate(old_rows)
    old_pivots,old_free,old_kernel = dual.rref_kernel(old_rows)
    assert len(old_pivots) == old_certificate['rank_certificate']['rank']
    result = dict(q=q,n=n,prime=P,G=G,old_time_factors=old_times,time_factors=times,w=w,
                  old_scheme_geometry=geometry,positive_block_scheme_geometry_check=positive_geometry,
                  geometry_only_appended_block_note='The extra (0,5) block in the positive-block geometry checker is not part of any source word or matrix.',
                  original_old_source_columns=old_columns,original_new_source_columns=columns,
                  inherited_indices_in_new_source_coordinates=inherited_ids,
                  observation_points=points,rejected_reference_observation_points=rejected,
                  old_scalar_matrix=old_rows,old_scalar_certificate=old_certificate,
                  old_scalar_pivot_columns=old_pivots,old_scalar_free_columns=old_free,
                  old_original_source_kernel_basis=old_kernel,
                  old_original_source_kernel_basis_sha256=residue.matrix_hash(old_kernel),
                  old_scalar_target=old_dimension,full_scalar_target=scalar_target,
                  scope='Only these prescribed finite-field fixtures and these exact conditional source selectors. A finite deficiency is not a generic failure.')
    if len(old_pivots) != old_dimension:
        result.update(status='Old scalar image does not reach the required finite target.',elapsed_seconds=time.monotonic()-started)
        return result
    assert old_pivots == reference['inherited_observation_certificate']['rank_certificate']['nonzero_minor']['columns']
    Kold = split.transpose(old_kernel)
    assert not any(value for row in schur.matrix_product(old_rows,Kold) for value in row)
    trace_xs,trace_rejected = line_points(old_tables,3**q,3*q,790024+q)
    trace_rows,trace_controls = [],[]
    for x in trace_xs:
        X = (-3**q % P,x,1)
        evaluate,_,_,denominators = source.evaluator(old_tables,X)
        actual = evaluate(old_columns)
        D = determinant_product(denominators)
        trace_rows.append([D*R[1]*source.inverse(X[0]*X[1]) % P for R in actual])
        assert not any(schur.matrix_product([[R[2] for R in actual]],Kold)[0])
        trace_controls.append(dict(point=X,old_line_denominators=denominators,D_old=D))
    trace = schur.matrix_product(trace_rows,Kold)
    trace_certificate = incoming.matrix_certificate(trace[:3*q])
    V = [[pow(x,k,P) for k in range(3*q)] for x in trace_xs[:3*q]]
    Vinverse,Vcertificate = schur.invert(V)
    trace_coefficients = schur.matrix_product(Vinverse,trace[:3*q])
    for x,row in zip(trace_xs[3*q:],trace[3*q:]):
        assert schur.matrix_product([[pow(x,k,P) for k in range(3*q)]],trace_coefficients)[0] == row
    result.update(old_trace_definition='D_q f=D_q R1/(X0 X1), restricted to X0=-v_n X2, X2=1.',
                  old_trace_x_values=trace_xs,old_trace_rejected_x_values=trace_rejected,
                  old_trace_point_controls=trace_controls,old_trace_observations=trace_rows,
                  old_trace_on_original_kernel=trace,old_trace_certificate=trace_certificate,
                  old_trace_coefficient_matrix=trace_coefficients,old_trace_interpolation_certificate=Vcertificate,
                  six_extra_old_trace_interpolation_checks_passed=True)
    if trace_certificate['rank_certificate']['rank'] != 3*q:
        result.update(status='Old kernel trace does not reach the required 3q target.',elapsed_seconds=time.monotonic()-started)
        return result
    trace_selected = trace_certificate['rank_certificate']['nonzero_minor']['columns']
    assert len(trace_selected) == 3*q
    accepted = boundary.candidate_columns(n)
    accepted_terms = boundary.candidate_inclusion(n,accepted,columns)
    accepted_order = [j for kind in (('A','A_star'),('B',),('T',),('M',),('E',))
                      for j,c in enumerate(accepted) if c['label']['kind'] in kind]
    appended_terms = [[(inherited_ids[i],value) for i,value in enumerate(old_kernel[j]) if value]
                      for j in trace_selected]
    basis_terms = [[(inherited_ids[i],1)] for i in old_pivots]+[accepted_terms[j] for j in accepted_order]+appended_terms
    basis_labels = ([dict(kind='old_scalar_basis',old_source_index=i,source_label=old_columns[i]['label']) for i in old_pivots]
                    +[dict(kind='accepted_new',source_label=accepted[j]['label']) for j in accepted_order]
                    +[dict(kind='appended_old_kernel',old_kernel_index=j) for j in trace_selected])
    assert len(basis_terms) == scalar_target
    basis_coefficients = projected.sparse_columns(basis_terms,len(columns))
    basis_rows = [source.combine_values(row,basis_terms) for row in scalar_rows]
    scalar_certificate = incoming.matrix_certificate(basis_rows)
    result.update(selected_old_kernel_indices=trace_selected,
                  selected_old_kernel_vectors=[old_kernel[j] for j in trace_selected],
                  full_scalar_basis_order='Saved old scalar basis; accepted A,Astar,B,T1,T2,M,E2; selected 3q appended old-kernel vectors.',
                  full_scalar_basis_labels=basis_labels,full_scalar_basis_terms=basis_terms,
                  full_scalar_basis_original_source_coefficient_matrix=basis_coefficients,
                  full_scalar_basis_evaluation_matrix=basis_rows,full_scalar_basis_certificate=scalar_certificate)
    if scalar_certificate['rank_certificate']['rank'] != scalar_target:
        result.update(status='The prescribed positive full scalar basis is singular.',elapsed_seconds=time.monotonic()-started)
        return result
    scalar_selected_rows = scalar_certificate['rank_certificate']['nonzero_minor']['rows']
    scalar_square = [basis_rows[i] for i in scalar_selected_rows]
    scalar_inverse,scalar_inverse_certificate = schur.invert(scalar_square)
    body_ids,endpoint_ids = source_selectors(columns,n)
    seed_ids = body_ids+endpoint_ids
    raw = projected.sparse_columns([[(i,1)] for i in seed_ids],len(columns))
    correction = schur.matrix_product(scalar_inverse,projected.select_columns([scalar_rows[i] for i in scalar_selected_rows],seed_ids))
    corrected = projected.subtract(raw,schur.matrix_product(basis_coefficients,correction))
    assert not any(value for row in schur.matrix_product(scalar_rows,corrected) for value in row)
    append_coefficients = projected.sparse_columns(appended_terms,len(columns))
    old_selected_coefficients = split.transpose([old_kernel[j] for j in trace_selected])
    ordinary_controls = []
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        evaluate_old,_,_,old_denominators = source.evaluator(old_tables,X)
        evaluate,kernels,_,denominators = source.evaluator(tables,X)
        old_vectors = schur.matrix_product(split.transpose(evaluate_old(old_columns)),old_selected_coefficients)
        all_vectors = evaluate(columns)
        new_vectors = schur.matrix_product(split.transpose(all_vectors),append_coefficients)
        assert not any(old_vectors[2])
        expected = split.transpose(schur.matrix_product(split.transpose(old_vectors),kernels[n]))
        assert expected == new_vectors
        Dold,Dnew = determinant_product(old_denominators),determinant_product(denominators)
        unew,vnew = times[-1]
        actual_cleared = [Dnew*R2*source.inverse(X[2]) % P for R2 in new_vectors[2]]
        expected_cleared = [-unew*vnew*X[1]*denominators[-1][2]*Dold*R1 % P for R1 in old_vectors[1]]
        assert actual_cleared == expected_cleared
        projected_vectors = schur.matrix_product(split.transpose(all_vectors),corrected)
        assert not any(projected_vectors[2])
        ordinary_controls.append(dict(point=X,all_line_denominators=denominators,
            appended_selected_kernel_vectors=new_vectors,
            exact_append_and_scalar_splitting_formula_verified=True,
            projected_body_and_endpoint_vectors=projected_vectors))
    aux_xs,aux_rejected = line_points(tables,w,3*n,800024+n)
    aux_rows,aux_controls = [],[]
    polynomial_checks = 0
    for i,x in enumerate(aux_xs):
        X = (-w % P,x,1)
        evaluate,_,_,denominators = source.evaluator(tables,X)
        actual = evaluate(columns)
        D = determinant_product(denominators)
        factor = -D*source.inverse(w*x) % P
        aux_rows.append([factor*R[1] % P for R in actual])
        if i in (0,3*n,len(aux_xs)-1):
            polynomial,polynomial_D = joint.cleared_component_values(times,X,columns)
            assert D == polynomial_D and polynomial == [D*R[1] % P for R in actual]
            polynomial_checks += len(columns)
        aux_controls.append(dict(point=X,all_line_denominators=denominators,D_n=D))
    aux_image = schur.matrix_product(aux_rows,corrected)
    aux_V = [[pow(x,k,P) for k in range(3*n)] for x in aux_xs[:3*n]]
    aux_inverse,aux_Vcertificate = schur.invert(aux_V)
    aux_coefficients = schur.matrix_product(aux_inverse,aux_image[:3*n])
    for x,row in zip(aux_xs[3*n:],aux_image[3*n:]):
        assert schur.matrix_product([[pow(x,k,P) for k in range(3*n)]],aux_coefficients)[0] == row
    square = aux_image[:3*n]
    body_matrix = projected.select_columns(square,list(range(3*q)))
    body_certificate = incoming.matrix_certificate(body_matrix)
    full_aux_certificate = incoming.matrix_certificate(square)
    result.update(scalar_basis_selected_rows=scalar_selected_rows,
                  scalar_basis_selected_square=scalar_square,scalar_basis_inverse_certificate=scalar_inverse_certificate,
                  raw_body_original_indices=body_ids,raw_body_original_columns=[columns[i] for i in body_ids],
                  raw_endpoint_original_indices=endpoint_ids,raw_endpoint_original_columns=[columns[i] for i in endpoint_ids],
                  common_full_scalar_projection_coefficients=correction,
                  scalar_corrected_actual_source_coefficient_matrix=corrected,
                  scalar_projection_verified_on_all_observation_rows=True,independent_ordinary_controls=ordinary_controls,
                  auxiliary_definition='B_w=-D_n R1/(w X1 X2), X=(-w,x,1), w=5.',
                  auxiliary_x_values=aux_xs,auxiliary_rejected_x_values=aux_rejected,
                  auxiliary_point_controls=aux_controls,actual_auxiliary_observation_matrix=aux_rows,
                  auxiliary_matrix_after_common_scalar_projection=aux_image,
                  auxiliary_polynomial_coefficient_matrix=aux_coefficients,
                  auxiliary_interpolation_certificate=aux_Vcertificate,
                  six_extra_auxiliary_interpolation_checks_passed=True,
                  independent_cleared_word_component_checks=polynomial_checks,
                  body_evaluation_matrix=body_matrix,body_certificate=body_certificate,
                  full_auxiliary_square=square,full_auxiliary_certificate=full_aux_certificate)
    if body_certificate['rank_certificate']['rank'] != 3*q:
        result.update(status='The prescribed body selector is deficient after full scalar projection.',elapsed_seconds=time.monotonic()-started)
        return result
    body_rows = body_certificate['rank_certificate']['nonzero_minor']['rows']
    remaining_rows = [i for i in range(3*n) if i not in body_rows]
    assert len(body_rows) == 3*q and len(remaining_rows) == 3
    body_square = [body_matrix[i] for i in body_rows]
    body_inverse,body_inverse_certificate = schur.invert(body_square)
    endpoints = projected.select_columns(square,list(range(3*q,3*n)))
    body_correction = schur.matrix_product(body_inverse,[endpoints[i] for i in body_rows])
    residual = projected.subtract(endpoints,schur.matrix_product(body_matrix,body_correction))
    assert not any(value for i in body_rows for value in residual[i])
    endpoint_schur = [residual[i] for i in remaining_rows]
    endpoint_certificate = incoming.matrix_certificate(endpoint_schur)
    endpoint_source = projected.subtract(projected.select_columns(corrected,list(range(3*q,3*n))),
                                        schur.matrix_product(projected.select_columns(corrected,list(range(3*q))),body_correction))
    assert schur.matrix_product(aux_rows[:3*n],endpoint_source) == residual
    assert not any(value for row in schur.matrix_product(scalar_rows,endpoint_source) for value in row)
    row_order = body_rows+remaining_rows
    sign = schur.permutation_sign(row_order)
    determinant_product_value = body_inverse_certificate['determinant_mod_prime']*endpoint_certificate['rank_certificate']['determinant_mod_prime'] % P
    assert sign*full_aux_certificate['rank_certificate']['determinant_mod_prime'] % P == determinant_product_value
    result.update(status='Completed fixed-fixture scalar/body/endpoint Schur verification.',
                  body_selected_rows=body_rows,endpoint_remaining_rows=remaining_rows,
                  body_selected_square=body_square,body_inverse_certificate=body_inverse_certificate,
                  endpoint_correction_coefficients_in_same_body_basis=body_correction,
                  endpoint_after_scalar_and_body_original_source_coefficients=endpoint_source,
                  endpoint_residual_on_all_auxiliary_rows=residual,
                  endpoint_schur_matrix=endpoint_schur,endpoint_schur_certificate=endpoint_certificate,
                  endpoint_schur_rank=endpoint_certificate['rank_certificate']['rank'],
                  full_auxiliary_rank=full_aux_certificate['rank_certificate']['rank'],
                  full_auxiliary_target=3*n,row_permutation_sign=sign,
                  exact_schur_determinant_identity_verified=True,
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q,n=n,old_scalar_rank=len(old_pivots),old_trace_rank=3*q,
                          prescribed_scalar_basis_rank=scalar_certificate['rank_certificate']['rank'],
                          body_rank=body_certificate['rank_certificate']['rank'],
                          endpoint_schur_rank=result['endpoint_schur_rank'],
                          endpoint_schur_determinant=endpoint_certificate['rank_certificate']['determinant_mod_prime'],
                          full_auxiliary_rank=result['full_auxiliary_rank'],
                          full_auxiliary_determinant=full_aux_certificate['rank_certificate']['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-zero-prefix-boundary-extension-results.json').read_text())
    keys = ('q','n','time_factors','observation_points','inherited_observation_certificate')
    references = {case['q']:{key:case[key] for key in keys}
                  for case in saved['predetermined_generic_alternative_followup']['cases'] if case['q'] in (4,5)}
    del saved
    started,cases,limitation = time.monotonic(),[],None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for q in (4,5):
            case = calculate(references[q])
            cases.append(case)
            if 'endpoint_schur_rank' not in case:
                print(json.dumps(dict(q=q,status=case['status'],elapsed_seconds=case['elapsed_seconds'])),flush=True)
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Prescribed conditional scalar basis and coupled endpoint Schur test at positive new u.',
                  scope='Only q=4,5, old/new positive seven-power u and three-power v, auxiliary w=5, prime 1000003. No parameter scan or uniform endpoint claim.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
