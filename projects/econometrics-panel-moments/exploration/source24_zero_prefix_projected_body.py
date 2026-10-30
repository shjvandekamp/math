#!/usr/bin/env python3
"""Specified body candidates after one fixed actual scalar correction.

Only q=4,5 at the previously prescribed seven-power old u fixture are
tested.  The scalar basis is an independent appended-old subset followed
by the accepted A,B,T1,T2,M,E2 columns.  All proposed body columns use this
same basis inverse; no arbitrary boundary pivot replacement is made.

The proposed 2q axis columns are E0,E1,C_(2,n)^01, the two columns
C_(t,n)^01,C_(t,n)^11 for t=3..q, and C_(n,2)^10.  Test each additional
q-column family C_(t,n)^12 and C_(t,n)^22 separately, after the same scalar
projection and then the same axis correction.  Actual residue-limit
observations are reused from the body-limit verifier with their original
normalizations.  This is a finite test, not a uniform rank proof.

The optional --complete-matching pass preserves the first results, tests
the C12/C22 union, and searches the prescribed remaining actual source
columns in a fixed order through the SAME scalar and axis correction.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_zero_prefix_body_limit as body


source,boundary,split = body.source,body.boundary,body.split
P,G = source.P,source.G
incoming,residue,schur = source.incoming,source.residue,source.schur
HERE = Path(__file__).resolve().parent


def sparse_columns(terms,count):
    matrix = [[0]*len(terms) for _ in range(count)]
    for j,column in enumerate(terms):
        for i,value in column:
            matrix[i][j] = (matrix[i][j]+value) % P
    return matrix


def select_columns(matrix,indices):
    return [[row[j] for j in indices] for row in matrix]


def subtract(A,B):
    assert len(A) == len(B)
    return [[(x-y) % P for x,y in zip(a,b)] for a,b in zip(A,B)]


def seed_indices(columns,n):
    q = n-1
    C = {(c['label']['t'],c['label']['s'],c['label']['a'],c['label']['b']):i
         for i,c in enumerate(columns) if c['label']['kind'] == 'C'}
    H = {(c['label']['t'],c['label']['a']):i
         for i,c in enumerate(columns) if c['label']['kind'] == 'H'}
    axis = [H[n,0],H[n,1],C[2,n,0,1]]
    axis += [C[t,n,a,1] for t in range(3,q+1) for a in (0,1)]
    axis += [C[n,2,1,0]]
    assert len(axis) == 2*q
    return axis,[C[t,n,1,2] for t in range(1,q+1)],[C[t,n,2,2] for t in range(1,q+1)]


def completion_priority(columns,n):
    q = n-1
    C = {(c['label']['t'],c['label']['s'],c['label']['a'],c['label']['b']):i
         for i,c in enumerate(columns) if c['label']['kind'] == 'C'}
    H = {(c['label']['t'],c['label']['a']):i
         for i,c in enumerate(columns) if c['label']['kind'] == 'H'}
    result = [C[2,n,1,1]]
    result += [C[t,n,2,1] for t in range(1,q+1)]
    result += [H[n,2]]
    result += [C[n,s,a,0] for s in range(2,q+1) for a in (0,1,2)]
    result += [C[t,n,a,0] for t in range(1,q+1) for a in (0,1)]
    result += [C[1,n,1,1]]
    result += [i for i,c in enumerate(columns)
               if (c['label']['kind'] == 'C' and n in (c['label']['t'],c['label']['s']))
               or (c['label']['kind'] == 'H' and c['label']['t'] == n)]
    return list(dict.fromkeys(result))


def binary_weight_comparison(times,union):
    """Compare the suggested raw incidence weights with the corrected map."""
    q,tables = len(times)-1,source.tables_at(times[:-1])
    weights,records = [],[]
    for t in range(1,q+1):
        X,_ = body.coordinates_for_line(times,t,2)
        determinants,product = [],1
        for s in range(1,q+1):
            if s == t:
                continue
            K = residue.ordinary_kernel(tables,s,X,P)
            determinant = (K[0][0]*K[1][1]-K[0][1]*K[1][0]) % P
            assert determinant
            determinants.append(dict(old_block=s,binary_determinant=determinant))
            product = product*determinant % P
        weights.append(source.inverse(product))
        records.append(dict(matching_block=t,point=X,other_old_binary_determinants=determinants,
                            product=product,inverse_product=weights[-1]))
    action = schur.matrix_product([weights],union)[0]
    return dict(formula='w_t=1/product_{s!=t} det(K_s restricted to states 0,1), at the state-2 matching point.',
                records=records,weights=weights,action_on_corrected_union=action,
                annihilates_corrected_union=not any(action))


def complete_matching(case):
    started,n,q = time.monotonic(),case['n'],case['q']
    assert q in (4,5) and n == q+1 and case['axis_rank'] == 2*q
    columns,_ = source.larger_columns(n)
    assert json.loads(json.dumps(columns)) == case['original_source_columns']
    families = case['matching_families']
    assert [family['family'] for family in families] == ['C_tn_12','C_tn_22']
    for family in families:
        assert residue.matrix_hash(family['matching_matrix']) == family['matching_certificate']['sha256']
    union = [left+right for left,right in zip(families[0]['matching_matrix'],families[1]['matching_matrix'])]
    union_coefficients = [left+right for left,right in zip(
        families[0]['twice_corrected_original_source_coefficients'],families[1]['twice_corrected_original_source_coefficients'])]
    union_labels = [dict(family=family['family'],original_source_index=index,
                        original_source_column=columns[index])
                    for family in families for index in family['raw_original_source_indices']]
    union_certificate = incoming.matrix_certificate(union)
    union_rank = union_certificate['rank_certificate']['rank']
    _,_,left_nullvectors = source.dual.rref_kernel(split.transpose(union))
    assert len(left_nullvectors) == q-union_rank
    for vector in left_nullvectors:
        assert not any(schur.matrix_product([vector],union)[0])
    result = dict(q=q,n=n,prime=P,time_factors=case['time_factors'],
                  previous_matching_ranks=[family['matching_rank'] for family in families],
                  union_column_labels=union_labels,corrected_union_matching_matrix=union,
                  union_certificate=union_certificate,union_rank=union_rank,
                  canonical_left_nullvectors=left_nullvectors,
                  left_nullvector_coordinate_order='State-2 matching rows, old blocks 1,...,q.',
                  raw_binary_incidence_weight_comparison=binary_weight_comparison(case['time_factors'],union))
    if union_rank == q-1:
        assert len(left_nullvectors) == 1
        left_null = left_nullvectors[0]
        candidate_ids = completion_priority(columns,n)
        tables = source.tables_at(case['time_factors'])
        selected_rows = case['scalar_basis_observation_rows']
        scalar_rows = []
        for i in selected_rows:
            X = case['observation_points'][i]
            evaluate,_,_,_ = source.evaluator(tables,X)
            scalar_rows.append([R[2]*source.inverse(X[2]) % P for R in evaluate(columns)])
        actual_basis = [source.combine_values(row,case['scalar_basis_terms_in_original_source_coordinates']) for row in scalar_rows]
        assert actual_basis == case['scalar_basis_selected_square']
        inverse,certificate = schur.invert(actual_basis)
        assert certificate['determinant_mod_prime'] == case['scalar_basis_selected_square_certificate']['determinant_mod_prime']
        correction = schur.matrix_product(inverse,select_columns(scalar_rows,candidate_ids))
        raw = sparse_columns([[(i,1)] for i in candidate_ids],len(columns))
        projected = subtract(raw,schur.matrix_product(case['scalar_basis_coefficient_matrix'],correction))
        assert not any(value for row in schur.matrix_product(scalar_rows,projected) for value in row)
        observations = case['actual_body_limit_observation_matrix']
        image = schur.matrix_product(observations,projected)
        axis_inverse,_ = schur.invert(case['specified_axis_matrix'])
        axis_correction = schur.matrix_product(axis_inverse,image[:2*q])
        axis_coefficients = select_columns(case['scalar_projected_original_source_coefficient_matrix'],list(range(2*q)))
        corrected = subtract(projected,schur.matrix_product(axis_coefficients,axis_correction))
        corrected_image = schur.matrix_product(observations,corrected)
        assert not any(value for row in corrected_image[:2*q] for value in row)
        matching = corrected_image[2*q:]
        actions = schur.matrix_product([left_null],matching)[0]
        # These named columns must vanish under the fixed correction itself.
        zero_controls = []
        for j,index in enumerate(candidate_ids):
            label = columns[index]['label']
            accepted = (label['kind'] == 'H' and label['t'] == n and label['a'] == 2)
            accepted |= (label['kind'] == 'C' and label['s'] == n and label['a'] in (0,1) and label['b'] == 0)
            axis_member = label == dict(kind='C',t=n,s=2,a=1,b=0)
            if accepted or axis_member:
                assert not any(row[j] for row in corrected)
                zero_controls.append(index)
        ordinary_controls = []
        for X in ((1,2,3),(2,3,5),(3,5,7)):
            evaluate,_,_,_ = source.evaluator(tables,X)
            R = schur.matrix_product(split.transpose(evaluate(columns)),corrected)
            assert not any(R[2])
            assert all((a+b+c) % P == 0 for a,b,c in zip(*R))
            ordinary_controls.append(dict(point=X,twice_corrected_vector_matrix_sha256=residue.matrix_hash(R),
                                          scalar_component_zero=True))
        chosen = next((j for j,value in enumerate(actions) if value),None)
        result.update(candidate_priority_original_indices=candidate_ids,
                      candidate_priority_original_columns=[columns[i] for i in candidate_ids],
                      same_scalar_basis_inverse_certificate=certificate,
                      scalar_correction_coefficients_in_fixed_basis=correction,
                      axis_correction_coefficients_in_fixed_axis_basis=axis_correction,
                      twice_corrected_original_source_coefficients=corrected,
                      matching_matrix_for_all_remaining_new_generators=matching,
                      left_nullvector_action_by_candidate=actions,
                      accepted_or_axis_basis_columns_verified_zero=zero_controls,
                      ordinary_scalar_cancellation_controls=ordinary_controls,
                      first_completing_priority_index=chosen)
        if chosen is not None:
            old_selection = union_certificate['rank_certificate']['nonzero_minor']['columns']
            assert len(old_selection) == q-1
            selected_matching = [([row[j] for j in old_selection]+[newrow[chosen]])
                                 for row,newrow in zip(union,matching)]
            matching_certificate = incoming.matrix_certificate(selected_matching)
            assert matching_certificate['rank_certificate']['rank'] == q
            matching_coefficients = [([row[j] for j in old_selection]+[newrow[chosen]])
                                     for row,newrow in zip(union_coefficients,corrected)]
            joint_coefficients = [left+right for left,right in zip(axis_coefficients,matching_coefficients)]
            joint = schur.matrix_product(observations,joint_coefficients)
            joint_certificate = incoming.matrix_certificate(joint)
            expected = case['axis_certificate']['rank_certificate']['determinant_mod_prime']*matching_certificate['rank_certificate']['determinant_mod_prime'] % P
            assert joint_certificate['rank_certificate']['rank'] == 3*q
            assert joint_certificate['rank_certificate']['determinant_mod_prime'] == expected
            result['completion'] = dict(additional_original_source_index=candidate_ids[chosen],
                additional_original_source_column=columns[candidate_ids[chosen]],
                left_nullvector_action=actions[chosen],
                selected_union_column_indices=old_selection,
                selected_union_columns=[union_labels[j] for j in old_selection],
                completed_matching_matrix=selected_matching,completed_matching_certificate=matching_certificate,
                completed_actual_source_coefficient_matrix=joint_coefficients,
                completed_axis_plus_matching_matrix=joint,completed_axis_plus_matching_certificate=joint_certificate,
                determinant_equals_axis_determinant_times_matching_determinant=True)
    elif union_rank == q:
        result['completion_not_needed'] = 'The requested union already supplies all q matching directions.'
    else:
        result['limitation'] = 'The union deficit exceeds one; no single-pivot completion was assumed.'
    result['scope'] = 'The prior failures are retained. This uses one fixed fixture and exactly the same actual scalar and axis projection; any extra pivot is a finite certificate, not a uniform theorem.'
    result['elapsed_seconds'] = time.monotonic()-started
    completion = result.get('completion')
    print(json.dumps(dict(q=q,union_rank=union_rank,left_nullity=len(left_nullvectors),
                          raw_binary_weights_annihilate_union=result['raw_binary_incidence_weight_comparison']['annihilates_corrected_union'],
                          additional_source=(completion['additional_original_source_column']['label'] if completion else None),
                          left_nullvector_action=(completion['left_nullvector_action'] if completion else None),
                          matching_determinant=(completion['completed_matching_certificate']['rank_certificate']['determinant_mod_prime'] if completion else None),
                          combined_determinant=(completion['completed_axis_plus_matching_certificate']['rank_certificate']['determinant_mod_prime'] if completion else None),
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def calculate(reference):
    started,n = time.monotonic(),reference['n']
    q = n-1
    times = reference['time_factors']
    assert times == [[7**(t-1),3**(t-1)] for t in range(1,n)]+[[0,3**q]]
    assert reference['prime'] == P and reference['G'] == [list(row) for row in G]
    columns,_ = source.larger_columns(n)
    inherited,_ = source.larger_columns(q)
    accepted = boundary.candidate_columns(n)
    assert json.loads(json.dumps(inherited)) == reference['inherited_original_source_columns']
    assert json.loads(json.dumps(accepted)) == reference['candidate_original_source_columns']
    original_index = {json.dumps(c,sort_keys=True):i for i,c in enumerate(columns)}
    inherited_ids = [original_index[json.dumps(c,sort_keys=True)] for c in inherited]
    accepted_terms = boundary.candidate_inclusion(n,accepted,columns)
    assert json.loads(json.dumps(accepted_terms)) == reference['candidate_terms_in_full_zero_prefix']
    accepted_order = [j for kind in (('A','A_star'),('B',),('T',),('M',),('E',))
                      for j,c in enumerate(accepted) if c['label']['kind'] in kind]
    assert sorted(accepted_order) == list(range(6*q+3))
    old_pivots = reference['inherited_observation_certificate']['rank_certificate']['nonzero_minor']['columns']
    basis_terms = [[(inherited_ids[i],1)] for i in old_pivots]+[accepted_terms[j] for j in accepted_order]
    basis_labels = [inherited[i]['label'] for i in old_pivots]+[accepted[j]['label'] for j in accepted_order]
    basis_coefficients = sparse_columns(basis_terms,len(columns))
    basis_size = len(basis_terms)
    geometry = split.field_geometry(times)
    assert len(old_pivots) == 9*q*(q-1)//2+3*q
    assert basis_size == geometry['boundary_ambient_dimension']
    axis_ids,matching12_ids,matching22_ids = seed_indices(columns,n)
    seed_ids = axis_ids+matching12_ids+matching22_ids
    seed_coefficients = sparse_columns([[(i,1)] for i in seed_ids],len(columns))

    tables = source.tables_at(times)
    scalar_rows = []
    for X in reference['observation_points']:
        evaluate,_,_,_ = source.evaluator(tables,X)
        scalar_rows.append([R[2]*source.inverse(X[2]) % P for R in evaluate(columns)])
    inherited_rows = select_columns(scalar_rows,inherited_ids)
    assert residue.matrix_hash(inherited_rows) == reference['inherited_observation_certificate']['sha256']
    accepted_rows = [source.combine_values(row,accepted_terms) for row in scalar_rows]
    assert accepted_rows == reference['actual_candidate_evaluation_matrix']
    combined = [old+new for old,new in zip(inherited_rows,accepted_rows)]
    assert residue.matrix_hash(combined) == reference['combined_certificate']['sha256']
    basis_rows = [source.combine_values(row,basis_terms) for row in scalar_rows]
    selected_rows = reference['combined_certificate']['rank_certificate']['nonzero_minor']['rows']
    assert len(selected_rows) == basis_size
    basis_square = [basis_rows[i] for i in selected_rows]
    basis_inverse,basis_certificate = schur.invert(basis_square)
    seed_scalar = select_columns(scalar_rows,seed_ids)
    correction = schur.matrix_product(basis_inverse,[seed_scalar[i] for i in selected_rows])
    projected = subtract(seed_coefficients,schur.matrix_product(basis_coefficients,correction))
    assert not any(value for row in schur.matrix_product(scalar_rows,projected) for value in row)
    generic_controls = []
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        evaluate,_,_,denominators = source.evaluator(tables,X)
        vectors = evaluate(columns)
        corrected_vectors = schur.matrix_product(split.transpose(vectors),projected)
        assert not any(corrected_vectors[2])
        assert all((a+b+c) % P == 0 for a,b,c in zip(*corrected_vectors))
        generic_controls.append(dict(point=X,all_line_denominators=denominators,
                                     projected_vector_matrix=corrected_vectors))

    row_labels = [dict(old_block=t,state=a,coefficient='delta^0')
                  for t in range(1,q+1) for a in (0,1)]
    row_labels += [dict(old_block=t,state=2,coefficient='delta^1') for t in range(1,q+1)]
    observations,point_controls = [],[]
    polynomial_checks = 0
    for label in row_labels:
        t,a = label['old_block'],label['state']
        row,actual,control = body.actual_residue_values(times,t,a,columns)
        observations.append(row)
        if (t,a) in ((1,0),(q,2)):
            cleared,other_D = body.polynomial_residue_control(times,t,a,columns)
            assert actual == cleared
            control['independent_polynomial_residue_check'] = dict(D_n_over_matched_line_jet=other_D,
                both_orders_match_every_source_column=True)
            polynomial_checks += 2*len(columns)
        point_controls.append(dict(**label,**control))
    image = schur.matrix_product(observations,projected)
    projected_axis = select_columns(projected,list(range(2*q)))
    axis_full_image = select_columns(image,list(range(2*q)))
    axis = axis_full_image[:2*q]
    axis_certificate = incoming.matrix_certificate(axis)
    axis_rank = axis_certificate['rank_certificate']['rank']
    outcomes = []
    if axis_rank == 2*q:
        axis_inverse,axis_inverse_certificate = schur.invert(axis)
        assert axis_inverse_certificate['determinant_mod_prime'] == axis_certificate['rank_certificate']['determinant_mod_prime']
        for name,start,ids in (('C_tn_12',2*q,matching12_ids),('C_tn_22',3*q,matching22_ids)):
            group_indices = list(range(start,start+q))
            group = select_columns(projected,group_indices)
            group_image = select_columns(image,group_indices)
            axis_correction = schur.matrix_product(axis_inverse,group_image[:2*q])
            corrected = subtract(group,schur.matrix_product(projected_axis,axis_correction))
            corrected_image = schur.matrix_product(observations,corrected)
            assert not any(value for row in corrected_image[:2*q] for value in row)
            assert not any(value for row in schur.matrix_product(scalar_rows,corrected) for value in row)
            matching = corrected_image[2*q:]
            matching_certificate = incoming.matrix_certificate(matching)
            matching_rank = matching_certificate['rank_certificate']['rank']
            block = [left+right for left,right in zip(axis_full_image,corrected_image)]
            block_certificate = incoming.matrix_certificate(block)
            assert block_certificate['rank_certificate']['rank'] == 2*q+matching_rank
            if matching_rank == q:
                expected = axis_certificate['rank_certificate']['determinant_mod_prime']*matching_certificate['rank_certificate']['determinant_mod_prime'] % P
                assert block_certificate['rank_certificate']['determinant_mod_prime'] == expected
            outcomes.append(dict(family=name,raw_original_source_indices=ids,
                raw_original_source_columns=[columns[i] for i in ids],
                scalar_projected_original_source_coefficients=group,
                axis_observations_before_axis_correction=group_image[:2*q],
                axis_observations_already_zero=not any(value for row in group_image[:2*q] for value in row),
                correction_coefficients_in_specified_axis_basis=axis_correction,
                twice_corrected_original_source_coefficients=corrected,
                exact_scalar_and_axis_cancellation_verified=True,
                matching_matrix=matching,matching_certificate=matching_certificate,matching_rank=matching_rank,
                combined_axis_matching_matrix=block,combined_axis_matching_certificate=block_certificate,
                determinant_factorization_checked_when_nonsingular=(matching_rank == q)))
    result = dict(n=n,q=q,prime=P,G=G,time_factors=times,field_geometry=geometry,
                  fixture_reference='source24-zero-prefix-boundary-extension-results.json: predetermined_generic_alternative_followup',
                  verified_reference_combined_scalar_matrix_sha256=reference['combined_certificate']['sha256'],
                  original_source_columns=columns,
                  scalar_basis_order='Selected appended-old generators, A, Astar, B, T1,T2, M, E2.',
                  inherited_basis_indices_in_original_old_family=old_pivots,
                  scalar_basis_labels=basis_labels,scalar_basis_terms_in_original_source_coordinates=basis_terms,
                  scalar_basis_coefficient_matrix=basis_coefficients,
                  scalar_basis_observation_rows=selected_rows,
                  scalar_basis_selected_square=basis_square,scalar_basis_selected_square_certificate=basis_certificate,
                  scalar_basis_size=basis_size,scalar_basis_saturates_verified_boundary_ambient=True,
                  observation_points=reference['observation_points'],
                  projected_scalar_zero_at_all_saved_points=True,independent_ordinary_controls=generic_controls,
                  seed_original_source_indices=seed_ids,seed_original_source_columns=[columns[i] for i in seed_ids],
                  seed_groups=['axis']*(2*q)+['C_tn_12']*q+['C_tn_22']*q,
                  exact_scalar_correction_coefficients_in_fixed_basis=correction,
                  scalar_projected_original_source_coefficient_matrix=projected,
                  body_limit_row_labels=row_labels,body_limit_point_controls=point_controls,
                  actual_body_limit_observation_matrix=observations,
                  body_limit_matrix_after_same_scalar_projection=image,
                  axis_original_source_indices=axis_ids,axis_original_source_columns=[columns[i] for i in axis_ids],
                  specified_axis_matrix=axis,axis_certificate=axis_certificate,
                  axis_rank=axis_rank,axis_target=2*q,axis_target_attained=axis_rank == 2*q,
                  matching_families=outcomes,independent_polynomial_residue_component_checks=polynomial_checks,
                  scope='Only q=4,5 at the recorded fixed fixture. The same specified scalar basis and axis correction are retained for both matching families. No uniform nonvanishing or generic failure follows from these observations.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q,n=n,scalar_basis_size=basis_size,axis_rank=axis_rank,axis_target=2*q,
                          axis_determinant=axis_certificate['rank_certificate'].get('determinant_mod_prime'),
                          matching=[dict(family=outcome['family'],rank=outcome['matching_rank'],
                                         axis_already_zero=outcome['axis_observations_already_zero'],
                                         determinant=outcome['matching_certificate']['rank_certificate'].get('determinant_mod_prime'))
                                    for outcome in outcomes],elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--complete-matching',action='store_true',
                        help='Preserve the first results and append the fixed-basis union and completion diagnostic.')
    args = parser.parse_args()
    previous = None
    if args.complete_matching:
        assert args.output and args.output.is_file()
        previous = json.loads(args.output.read_text())
        references = {case['q']:case for case in previous['cases']}
    else:
        saved = json.loads((HERE/'source24-zero-prefix-boundary-extension-results.json').read_text())
        references = {case['q']:case for case in saved['predetermined_generic_alternative_followup']['cases'] if case['q'] in (4,5)}
        del saved
    started,cases,limitation = time.monotonic(),[],None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for q in (4,5):
            cases.append(complete_matching(references[q]) if args.complete_matching else calculate(references[q]))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Specified body-axis and matching families after exact coupled scalar correction.',
                  scope='Only q=4,5, old times (7^(t-1),3^(t-1)), new times (0,3^q), prime 1000003. Both proposed matching families tested separately; no scans.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    statistics = {key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}
    if args.complete_matching:
        result['status'] = 'Follow-up: union, common left nullvector, and prescribed actual-source completion after the same corrections.'
        result['scope'] = 'Only the previous q=4,5 fixtures and fixed projection. Original individual-family failures remain recorded above.'
        previous['matching_completion_followup'] = result
        result = previous
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(statistics),flush=True)


if __name__ == '__main__':
    main()
