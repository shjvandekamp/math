#!/usr/bin/env python3
"""Finite quotient test of the proposed 6q+3 zero-prefix boundary columns.

Use the existing G* fixture, positive old times (6^(t-1),3^(t-1)), and
u_n=0, v_n=3^q.  Start with the accepted 4q A/B columns.  Add
M_t0=C_tn^(0,2), M_t2=C_tn^(2,0), E=empty(n,2)-empty(1,2),
T1=E-sum_b C_1n^(2,b), and T2=E-sum_b C_2n^(2,b)+C_n2^(2,2).

All original source coefficients are retained.  The entire inherited
zero-prefix family precedes the candidate columns in one joint matrix on
the saved boundary observations.  Full observed quotient gain certifies
independence modulo the whole inherited function span; an observed deficit
alone is not a rational-function upper bound or a generic refutation.

The optional --generic-alternative follow-up preserves those cases and tests
the one prescribed old fixture (7^(t-1),3^(t-1)).  It also checks the matching
denominators and the canceled eta/omega formulas in ZP44--47.  No uniform
extension theorem is inferred from these finite cases.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_zero_prefix_extension as source


P, G = source.P, source.G
incoming, residue, schur = source.incoming, source.residue, source.schur
HERE = Path(__file__).resolve().parent


def candidate_columns(n):
    q = n-1
    result = source.new_columns(n)
    for t in range(1,n):
        result += [source.column(dict(kind='M',stage=n,t=t,a=a,b=b),source.Cterms(t,n,a,b))
                   for a,b in ((0,2),(2,0))]
    E = [(1,('empty',n,2)),(-1,('empty',1,2))]
    result.append(source.column(dict(kind='E',stage=n),E))
    for t in (1,2):
        terms = E+[(-coefficient,primitive) for b in range(3)
                   for coefficient,primitive in source.Cterms(t,n,2,b)]
        if t == 2:
            terms += source.Cterms(n,2,2,2)
        result.append(source.column(dict(kind='T',stage=n,t=t),terms))
    assert len(result) == 6*q+3
    return result


def candidate_inclusion(n,candidates,zero):
    Cids = {(c['label']['t'],c['label']['s'],c['label']['a'],c['label']['b']):i
            for i,c in enumerate(zero) if c['label']['kind'] == 'C'}
    Hids = {(c['label']['t'],c['label']['a']):i
            for i,c in enumerate(zero) if c['label']['kind'] == 'H'}
    result = []
    for candidate in candidates:
        label = candidate['label']
        kind = label['kind']
        if kind == 'A':
            terms = [(Cids[label['t'],n,label['a'],0],1)]
        elif kind == 'A_star':
            terms = [(Cids[1,n,label['a'],b],1) for b in range(3)]
        elif kind == 'B':
            terms = [(Cids[n,label['s'],label['a'],2],1)]
        elif kind == 'M':
            terms = [(Cids[label['t'],n,label['a'],label['b']],1)]
        elif kind == 'E':
            terms = [(Hids[n,2],1)]
        else:
            t = label['t']
            terms = [(Hids[n,2],1)]+[(Cids[t,n,2,b],-1) for b in range(3)]
            if t == 2:
                terms.append((Cids[n,2,2,2],1))
        expanded = [(factor*coefficient,primitive) for j,factor in terms
                    for coefficient,primitive in zero[j]['terms']]
        assert source.coefficients(expanded) == source.coefficients(candidate['terms'])
        result.append(terms)
    return result


def direct_word_values(times,X,candidates):
    """Independent canceled C commutators and direct empty-word differences."""
    n = len(times)
    tables = source.tables_at(times)
    kernels = {t:residue.ordinary_kernel(tables,t,X,P) for t in tables}
    products = {}

    def product(order):
        key = tuple(order)
        if key not in products:
            products[key] = residue.word_product(kernels,order,P)
        return products[key]

    def C(t,s,a,b):
        baseline = product(source.word(n,source.first_other(t),t))[b]
        moved = product(source.word(n,s,t))[b]
        return [X[a]*kernels[t][a][b]*(x-y) % P for x,y in zip(baseline,moved)]

    def add(vectors):
        return [sum(vector[d] for vector in vectors) % P for d in range(3)]

    E = [X[2]*(x-y) % P for x,y in zip(product(source.word(n,1))[2],product(source.word(n,n))[2])]
    result = []
    for candidate in candidates:
        label = candidate['label']
        kind = label['kind']
        if kind == 'A':
            value = C(label['t'],n,label['a'],0)
        elif kind == 'A_star':
            value = add([C(1,n,label['a'],b) for b in range(3)])
        elif kind == 'B':
            value = C(n,label['s'],label['a'],2)
        elif kind == 'M':
            value = C(label['t'],n,label['a'],label['b'])
        elif kind == 'E':
            value = E[:]
        else:
            t = label['t']
            summed = add([C(t,n,2,b) for b in range(3)])
            value = [(x-y) % P for x,y in zip(E,summed)]
            if t == 2:
                value = add([value,C(n,2,2,2)])
        assert sum(value) % P == 0
        result.append(value)
    return result


def dual_word(tables,order,X,dX,residue_line=None):
    """Actual product jet, with one optional L_(u,a) K_u residue replacement."""
    dual = source.dual
    coordinates = [(x % P,dx % P) for x,dx in zip(X,dX)]
    result = dual.identity()
    for t in order:
        K = []
        for a,row in enumerate(tables[t]):
            numerators = [dual.scale(row[d],coordinates[d]) for d in range(3)]
            if residue_line is not None and t == residue_line[0]:
                K.append(numerators if a == residue_line[1] else [dual.ZERO]*3)
            else:
                denominator = tuple(sum(v[k] for v in numerators) % P for k in (0,1))
                assert denominator[0]
                K.append([dual.mul(v,dual.inverse(denominator)) for v in numerators])
        result = dual.mmul(result,K)
    return result


def matching_data(times):
    """ZP44 matching geometry and canceled formulas, retaining failed units."""
    q,v = len(times)-1,times[-1][1]
    old = source.tables_at(times[:-1])
    records,by_label = [],{}
    for t,(u,vt) in enumerate(times[:-1],start=1):
        order = [s for s in range(1,q+1) if s != t]
        for a,X in ((0,(0,-vt*source.inverse(u) % P,1)),
                    (2,(1,-source.inverse(3*u) % P,0))):
            values = [[residue.dot(old[s][b],X,P) for b in range(3)] for s in range(1,q+1)]
            assert values[t-1][a] == 0
            collisions = [dict(block=s,state=b) for s in range(1,q+1) for b in range(3)
                          if (s,b) != (t,a) and values[s-1][b] == 0]
            record = dict(block=t,state=a,point=X,old_line_values=values,
                          other_old_line_collisions=collisions,
                          all_other_old_lines_are_units=not collisions,
                          increasing_omitted_word=order)
            if not collisions:
                if a == 0:
                    kernels = {s:residue.ordinary_kernel(old,s,X,P) for s in order}
                    eta = residue.word_product(kernels,order,P)[2][2]
                    diagonal = 2*v*vt*(1-eta) % P
                    record.update(eta=eta,one_minus_eta=(1-eta) % P,
                                  predicted_matching_diagonal=diagonal)
                else:
                    product = dual_word(old,order,X,(0,0,1))
                    assert product[0][2][0] == 0
                    omega = product[0][2][1]
                    # Independent cancellation at the final transition: its
                    # column 2 is identically zero on the X2=0 axis, so only
                    # its own derivative contributes to the output jet.
                    kernels = {s:residue.ordinary_kernel(old,s,X,P) for s in order}
                    prefix = residue.word_product(kernels,order[:-1],P)
                    last = order[-1]
                    canceled = sum(prefix[0][b]*old[last][b][2]*source.inverse(values[last-1][b])
                                   for b in range(3)) % P
                    assert omega == canceled
                    diagonal = (1-omega*source.inverse(v)) % P
                    record.update(omega=omega,independent_last_transition_cancellation=canceled,
                                  predicted_matching_diagonal=diagonal)
                record['predicted_matching_diagonal_is_nonzero'] = bool(diagonal)
            records.append(record)
            by_label[t,a] = record
    units = all(record['all_other_old_lines_are_units'] for record in records)
    result = dict(observation='Restrict L_(t,a) h/mu to L_(t,a)=0 before evaluating at Q_(t,a), a=0,2; defined on the common axis kernel.',
                  mu='v X0 X2 / ((X0+v X2)(X0+2v X2))',
                  records=records,all_matching_denominator_conditions_hold=units)
    if units:
        # The actual M formula is checked against source words at ordinary
        # points below.  Compute its other-block residues using one singular
        # kernel replacement.  For state 2, the dual direction remains on
        # L_(u,2)=0; the output X2 factor is canceled before evaluation.
        labels = [(t,a) for t in range(1,q+1) for a in (0,2)]
        matrix = []
        for u,a in labels:
            rec,X = by_label[u,a],by_label[u,a]['point']
            row = []
            for t,b in labels:
                if t == u:
                    value = rec['predicted_matching_diagonal'] if b == a else 0
                else:
                    order = [s for s in range(1,q+1) if s != t]
                    if a == 0:
                        product = dual_word(old,order,X,(0,0,0),(u,a))
                        residue_H = -2*v*product[2][2][0] % P
                    else:
                        ut,vt = times[u-1]
                        product = dual_word(old,order,X,(0,-2*vt*source.inverse(3*ut),1),(u,a))
                        assert product[0][2][0] == 0
                        residue_H = (-product[2][2][0]-source.inverse(v)*product[0][2][1]) % P
                    factor = times[t-1][1] if b == 0 else 1
                    value = factor*residue_H*source.inverse(rec['old_line_values'][t-1][b]) % P
                row.append(value)
            matrix.append(row)
        assert all(matrix[i][j] == 0 for i in range(2*q) for j in range(2*q) if i != j)
        result.update(matching_row_and_column_labels=labels,actual_canceled_matching_matrix=matrix,
                      matching_certificate=incoming.matrix_certificate(matrix),
                      all_matching_diagonals_nonzero=all(matrix[i][i] for i in range(2*q)),
                      other_block_matching_residue_checks=2*q*(2*q-2))
    return result


def calculate_generic(case):
    """One prescribed alternative, with no parameter search or old-rank reuse."""
    started,n = time.monotonic(),case['m']
    q = n-1
    times = [(7**(t-1),3**(t-1)) for t in range(1,n)]+[(0,3**q)]
    tables = source.tables_at(times)
    inherited,_ = source.larger_columns(q)
    zero,_ = source.larger_columns(n)
    candidates = candidate_columns(n)
    inclusion = candidate_inclusion(n,candidates,zero)
    all_columns = inherited+candidates
    requested = case['ordinary_points']
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
    matrix,denominators = [],[]
    for X in points:
        evaluate,_,_,denom = source.evaluator(tables,X)
        matrix.append([row[2]*source.inverse(X[2]) % P for row in evaluate(all_columns)])
        denominators.append(denom)
    inherited_matrix = [row[:len(inherited)] for row in matrix]
    candidate_matrix = [row[len(inherited):] for row in matrix]
    old_certificate = incoming.matrix_certificate(inherited_matrix)
    certificate = incoming.matrix_certificate(matrix)
    old_rank = old_certificate['rank_certificate']['rank']
    rank = certificate['rank_certificate']['rank']
    gain,expected = rank-old_rank,6*q+3
    selected = certificate['rank_certificate']['nonzero_minor']
    minor = [[matrix[i][j] for j in selected['columns']] for i in selected['rows']]
    minor_certificate = incoming.matrix_certificate(minor)
    assert minor_certificate['rank_certificate']['determinant_mod_prime'] == selected['determinant_mod_prime']
    selected_new = [j-len(inherited) for j in selected['columns'] if j >= len(inherited)]
    if gain == expected:
        assert selected_new == list(range(expected))
    matching = matching_data(times)
    controls,formula_checks,append_checks = [],0,0
    old_tables = source.tables_at(times[:-1])
    for X in points[:3]:
        evaluate,_,product,denom = source.evaluator(tables,X)
        actual = evaluate(candidates)
        assert actual == direct_word_values(times,X,candidates)
        old_evaluate,_,_,_ = source.evaluator(old_tables,X)
        before,after = old_evaluate(inherited),evaluate(inherited)
        v = times[-1][1]
        ell,tilde = (X[0]+v*X[2]) % P,(X[0]+2*v*X[2]) % P
        mu = v*X[0]*X[2]*source.inverse(ell*tilde) % P
        assert all(new[2] == mu*old[2] % P for old,new in zip(before,after))
        append_checks += len(inherited)
        formula_values = []
        for j,c in enumerate(candidates):
            if c['label']['kind'] != 'M':
                continue
            t,a = c['label']['t'],c['label']['a']
            Q = product([s for s in range(1,q+1) if s != t])
            W = Q[0][2]*source.inverse(X[2]) % P
            H = (tilde*(1-Q[2][2])-X[0]*ell*source.inverse(v)*W) % P
            factor = times[t-1][1] if a == 0 else 1
            formula = mu*factor*H*source.inverse(denom[t-1][a]) % P
            h = actual[j][2]*source.inverse(X[2]) % P
            assert formula == h
            formula_values.append(dict(candidate_index=j,h=h,ZP46_value=formula))
            formula_checks += 1
        controls.append(dict(point=X,actual_vector_sha256=residue.matrix_hash(actual),
                             ZP46_actual_source_checks=formula_values))
    result = dict(fixture='Predetermined seven-power old u alternative; no parameter search.',n=n,q=q,prime=P,G=G,
                  time_factors=times,observation_points=points,observation_point_count=len(points),
                  requested_points_reference='source24-zero-prefix-extension-results.json: boundary_full_space_followup',
                  rejected_saved_observation_points=rejected,ordinary_denominators=denominators,
                  all_recorded_evaluation_denominators_are_units=True,
                  inherited_original_source_columns=inherited,candidate_original_source_columns=candidates,
                  candidate_terms_in_full_zero_prefix=inclusion,
                  exact_original_source_coefficient_inclusions_verified=True,
                  inherited_observation_certificate=old_certificate,actual_candidate_evaluation_matrix=candidate_matrix,
                  combined_column_order='All inherited original generators, followed by the listed 6q+3 candidates.',
                  combined_certificate=certificate,selected_joint_minor_matrix=minor,
                  selected_joint_minor_certificate=minor_certificate,selected_candidate_column_indices=selected_new,
                  inherited_observation_rank=old_rank,combined_observation_rank=rank,
                  observed_quotient_gain=gain,proposed_quotient_gain=expected,proposed_gain_attained=gain == expected,
                  matching=matching,actual_word_controls=controls,
                  independent_actual_word_component_checks=9*len(candidates),
                  actual_source_ZP46_checks=formula_checks,actual_inherited_scalar_append_checks=append_checks,
                  scope='Finite rank lower bounds at this one fixed alternative. The matching observations are used only on the joint axis kernel; no ranks of unrelated observation groups are added.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(fixture='seven-power',q=q,n=n,inherited_rank=old_rank,
                          combined_rank=rank,observed_gain=gain,proposed_gain=expected,
                          matching_units=matching['all_matching_denominator_conditions_hold'],
                          matching_rank=matching.get('matching_certificate',{}).get('rank_certificate',{}).get('rank'),
                          selected_joint_minor_determinant=selected['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def calculate(case):
    started,n = time.monotonic(),case['m']
    q = n-1
    times = case['special_time_factors']
    assert times == [[6**(t-1),3**(t-1)] for t in range(1,n)]+[[0,3**q]]
    assert case['prime'] == P and case['G'] == [list(row) for row in G]
    B0 = case['full_zero_prefix_matrix']
    B0cert = case['full_zero_prefix_certificate']
    assert residue.matrix_hash(B0) == B0cert['sha256']
    zero,_ = source.larger_columns(n)
    assert json.loads(json.dumps(zero)) == case['zero_prefix_columns']
    inherited,_ = source.larger_columns(q)
    lookup = {json.dumps(c,sort_keys=True):i for i,c in enumerate(zero)}
    inherited_ids = [lookup[json.dumps(c,sort_keys=True)] for c in inherited]
    assert inherited_ids == case['inherited_indices_in_full_zero_prefix']
    inherited_matrix = [[row[i] for i in inherited_ids] for row in B0]
    inherited_certificate = case['inherited_zero_prefix_certificate']
    assert residue.matrix_hash(inherited_matrix) == inherited_certificate['sha256']
    candidates = candidate_columns(n)
    inclusion = candidate_inclusion(n,candidates,zero)
    candidate_matrix = [source.combine_values(row,inclusion) for row in B0]
    combined = [old+new for old,new in zip(inherited_matrix,candidate_matrix)]
    certificate = incoming.matrix_certificate(combined)
    old_rank = inherited_certificate['rank_certificate']['rank']
    combined_rank = certificate['rank_certificate']['rank']
    gain = combined_rank-old_rank
    expected_gain = 6*q+3
    passed = gain == expected_gain
    selected_minor = certificate['rank_certificate']['nonzero_minor']
    selected_new = [j-len(inherited) for j in selected_minor['columns'] if j >= len(inherited)]
    if passed:
        assert selected_new == list(range(expected_gain))
    minor_matrix = [[combined[i][j] for j in selected_minor['columns']] for i in selected_minor['rows']]
    # The saved certificate's minor has its explicit pivot row order.
    minor_certificate = incoming.matrix_certificate(minor_matrix)
    assert minor_certificate['rank_certificate']['determinant_mod_prime'] == selected_minor['determinant_mod_prime']
    assert all(value for row in case['ordinary_denominators'] for line in row for value in line)
    assert all(X[2] % P for X in case['ordinary_points'])
    tables = source.tables_at(times)
    controls,component_checks = [],0
    points = [(X,i) for i,X in enumerate(case['ordinary_points'][:3])]
    points += [(X,None) for X in ((1,2,3),(2,3,5),(3,5,7))]
    for X,saved_row in points:
        evaluate,_,_,denominators = source.evaluator(tables,X)
        actual = evaluate(candidates)
        direct = direct_word_values(times,X,candidates)
        assert actual == direct
        component_checks += 3*len(candidates)
        h = [row[2]*source.inverse(X[2]) % P for row in actual]
        if saved_row is not None:
            assert h == candidate_matrix[saved_row]
        else:
            zero_h = [row[2]*source.inverse(X[2]) % P for row in evaluate(zero)]
            assert h == source.combine_values(zero_h,inclusion)
        controls.append(dict(point=X,saved_observation_row=saved_row,denominators=denominators,
                             actual_candidate_h=h,actual_vector_sha256=residue.matrix_hash(actual)))
    result = dict(n=n,q=q,prime=P,G=G,time_factors=times,
                  saved_result_reference='source24-zero-prefix-extension-results.json: boundary_full_space_followup',
                  saved_full_zero_prefix_matrix_sha256=B0cert['sha256'],
                  observation_points=case['ordinary_points'],observation_point_count=len(B0),
                  all_recorded_evaluation_denominators_are_units=True,
                  inherited_original_source_columns=inherited,
                  inherited_indices_in_full_zero_prefix=inherited_ids,
                  inherited_observation_certificate=inherited_certificate,
                  candidate_original_source_columns=candidates,candidate_terms_in_full_zero_prefix=inclusion,
                  exact_original_source_coefficient_inclusions_verified=True,
                  actual_candidate_evaluation_matrix=candidate_matrix,
                  combined_column_order='All inherited original generators, followed by the listed 6q+3 candidates.',
                  combined_certificate=certificate,
                  selected_joint_minor_matrix=minor_matrix,selected_joint_minor_certificate=minor_certificate,
                  selected_candidate_column_indices=selected_new,
                  inherited_observation_rank=old_rank,combined_observation_rank=combined_rank,
                  observed_quotient_gain=gain,proposed_quotient_gain=expected_gain,
                  proposed_gain_attained=passed,
                  independent_actual_word_component_checks=component_checks,
                  actual_word_controls=controls,
                  scope='Full observed gain gives a finite independence certificate modulo all inherited generators. Failure to attain it on these rows alone is not a generic or rational-function upper-bound conclusion.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(q=q,n=n,inherited_rank=old_rank,candidate_columns=expected_gain,
                          combined_rank=combined_rank,observed_gain=gain,proposed_gain_attained=passed,
                          selected_joint_minor_determinant=selected_minor['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--generic-alternative',action='store_true',
                        help='Preserve the original saved run and add only the fixed seven-power follow-up.')
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-zero-prefix-extension-results.json').read_text())
    previous = None
    if args.generic_alternative:
        assert args.output and args.output.is_file(), 'The follow-up must preserve an existing original result.'
        previous = json.loads(args.output.read_text())
    started,cases,limitation = time.monotonic(),[],None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for n in (3,4,5,6):
            case = next(c for c in saved['boundary_full_space_followup']['cases'] if c['m'] == n)
            if args.generic_alternative:
                original = next(c for c in previous['cases'] if c['n'] == n)
                original['matching_geometry_followup'] = matching_data(original['time_factors'])
                original['fixture_diagnosis'] = 'The six-power old u fixture violates matching denominator conditions; its recorded rank deficits are retained and are not a generic refutation.'
                cases.append(calculate_generic(case))
            else:
                cases.append(calculate(case))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Finite actual-source verification of the proposed 6q+3 boundary extension.',
                  scope='Only q=2,3,4,5 at the recorded common-G boundary fixtures; no all-q extension or resulting all-length lower bound is asserted.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.generic_alternative:
        previous['predetermined_generic_alternative_followup'] = result
        result = previous
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    statistics = result['predetermined_generic_alternative_followup'] if args.generic_alternative else result
    print(json.dumps({key:statistics[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
