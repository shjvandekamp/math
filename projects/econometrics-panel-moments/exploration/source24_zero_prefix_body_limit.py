#!/usr/bin/env python3
"""Finite pole-limit test of the boundary scalar-kernel body map.

Use only the saved n=4,5,6 six-power boundary fixtures.  On X=(-1,y,delta),
the old line (t,a) has y=(1-G[a,2] v_t delta)/(G[a,1] u_t).  Take the
constant coefficient of L_(t,a) R1/(X0 X1) for a=0,1.  For a=2 its
constant coefficient vanishes; divide by delta and take the constant,
using the exact dual coordinate direction along the old line.

All observations are applied to the SAME saved original-source scalar
kernel before ranking.  Actual primitive residues use one rank-one
kernel replacement.  Independent polynomial-cleared word products check
both constant and first-order residue coefficients without pole division.
No all-q body-rank or induction statement is inferred from these cases.
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_zero_prefix_boundary_extension as boundary
import source24_zero_prefix_split_jet as split


source = split.source
P, G = source.P, source.G
incoming, residue, schur, dual = source.incoming, source.residue, source.schur, source.dual
HERE = Path(__file__).resolve().parent


def coordinates_for_line(times,t,a):
    u,v = times[t-1]
    inverse_slope = source.inverse(G[a][1]*u)
    return (-1 % P,inverse_slope,0),(0,-G[a][2]*v*inverse_slope % P,1)


def actual_residue_values(times,t,a,columns):
    """Actual L_(t,a) R1 jets, restricted to that line before evaluation."""
    n,tables = len(times),source.tables_at(times)
    X,dX = coordinates_for_line(times,t,a)
    coords = [(x,dx) for x,dx in zip(X,dX)]
    line_jets = [[(residue.dot(row,X,P),residue.dot(row,dX,P)) for row in table]
                 for table in tables.values()]
    assert line_jets[t-1][a] == dual.ZERO
    assert all(value[0] for s,line in enumerate(line_jets,start=1)
               for b,value in enumerate(line) if (s,b) != (t,a))
    products,primitives,prefixes = {},{},{}

    def product(order,with_residue):
        key = tuple(order),with_residue
        if key not in products:
            products[key] = boundary.dual_word(tables,order,X,dX,(t,a) if with_residue else None)
        return products[key]

    def prefix(s,c,b):
        key = s,c,b
        if key not in prefixes:
            assert s != t
            numerator = dual.scale(tables[s][c][b],coords[b])
            prefixes[key] = dual.mul(numerator,dual.inverse(line_jets[s-1][c]))
        return prefixes[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,s,c = key
                value = dual.scale(-1,dual.mul(coords[c],product(source.word(n,s),True)[c][1]))
            else:
                _,s,first,c,b = key
                order = source.word(n,first,s)
                if s == t:
                    if c != a:
                        value = dual.ZERO
                    else:
                        departure = dual.scale(tables[t][a][b],coords[b])
                        tail = dual.sub(dual.ONE if b == 1 else dual.ZERO,product(order,False)[b][1])
                        value = dual.mul(coords[a],dual.mul(departure,tail))
                else:
                    value = dual.scale(-1,dual.mul(coords[c],dual.mul(prefix(s,c,b),product(order,True)[b][1])))
            primitives[key] = value
        return primitives[key]

    values = []
    for column in columns:
        value = dual.ZERO
        for coefficient,key in column['terms']:
            value = dual.add(value,dual.scale(coefficient,primitive(key)))
        values.append(value)
    denominator = dual.mul(coords[0],coords[1])
    f_values = [dual.mul(value,dual.inverse(denominator)) for value in values]
    if a == 2:
        assert all(value[0] == 0 for value in values)
        assert all(value[1] == original[1]*source.inverse(X[0]*X[1]) % P
                   for value,original in zip(f_values,values))
    observation = [value[int(a == 2)] for value in f_values]
    return observation,values,dict(point=X,delta_direction=dX,all_line_jets=line_jets,
                                   coordinate_denominator_jet=denominator,
                                   all_other_line_denominators_are_units=True,
                                   matched_line_vanishes_to_both_orders=True,
                                   state_two_constant_residues_vanish=(True if a == 2 else None))


def polynomial_residue_control(times,t,a,columns):
    """Evaluate D_n R1 in dual polynomial arithmetic, then divide D_n/L_ta."""
    n,tables = len(times),source.tables_at(times)
    X,dX = coordinates_for_line(times,t,a)
    coords = [(x,dx) for x,dx in zip(X,dX)]
    numerators = {s:[[dual.scale(row[b],coords[b]) for b in range(3)] for row in table]
                  for s,table in tables.items()}
    lines = {s:[tuple(sum(entry[k] for entry in row) % P for k in (0,1)) for row in matrix]
             for s,matrix in numerators.items()}
    assert lines[t][a] == dual.ZERO
    block_D = {s:dual.mul(dual.mul(line[0],line[1]),line[2]) for s,line in lines.items()}
    total_D,other_D = dual.ONE,dual.ONE
    for s,line in lines.items():
        for b,value in enumerate(line):
            total_D = dual.mul(total_D,value)
            if (s,b) != (t,a):
                other_D = dual.mul(other_D,value)
    assert total_D == dual.ZERO and other_D[0]
    cleared = {s:[[dual.mul(matrix[c][b],dual.mul(lines[s][(c+1)%3],lines[s][(c+2)%3]))
                    for b in range(3)] for c in range(3)] for s,matrix in numerators.items()}
    products,primitives = {},{}

    def product(order):
        key = tuple(order)
        if key not in products:
            result = dual.identity()
            for s in order:
                result = dual.mmul(result,cleared[s])
            products[key] = result
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,s,c = key
                value = dual.mul(coords[c],dual.sub(dual.scale(int(c == 1),total_D),product(source.word(n,s))[c][1]))
            else:
                _,s,first,c,b = key
                tail_D = dual.ONE
                for u,D in block_D.items():
                    if u != s:
                        tail_D = dual.mul(tail_D,D)
                tail = dual.sub(dual.scale(int(b == 1),tail_D),product(source.word(n,first,s))[b][1])
                value = dual.mul(coords[c],dual.mul(cleared[s][c][b],tail))
            primitives[key] = value
        return primitives[key]

    result = []
    for column in columns:
        value = dual.ZERO
        for coefficient,key in column['terms']:
            value = dual.add(value,dual.scale(coefficient,primitive(key)))
        result.append(dual.mul(value,dual.inverse(other_D)))
    return result,other_D


def calculate(case,jetcase):
    started,n = time.monotonic(),case['m']
    q = n-1
    times,B0 = case['special_time_factors'],case['full_zero_prefix_matrix']
    assert times == [[6**(s-1),3**(s-1)] for s in range(1,n)]+[[0,3**q]]
    assert case['prime'] == P and case['G'] == [list(row) for row in G]
    columns,_ = source.larger_columns(n)
    assert json.loads(json.dumps(columns)) == case['zero_prefix_columns'] == jetcase['original_source_columns']
    certificate = case['full_zero_prefix_certificate']
    matrix_hash = residue.matrix_hash(B0)
    assert matrix_hash == certificate['sha256'] == jetcase['saved_boundary_matrix_sha256']
    geometry = split.field_geometry(times)
    pivots,free,kernel = (jetcase[key] for key in
                          ('boundary_pivot_columns','boundary_free_columns','original_source_kernel_basis'))
    assert len(pivots) == certificate['rank_certificate']['rank'] == geometry['boundary_ambient_dimension']
    assert pivots == certificate['rank_certificate']['nonzero_minor']['columns']
    assert len(kernel) == len(free) == len(columns)-len(pivots)
    assert sorted(pivots+free) == list(range(len(columns)))
    assert all(vector[j] == int(i == k) for i,vector in enumerate(kernel) for k,j in enumerate(free))
    kernel_hash = residue.matrix_hash(kernel)
    assert kernel_hash == jetcase['original_source_kernel_basis_sha256']
    K = split.transpose(kernel)
    assert not any(x for row in schur.matrix_product(B0,K) for x in row)

    labels = [dict(old_block=t,state=a,coefficient='delta^0')
              for t in range(1,q+1) for a in (0,1)]
    labels += [dict(old_block=t,state=2,coefficient='delta^1 after the proven zero constant term')
               for t in range(1,q+1)]
    observations,controls = [],[]
    independent_checks = 0
    for label in labels:
        t,a = label['old_block'],label['state']
        row,actual,control = actual_residue_values(times,t,a,columns)
        observations.append(row)
        if (t,a) in ((1,0),(q,1),(1,2),(q,2)):
            cleared,other_D = polynomial_residue_control(times,t,a,columns)
            assert actual == cleared
            control['independent_polynomial_residue_control'] = dict(
                D_n_over_matched_line_jet=other_D,
                both_orders_equal_for_every_original_source_column=True,
                residue_constant_and_derivative_sha256=residue.matrix_hash([list(value) for value in actual]))
            independent_checks += 2*len(columns)
        controls.append(dict(**label,**control))
    image = schur.matrix_product(observations,K)
    first = incoming.matrix_certificate(image[:2*q])
    full = incoming.matrix_certificate(image)
    first_rank,rank = first['rank_certificate']['rank'],full['rank_certificate']['rank']
    minor = full['rank_certificate']['nonzero_minor']
    selected = [[image[i][j] for j in minor['columns']] for i in minor['rows']]
    selected_certificate = incoming.matrix_certificate(selected)
    assert selected_certificate['rank_certificate']['determinant_mod_prime'] == minor['determinant_mod_prime']
    result = dict(n=n,q=q,prime=P,G=G,time_factors=times,
                  field_geometry=geometry,boundary_ambient_saturation_verified=True,
                  original_source_columns=columns,
                  saved_boundary_reference='source24-zero-prefix-extension-results.json: boundary_full_space_followup',
                  saved_boundary_matrix_sha256=matrix_hash,
                  saved_kernel_reference='source24-zero-prefix-split-jet-results.json: original_source_kernel_basis',
                  saved_original_source_kernel_basis_sha256=kernel_hash,
                  boundary_pivot_columns=pivots,boundary_free_columns=free,
                  boundary_rank=len(pivots),kernel_dimension=len(kernel),
                  systematic_free_coordinates_and_exact_boundary_kernel_verified=True,
                  observation_definition='L_(t,a) f at y=(1-G[a,2] v_t delta)/(G[a,1] u_t), f=R1/(X0 X1), X=(-1,y,delta). Constants for states 0/1; first delta coefficient for state 2.',
                  state_two_sign_convention='The stored row is +d_delta Res(R1)/(X0 X1), the negative of the b-matching convention; no additional sign is applied.',
                  row_labels=labels,point_controls=controls,
                  actual_residue_limit_observations_in_original_source_coordinates=observations,
                  residue_limit_matrix_on_same_original_scalar_kernel=image,
                  first_two_states_certificate=first,full_certificate=full,
                  first_two_states_rank=first_rank,state_two_added_gain=rank-first_rank,
                  full_rank=rank,target_rank=3*q,target_attained=rank == 3*q,
                  selected_minor_matrix=selected,selected_minor_certificate=selected_certificate,
                  selected_original_source_kernel_vectors=[kernel[j] for j in minor['columns']],
                  independent_polynomial_constant_and_first_order_component_checks=independent_checks,
                  scope='Only the three recorded finite-field fixtures. Every row uses the same actual scalar kernel. A deficient limit need not imply failure of the body map at finite auxiliary w; no all-q assertion is made.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(n=n,q=q,kernel_dimension=len(kernel),first_two_states_rank=first_rank,
                          state_two_added_gain=rank-first_rank,full_rank=rank,target=3*q,
                          target_attained=rank == 3*q,
                          selected_minor_determinant=minor['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-zero-prefix-extension-results.json').read_text())
    keys = ('m','prime','G','special_time_factors','zero_prefix_columns',
            'full_zero_prefix_matrix','full_zero_prefix_certificate')
    boundary_cases = {case['m']:{key:case[key] for key in keys}
                      for case in saved['boundary_full_space_followup']['cases'] if case['m'] in (4,5,6)}
    del saved
    saved_jets = json.loads((HERE/'source24-zero-prefix-split-jet-results.json').read_text())
    keys = ('n','original_source_columns','boundary_pivot_columns','boundary_free_columns',
            'original_source_kernel_basis','original_source_kernel_basis_sha256','saved_boundary_matrix_sha256')
    jets = {case['n']:{key:case[key] for key in keys} for case in saved_jets['cases']}
    del saved_jets
    started,cases,limitation = time.monotonic(),[],None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for n in (4,5,6):
            cases.append(calculate(boundary_cases[n],jets[n]))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Actual scalar-kernel body pole limit at the three saved boundary fixtures.',
                  scope='n=4,5,6, six-power old u and three-power v, new u=0, prime 1000003. Finite checks only; no new parameter scan or uniform body theorem.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
