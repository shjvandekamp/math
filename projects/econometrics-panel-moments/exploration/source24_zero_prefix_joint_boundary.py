#!/usr/bin/env python3
"""Coupled boundary scalar-kernel restriction and first splitting jet.

At the three saved six-power boundary fixtures n=4,5,6, evaluate
B_w(R)=-D_n R_1/(w X_1 X_2) on X_0=-w X_2, with the fixed w=5.
Apply the saved systematic kernel in ORIGINAL source coordinates before
interpolating or ranking.  Every boundary B_w has the X_2^2 factor from
ZP51, so its X_2=1 chart has degree at most 3(n-1).  Extra evaluations
control this interpolation; they are not the proof of its degree bound.
The later ZP53 scalar-kernel argument improves the factor to X_2^3.
--verify-kernel-endpoint checks the resulting zero highest coefficient
directly in the saved matrices, without repeating the original ranks.

The optional-looking joint comparison is cheap here: the already saved
first splitting jet is reconstructed on exactly the same kernel basis.
Rank its vertical stack with B_w rather than adding separate ranks.
No matching-point conditions or all-length rank claims are used.
"""

import argparse
import json
from pathlib import Path
import random
import signal
import time

import source24_zero_prefix_split_jet as split


source = split.source
P, G = source.P, source.G
incoming, residue, schur = source.incoming, source.residue, source.schur
HERE = Path(__file__).resolve().parent


def cleared_component_values(times,X,columns,output=1):
    """D_n R_output from polynomial kernel numerators, using no inverses."""
    n,tables = len(times),source.tables_at(times)
    lines = {t:[residue.dot(row,X,P) for row in table] for t,table in tables.items()}
    block_D = {t:L[0]*L[1]*L[2] % P for t,L in lines.items()}
    total_D = 1
    for value in block_D.values():
        total_D = total_D*value % P
    cleared = {t:[[table[a][b]*X[b]*lines[t][(a+1)%3]*lines[t][(a+2)%3] % P
                   for b in range(3)] for a in range(3)] for t,table in tables.items()}
    products,primitives = {},{}

    def product(order):
        key = tuple(order)
        if key not in products:
            products[key] = residue.word_product(cleared,order,P)
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,t,a = key
                value = X[a]*(total_D*int(a == output)-product(source.word(n,t))[a][output])
            else:
                _,t,s,a,b = key
                tail_D = 1
                for u,D in block_D.items():
                    if u != t:
                        tail_D = tail_D*D % P
                tail = product(source.word(n,s,t))[b][output]
                value = X[a]*cleared[t][a][b]*(tail_D*int(b == output)-tail)
            primitives[key] = value % P
        return primitives[key]

    values = [sum(coefficient*primitive(key) for coefficient,key in c['terms']) % P for c in columns]
    return values,total_D


def observation_points(times,w,target):
    tables = source.tables_at(times)

    def permitted(x):
        return x != 0 and all(residue.dot(row,(-w,x,1),P)
                              for table in tables.values() for row in table)

    xs,rejected,x = [],[],0
    while len(xs) < target:
        x += 1
        if permitted(x):
            xs.append(x)
        else:
            rejected.append(x)
    rng = random.Random(380024+len(times))
    while len(xs) < target+6:
        x = rng.randrange(1,P)
        if x not in xs and permitted(x):
            xs.append(x)
    return xs,rejected


def mixed_minor(B0,boundary_certificate,pivots,observations,image,image_certificate):
    """One block minor after the SAME invertible source-column change."""
    old = boundary_certificate['rank_certificate']['nonzero_minor']
    new = image_certificate['rank_certificate']['nonzero_minor']
    assert old['columns'] == pivots
    br,nr,nc = old['rows'],new['rows'],new['columns']
    upper = [[B0[i][j] for j in pivots]+[0]*len(nc) for i in br]
    lower = [[observations[i][j] for j in pivots]+[image[i][j] for j in nc] for i in nr]
    matrix = upper+lower
    certificate = incoming.matrix_certificate(matrix)
    expected = old['determinant_mod_prime']*new['determinant_mod_prime'] % P
    assert certificate['rank_certificate']['determinant_mod_prime'] == expected
    assert certificate['rank_certificate']['rank'] == len(pivots)+image_certificate['rank_certificate']['rank']
    return dict(boundary_rows=br,source_pivot_columns=pivots,
                image_rows=nr,original_kernel_vector_indices=nc,
                transformed_joint_minor_matrix=matrix,certificate=certificate,
                determinant_equals_boundary_minor_times_induced_minor=True)


def verify_kernel_endpoint(case):
    """A follow-up to the observed deficit, preserving the original bound."""
    q = case['q']
    coefficients = case['B_w_coefficient_matrix_on_original_kernel']
    assert len(coefficients) == 3*q+1
    assert residue.matrix_hash(coefficients) == case['B_w_certificate']['sha256']
    assert case['interpolation_monomials'][-1] == 'x^'+str(3*q)
    assert not any(coefficients[-1])
    case['sharper_kernel_endpoint_followup'] = dict(
        status='Checked after the original one-dimensional deficit was observed; not an anticipated target in that run.',
        paper_reference='SOURCE24_ZERO_PREFIX_EXTENSION.md ZP53',
        unrestricted_boundary_target_dimension=3*q+1,
        scalar_kernel_target_dimension=3*q,
        scalar_kernel_chart_degree_bound=3*q-1,
        verified_zero_coefficient_power=3*q,
        verified_zero_coefficient_row=coefficients[-1],
        saved_coefficient_matrix_sha256=case['B_w_certificate']['sha256'],
        observed_rank_attains_sharper_target=case['B_w_kernel_rank'] == 3*q,
        justification='On X=(-w*z,1,z), every boundary row has constant term kappa*(k-e1), k=(-w,0,v)/(v-w). The actual scalar-kernel condition R2=0 forces kappa=0, hence R1=O(z), and B_w has the additional X2 factor. This paper argument supplies the uniform bound; this check verifies its endpoint in the recorded matrices.')


def calculate(case,jetcase,w=5):
    started,n = time.monotonic(),case['m']
    q,target = n-1,3*(n-1)+1
    times,B0 = case['special_time_factors'],case['full_zero_prefix_matrix']
    assert times == [[6**(t-1),3**(t-1)] for t in range(1,n)]+[[0,3**q]]
    assert case['prime'] == P and case['G'] == [list(row) for row in G]
    assert w not in (0,times[-1][1] % P,2*times[-1][1] % P)
    columns,_ = source.larger_columns(n)
    assert json.loads(json.dumps(columns)) == case['zero_prefix_columns'] == jetcase['original_source_columns']
    boundary_certificate = case['full_zero_prefix_certificate']
    boundary_hash = residue.matrix_hash(B0)
    assert boundary_hash == boundary_certificate['sha256'] == jetcase['saved_boundary_matrix_sha256']
    geometry = split.field_geometry(times)
    pivots,free,kernel = (jetcase[key] for key in
                          ('boundary_pivot_columns','boundary_free_columns','original_source_kernel_basis'))
    assert len(pivots) == geometry['boundary_ambient_dimension'] == boundary_certificate['rank_certificate']['rank']
    assert len(kernel) == len(free) == len(columns)-len(pivots)
    assert pivots == boundary_certificate['rank_certificate']['nonzero_minor']['columns']
    assert sorted(pivots+free) == list(range(len(columns)))
    assert all(vector[j] == int(i == k) for i,vector in enumerate(kernel) for k,j in enumerate(free))
    kernel_hash = residue.matrix_hash(kernel)
    assert kernel_hash == jetcase['original_source_kernel_basis_sha256']
    K = split.transpose(kernel)
    assert not any(value for row in schur.matrix_product(B0,K) for value in row)

    xs,rejected = observation_points(times,w,target)
    tables = source.tables_at(times)
    rows,point_controls = [],[]
    polynomial_checks = 0
    for i,x in enumerate(xs):
        X = (-w % P,x,1)
        evaluate,_,_,denominators = source.evaluator(tables,X)
        actual = evaluate(columns)
        D = 1
        for line in denominators:
            for value in line:
                D = D*value % P
        factor = -D*source.inverse(w*x) % P
        rows.append([factor*R[1] % P for R in actual])
        if i in (0,1,target,len(xs)-1):
            polynomial,polynomial_D = cleared_component_values(times,X,columns)
            assert D == polynomial_D
            assert polynomial == [D*R[1] % P for R in actual]
            polynomial_checks += len(columns)
        point_controls.append(dict(point=X,all_actual_line_denominators=denominators,
                                   D_n=D,B_w_scalar_factor=factor))
    # Restrict before fitting or computing rank; source coefficients stay fixed.
    restricted = schur.matrix_product(rows,K)
    vandermonde = [[pow(x,k,P) for k in range(target)] for x in xs[:target]]
    inverse,Vcertificate = schur.invert(vandermonde)
    observations = schur.matrix_product(inverse,rows[:target])
    coefficients = schur.matrix_product(inverse,restricted[:target])
    assert schur.matrix_product(observations,K) == coefficients
    for x,row in zip(xs[target:],restricted[target:]):
        predicted = schur.matrix_product([[pow(x,k,P) for k in range(target)]],coefficients)[0]
        assert predicted == row
    body_certificate = incoming.matrix_certificate(coefficients)
    body_rank = body_certificate['rank_certificate']['rank']
    body_mixed = mixed_minor(B0,boundary_certificate,pivots,observations,coefficients,body_certificate)

    # Reconstruct the saved Theta observation rows, not a separately chosen
    # kernel or quotient, and check their product with precisely this K.
    theta_xs = jetcase['trace_x_values']
    theta_target = 3*q
    theta_rows = [[value*source.inverse(x*x) % P for value in row]
                  for x,row in zip(theta_xs,jetcase['actual_cleared_derivative_observation_matrix'])]
    theta_V = [[pow(x,k,P) for k in range(theta_target)] for x in theta_xs[:theta_target]]
    theta_inverse,_ = schur.invert(theta_V)
    theta_observations = schur.matrix_product(theta_inverse,theta_rows[:theta_target])
    theta = schur.matrix_product(theta_observations,K)
    assert theta == jetcase['theta_coefficient_matrix']
    assert residue.matrix_hash(theta) == jetcase['theta_certificate']['sha256']
    theta_controls = []
    for i in (0,len(theta_xs)-1):
        X = (-times[-1][1] % P,theta_xs[i],1)
        direct,_ = split.cleared_derivative_values(times,X,columns)
        assert direct == jetcase['actual_cleared_derivative_observation_matrix'][i]
        theta_controls.append(dict(point=X,actual_cleared_derivative_row_sha256=residue.matrix_hash([direct])))
    joint = coefficients+theta
    joint_observations = observations+theta_observations
    joint_certificate = incoming.matrix_certificate(joint)
    joint_rank = joint_certificate['rank_certificate']['rank']
    joint_mixed = mixed_minor(B0,boundary_certificate,pivots,joint_observations,joint,joint_certificate)

    v = times[-1][1]
    boundary_factor = (v-w)**2*(2*v-w) % P
    # Along X=(-w*y,1,y), the new K is this constant matrix and its
    # block determinant is boundary_factor*y^3.  Every actual source R1
    # is regular at y=0 (all old denominators there are units), so B_w
    # has y^2 as an exact factor, independently of the kernel restriction.
    constant_new_K = [[-w*source.inverse(G[a][2]*v-w) % P,0,
                       G[a][2]*v*source.inverse(G[a][2]*v-w) % P] for a in range(3)]
    old_axis_units = [[row[1] for row in table] for table in source.tables_at(times[:-1]).values()]
    assert boundary_factor and all(value for row in old_axis_units for value in row)
    for y in (1,2):
        X = (-w*y % P,1,y)
        assert residue.ordinary_kernel(tables,n,X,P) == constant_new_K
        new_D = 1
        for row in tables[n]:
            new_D = new_D*residue.dot(row,X,P) % P
        assert new_D == boundary_factor*pow(y,3,P) % P
    boundary_rank = len(pivots)
    theta_rank = jetcase['theta_certificate']['rank_certificate']['rank']
    result = dict(n=n,q=q,prime=P,G=G,time_factors=times,w=w,field_geometry=geometry,
                  boundary_ambient_saturation_verified=True,matching_conditions_required=False,
                  original_source_columns=columns,
                  saved_boundary_reference='source24-zero-prefix-extension-results.json: boundary_full_space_followup',
                  saved_boundary_matrix_sha256=boundary_hash,saved_boundary_point_count=len(B0),
                  saved_kernel_reference='source24-zero-prefix-split-jet-results.json: original_source_kernel_basis',
                  saved_original_source_kernel_basis_sha256=kernel_hash,
                  boundary_pivot_columns=pivots,boundary_free_columns=free,
                  boundary_rank=boundary_rank,kernel_dimension=len(kernel),
                  systematic_free_coordinates_and_exact_boundary_kernel_verified=True,
                  observation_definition='B_w=-D_n R1/(w X1 X2), evaluated on X0=-w X2; source vectors retain all original coefficient couplings.',
                  degree_bound=3*q,full_binary_target_dimension=3*q+3,
                  boundary_divisibility_target_dimension=target,
                  boundary_X2_squared_factor=dict(new_D_coefficient=boundary_factor,
                      constant_new_K_on_auxiliary_line=constant_new_K,old_line_values_at_e1=old_axis_units,
                      reason='The new block D contributes y^3 on X=(-w*y,1,y); actual R1 is regular there, and division by y leaves y^2. Paper ZP51.'),
                  observation_x_values=xs,rejected_initial_x_values=rejected,point_controls=point_controls,
                  actual_B_w_observation_matrix=rows,B_w_after_original_kernel=restricted,
                  interpolation_monomials=['x^'+str(k) for k in range(target)],
                  interpolation_inverse_certificate=Vcertificate,
                  B_w_coefficient_observations_on_original_columns=observations,
                  B_w_coefficient_matrix_on_original_kernel=coefficients,B_w_certificate=body_certificate,
                  extra_interpolation_points=len(xs)-target,all_extra_interpolation_values_match=True,
                  degree_justification='Exact X2^2 boundary factor and homogeneous degree 3n-1; extra finite evaluations are only controls.',
                  independent_denominator_free_cleared_component_checks=polynomial_checks,
                  boundary_plus_B_w=body_mixed,
                  saved_theta_coefficient_matrix_sha256=jetcase['theta_certificate']['sha256'],
                  theta_coefficient_observations_on_same_original_columns=theta_observations,
                  actual_saved_theta_row_controls=theta_controls,
                  combined_kernel_row_labels=[dict(channel='B_w',power=k) for k in range(target)]+
                      [dict(channel='Theta',power=k) for k in range(theta_target)],
                  combined_B_w_Theta_on_same_kernel=joint,combined_kernel_certificate=joint_certificate,
                  boundary_plus_B_w_plus_Theta=joint_mixed,
                  B_w_kernel_rank=body_rank,Theta_kernel_rank=theta_rank,
                  combined_kernel_rank=joint_rank,Theta_gain_after_B_w=joint_rank-body_rank,
                  overlap_dimension_of_row_spaces=body_rank+theta_rank-joint_rank,
                  boundary_plus_B_w_rank=boundary_rank+body_rank,
                  boundary_plus_B_w_plus_Theta_rank=boundary_rank+joint_rank,
                  scope='Only these three exact finite-field fixtures. The stack is ranked on one common source kernel; no separate ranks are added and no higher-jet or uniform claim is made.',
                  elapsed_seconds=time.monotonic()-started)
    verify_kernel_endpoint(result)
    print(json.dumps(dict(n=n,boundary_rank=boundary_rank,B_w_kernel_rank=body_rank,
                          B_w_target=target,boundary_plus_B_w_rank=boundary_rank+body_rank,
                          Theta_rank=theta_rank,combined_kernel_rank=joint_rank,
                          Theta_gain_after_B_w=joint_rank-body_rank,
                          overlap=body_rank+theta_rank-joint_rank,
                          boundary_plus_both_rank=boundary_rank+joint_rank,
                          B_w_mixed_determinant=body_mixed['certificate']['rank_certificate']['determinant_mod_prime'],
                          joint_mixed_determinant=joint_mixed['certificate']['rank_certificate']['determinant_mod_prime'],
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--verify-kernel-endpoint',action='store_true',
                        help='Check the sharper kernel endpoint in an existing result; preserve its original run and ranks.')
    args = parser.parse_args()
    if args.verify_kernel_endpoint:
        assert args.output and args.output.is_file()
        started = time.monotonic()
        result = json.loads(args.output.read_text())
        for case in result['cases']:
            verify_kernel_endpoint(case)
            assert time.monotonic()-started < 28 and incoming.maximum_rss_bytes() < 95*1024**2
        result['kernel_endpoint_followup'] = dict(
            operation='Verified saved coefficient hashes and the zero x^(3q) row only; no evaluations, interpolation, or ranks rerun.',
            checked_lengths=[case['n'] for case in result['cases']],
            elapsed_seconds=time.monotonic()-started,
            maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=None)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result['kernel_endpoint_followup']),flush=True)
        return
    saved = json.loads((HERE/'source24-zero-prefix-extension-results.json').read_text())
    keys = ('m','prime','G','special_time_factors','zero_prefix_columns',
            'full_zero_prefix_matrix','full_zero_prefix_certificate')
    boundary = {case['m']:{key:case[key] for key in keys}
                for case in saved['boundary_full_space_followup']['cases'] if case['m'] in (4,5,6)}
    del saved
    saved_jets = json.loads((HERE/'source24-zero-prefix-split-jet-results.json').read_text())
    keys = ('n','original_source_columns','boundary_pivot_columns','boundary_free_columns',
            'original_source_kernel_basis','original_source_kernel_basis_sha256',
            'saved_boundary_matrix_sha256','trace_x_values',
            'actual_cleared_derivative_observation_matrix','theta_coefficient_matrix','theta_certificate')
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
            cases.append(calculate(boundary[n],jets[n]))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Actual boundary scalar-kernel restriction and coupled first splitting jet.',
                  scope='n=4,5,6 at the saved six-power boundary fixtures, w=5, prime 1000003. No new parameter scan, higher jet, matching assumption, or uniform rank theorem.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
