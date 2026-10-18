#!/usr/bin/env python3
"""Actual first splitting jet on the saved zero-prefix boundary kernel.

Only n=4,5,6 and the saved G*/time fixtures are used.  Boundary kernel
vectors are systematic vectors in ORIGINAL source coordinates.  Differentiate
p=D_n h with respect to u_n at zero, restrict to ell=X0+v_n X2=0, and
apply those kernel vectors before ranking.  The induced trace is divided by
X1^2 and interpolated as degree <=3q-1 on X2=1; independent extra points
check the interpolation.  The degree justification is the paper ZP35--36,
not a conclusion inferred solely from those point checks.

Old kernels on ell are ordinary.  The new block is never inverted there:
the derivative of its polynomial-cleared kernel is inserted into the actual
word.  An independent rational dual-u implementation checks generic points
where the new denominators are units.  The full saved boundary matrices are
referenced by verified hashes rather than duplicated in this result.
"""

import argparse
import json
from pathlib import Path
import random
import signal
import time

import source24_zero_prefix_extension as source


P, G = source.P, source.G
incoming, residue, schur, dual = source.incoming, source.residue, source.schur, source.dual
HERE = Path(__file__).resolve().parent


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def select(matrix, indices):
    return [[row[j] for j in indices] for row in matrix]


def monomials(degree):
    return [(a,b,degree-a-b) for a in range(degree+1) for b in range(degree-a+1)]


def monomial_value(exponent, X):
    value = 1
    for x,k in zip(X,exponent):
        value = value*pow(x,k,P) % P
    return value


def derivative_value(exponent, X, tangent):
    value = 0
    for i,k in enumerate(exponent):
        if k:
            smaller = list(exponent)
            smaller[i] -= 1
            value += k*tangent[i]*monomial_value(smaller,X)
    return value % P


def canonical_point(X):
    pivot = next(x % P for x in X if x % P)
    return tuple(x*source.inverse(pivot) % P for x in X)


def field_geometry(times):
    """ZP26--34, using the intended doubled point rather than generic lines."""
    q, v = len(times)-1, times[-1][1]
    tables = source.tables_at(times[:-1])
    blocks, seen, all_supports = [], set(), []
    for t,(u,w) in enumerate(times[:-1],start=1):
        points = [(0,w,-u),(-3*u,1,0),(u*w,w,-2*u),(-u*w,w,-u),(-w,0,1)]
        labels = ['Q0','Q2','P02','P12','R_doubled']
        tangent = (-2*u,1,0)
        quadratic = [[monomial_value(e,X) for e in monomials(2)] for X in points]
        quadratic.append([derivative_value(e,points[-1],tangent) for e in monomials(2)])
        qcertificate = incoming.matrix_certificate(quadratic)
        assert qcertificate['rank_certificate']['rank'] == 6
        cubic_values = []
        for X in points:
            L = [residue.dot(row,X,P) for row in tables[t]]
            cubic_values.append([X[a]*L[(a+1)%3]*L[(a+2)%3] % P for a in range(3)]
                                +[L[0]*L[1]*L[2] % P])
        R = points[-1]
        L = [residue.dot(row,R,P) for row in tables[t]]
        dL = [residue.dot(row,tangent,P) for row in tables[t]]
        dcubics = []
        for a in range(3):
            b,c = [j for j in range(3) if j != a]
            dcubics.append((tangent[a]*L[b]*L[c]+R[a]*(dL[b]*L[c]+L[b]*dL[c])) % P)
        dcubics.append(sum(dL[a]*L[(a+1)%3]*L[(a+2)%3] for a in range(3)) % P)
        assert not any(x for row in cubic_values for x in row) and not any(dcubics)
        normalized = [canonical_point(X) for X in points]
        assert len(set(normalized)) == 5 and not set(normalized).intersection(seen)
        assert canonical_point((0,1,0)) not in normalized and canonical_point((0,0,1)) not in normalized
        tilde_values = [(X[0]+2*v*X[2]) % P for X in points]
        assert all(tilde_values)
        seen.update(normalized)
        all_supports.extend((t,label,X) for label,X in zip(labels,points))
        blocks.append(dict(old_block=t,support_labels=labels,support_points=points,
                           doubled_point_tangent=tangent,quadratic_restriction_matrix=quadratic,
                           quadratic_restriction_certificate=qcertificate,
                           four_cubics_vanish_on_six_conditions=True,
                           new_tilde_line_values=tilde_values))
    separator_controls = 0
    for t,table in tables.items():
        for other,_,X in all_supports:
            if other == t:
                continue
            L = [residue.dot(row,X,P) for row in table]
            values = [X[a]*L[(a+1)%3]*L[(a+2)%3] % P for a in range(3)]+[L[0]*L[1]*L[2] % P]
            assert any(values)
            separator_controls += 1
    new_linear = [[0,1,0],[-2*v % P,0,1],[0,0,1]]
    new_certificate = incoming.matrix_certificate(new_linear)
    assert new_certificate['rank_certificate']['rank'] == 3
    old_vertex_products = []
    for X in ((0,1,0),(0,0,1)):
        value = 1
        for table in tables.values():
            for row in table:
                value = value*residue.dot(row,X,P) % P
        assert value
        old_vertex_products.append(value)
    ambient = (9*q*q+9*q+6)//2
    return dict(old_blocks=blocks,pairwise_disjoint_supports=True,
                old_schemes_avoid_coordinate_vertices=True,new_tilde_avoids_all_old_supports=True,
                other_support_separator_controls=separator_controls,
                new_boundary_plus_normalization_linear_matrix=new_linear,
                new_boundary_plus_normalization_certificate=new_certificate,
                D_old_at_e1_e2=old_vertex_products,
                characteristic=P,boundary_ambient_dimension=ambient,
                justification_reference='SOURCE24_ZERO_PREFIX_EXTENSION.md ZP26--34; the displayed interpolation argument applies under these checked field conditions.')


def cleared_new_block(v, X):
    """Polynomial dual arithmetic for C_n=D_n^blk K_n, with no inverse."""
    numerators = [[(X[0] % P,0),(0,G[a][1]*X[1] % P),(G[a][2]*v*X[2] % P,0)] for a in range(3)]
    lines = [tuple(sum(entry[k] for entry in row) % P for k in (0,1)) for row in numerators]
    D = dual.mul(dual.mul(lines[0],lines[1]),lines[2])
    C = [[dual.mul(numerators[a][b],dual.mul(lines[(a+1)%3],lines[(a+2)%3]))
          for b in range(3)] for a in range(3)]
    return D,C,lines,numerators


def cleared_derivative_values(times, X, columns):
    n, v = len(times), times[-1][1]
    old_tables = source.tables_at(times[:-1])
    old_denominators = [[residue.dot(row,X,P) for row in table] for table in old_tables.values()]
    assert all(x for row in old_denominators for x in row)
    Dold = 1
    for row in old_denominators:
        for value in row:
            Dold = Dold*value % P
    Dnew,Cnew,_,_ = cleared_new_block(v,X)
    J = [[value[1] for value in row] for row in Cnew]
    kernels = {t:residue.ordinary_kernel(old_tables,t,X,P) for t in old_tables}
    kernels[n] = J
    products, primitives = {}, {}

    def product(order):
        key = tuple(order)
        if key not in products:
            products[key] = residue.word_product(kernels,order,P)
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,t,a = key
                value = X[a]*(Dnew[1]*int(a == 2)-product(source.word(n,t))[a][2])
            else:
                _,t,s,a,b = key
                tail = product(source.word(n,s,t))[b][2]
                if t == n:
                    value = X[a]*J[a][b]*(int(b == 2)-tail)
                else:
                    value = X[a]*kernels[t][a][b]*(Dnew[1]*int(b == 2)-tail)
            primitives[key] = Dold*value*source.inverse(X[2]) % P
        return primitives[key]
    values = [sum(coefficient*primitive(key) for coefficient,key in c['terms']) % P for c in columns]
    return values,dict(Dold=Dold,old_denominators=old_denominators,Dnew=Dnew,Jnew=J)


def actual_dual_values(times, X, columns):
    """Independent actual K words over dual u_n, at ordinary unit points."""
    n,v = len(times),times[-1][1]
    old_tables = source.tables_at(times[:-1])
    kernels = {t:[[(value,0) for value in row] for row in residue.ordinary_kernel(old_tables,t,X,P)]
               for t in old_tables}
    Dold = 1
    for table in old_tables.values():
        for row in table:
            Dold = Dold*residue.dot(row,X,P) % P
    Dnew,_,lines,numerators = cleared_new_block(v,X)
    assert all(line[0] for line in lines)
    kernels[n] = [[dual.mul(value,dual.inverse(lines[a])) for value in row] for a,row in enumerate(numerators)]
    products, primitives = {}, {}

    def product(order):
        key = tuple(order)
        if key not in products:
            value = dual.identity()
            for t in order:
                value = dual.mmul(value,kernels[t])
            products[key] = value
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,t,a = key
                value = dual.scale(X[a],dual.sub(dual.ONE if a == 2 else dual.ZERO,product(source.word(n,t))[a][2]))
            else:
                _,t,s,a,b = key
                tail = dual.sub(dual.ONE if b == 2 else dual.ZERO,product(source.word(n,s,t))[b][2])
                value = dual.scale(X[a],dual.mul(kernels[t][a][b],tail))
            primitives[key] = dual.scale(Dold*source.inverse(X[2]),dual.mul(Dnew,value))
        return primitives[key]
    values = []
    for c in columns:
        value = dual.ZERO
        for coefficient,key in c['terms']:
            value = dual.add(value,dual.scale(coefficient,primitive(key)))
        values.append(value)
    return values


def trace_points(times, target):
    n,v = len(times),times[-1][1]
    old_tables = source.tables_at(times[:-1])
    xs,rejected,x = [],[],0

    def permitted(a):
        X = (-v % P,a,1)
        return a != 0 and all(residue.dot(row,X,P) for table in old_tables.values() for row in table)

    while len(xs) < target:
        x += 1
        if permitted(x):
            xs.append(x)
        else:
            rejected.append(x)
    rng = random.Random(360024+n)
    while len(xs) < target+6:
        x = rng.randrange(1,P)
        if x not in xs and permitted(x):
            xs.append(x)
    return xs,rejected


def inherited_kernel_check(q, times, columns, B0, derivative_matrix, normalized_jet_rows,
                           xs, coefficient_observations, saved):
    """Only q=4,5: the saved old positive image saturates its ambient bound."""
    oldcase = next(case for case in saved['cases'] if case['m'] == q)
    oldcolumns,_ = source.larger_columns(q)
    assert json.loads(json.dumps(oldcolumns)) == oldcase['larger_spaces']['zero_prefix_columns']
    oldmatrix = oldcase['larger_spaces']['zero_prefix_matrix']
    oldcert = oldcase['larger_spaces']['zero_prefix_certificate']
    assert residue.matrix_hash(oldmatrix) == oldcert['sha256']
    oldpivots,oldfree,oldkernel = dual.rref_kernel(oldmatrix)
    assert len(oldpivots) == 9*q*(q-1)//2+3*q
    source_index = {json.dumps(c,sort_keys=True):i for i,c in enumerate(columns)}
    indices = [source_index[json.dumps(c,sort_keys=True)] for c in oldcolumns]
    embedded = [[0]*len(columns) for _ in oldkernel]
    for vector,oldvector in zip(embedded,oldkernel):
        for i,value in zip(indices,oldvector):
            vector[i] = value
    E = transpose(embedded)
    assert not any(x for row in schur.matrix_product(B0,E) for x in row)
    theta = schur.matrix_product(normalized_jet_rows,E)
    coefficients = schur.matrix_product(coefficient_observations,E)
    old_tables = source.tables_at(times[:-1])
    formula_checks = 0
    v = times[-1][1]
    for row,x in zip(theta,xs):
        X = (-v % P,x,1)
        old_values,_,_,denominators = source.evaluator(old_tables,X)
        vectors = old_values(oldcolumns)
        components = schur.matrix_product(transpose(vectors),transpose(oldkernel))
        assert not any(components[2])
        Dold = 1
        for line in denominators:
            for value in line:
                Dold = Dold*value % P
        expected = [pow(v,3,P)*Dold*R1*source.inverse(X[0]*X[1]) % P for R1 in components[1]]
        assert row == expected
        formula_checks += len(oldkernel)
    generic_checks = 0
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        old_values,_,_,denominators = source.evaluator(old_tables,X)
        components = schur.matrix_product(transpose(old_values(oldcolumns)),transpose(oldkernel))
        assert not any(components[2])
        Dold = 1
        for line in denominators:
            for value in line:
                Dold = Dold*value % P
        direct = actual_dual_values(times,X,columns)
        zero = schur.matrix_product([[value[0] for value in direct]],E)[0]
        actual = schur.matrix_product([[value[1] for value in direct]],E)[0]
        assert not any(zero)
        expected = [-v*X[1]*(X[0]+2*v*X[2])*Dold*R1 % P for R1 in components[1]]
        assert actual == expected
        generic_checks += len(oldkernel)
    certificate = incoming.matrix_certificate(coefficients)
    return dict(old_length=q,old_positive_matrix_sha256=oldcert['sha256'],
                old_source_columns=oldcolumns,old_pivot_columns=oldpivots,old_free_columns=oldfree,
                old_original_coordinate_kernel_basis=oldkernel,
                inherited_source_indices=indices,embedded_kernel_basis=embedded,
                boundary_kernel_inclusion_verified=True,
                theta_coefficient_matrix=coefficients,theta_certificate=certificate,
                trace_formula='Theta = v^3 D_q f, f=R1/(X0 X1), restricted to ell.',
                trace_formula_component_checks=formula_checks,
                generic_actual_dual_formula='p_1 = -v X1 (X0+2v X2) D_q R1',
                generic_actual_dual_component_checks=generic_checks,
                scope='Only the saturated old positive cases q=4,5. The unresolved q=3 sampled kernel is not used.')


def calculate(case, saved):
    started,n = time.monotonic(),case['m']
    q,target = n-1,3*(n-1)
    times,B0 = case['special_time_factors'],case['full_zero_prefix_matrix']
    columns,_ = source.larger_columns(n)
    assert json.loads(json.dumps(columns)) == case['zero_prefix_columns']
    assert case['prime'] == P and case['G'] == [list(row) for row in G]
    boundary_cert = case['full_zero_prefix_certificate']
    assert residue.matrix_hash(B0) == boundary_cert['sha256']
    geometry = field_geometry(times)
    pivots,free,kernel = dual.rref_kernel(B0)
    assert len(pivots) == boundary_cert['rank_certificate']['rank'] == geometry['boundary_ambient_dimension']
    assert pivots == boundary_cert['rank_certificate']['nonzero_minor']['columns']
    K = transpose(kernel)
    v = times[-1][1]
    xs,rejected = trace_points(times,target)
    derivative_rows,normalized_rows,point_controls = [],[],[]
    for x in xs:
        X = (-v % P,x,1)
        values,controls = cleared_derivative_values(times,X,columns)
        expected_J = [[2*x*v*entry % P for entry in (X[0],0,v)],
                      [x*v*entry % P for entry in (X[0],0,v)],[0,0,0]]
        assert controls['Dnew'] == (0,0) and controls['Jnew'] == expected_J
        derivative_rows.append(values)
        normalized_rows.append([value*source.inverse(x*x) % P for value in values])
        point_controls.append(dict(point=X,**controls))
    # Restrict FIRST, then interpolate and rank the induced map.
    restricted = schur.matrix_product(derivative_rows,K)
    theta_values = [[value*source.inverse(x*x) % P for value in row] for x,row in zip(xs,restricted)]
    vandermonde = [[pow(x,k,P) for k in range(target)] for x in xs[:target]]
    Vinv,Vcertificate = schur.invert(vandermonde)
    coefficients = schur.matrix_product(Vinv,theta_values[:target])
    for x,row in zip(xs[target:],theta_values[target:]):
        expected = schur.matrix_product([[pow(x,k,P) for k in range(target)]],coefficients)[0]
        assert expected == row
    jetcertificate = incoming.matrix_certificate(coefficients)
    coefficient_observations = schur.matrix_product(Vinv,normalized_rows[:target])
    assert schur.matrix_product(coefficient_observations,K) == coefficients
    generic_controls = []
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        direct = actual_dual_values(times,X,columns)
        cleared,controls = cleared_derivative_values(times,X,columns)
        assert cleared == [value[1] for value in direct]
        assert not any(x for x in schur.matrix_product([[value[0] for value in direct]],K)[0])
        generic_controls.append(dict(point=X,actual_dual_cleared_values=direct,
                                     independent_cleared_derivative_sha256=residue.matrix_hash([cleared]),
                                     original_kernel_constant_terms_zero=True,**controls))
    boundary_minor = boundary_cert['rank_certificate']['nonzero_minor']
    jetminor = jetcertificate['rank_certificate']['nonzero_minor']
    br,bc,jr,jc = boundary_minor['rows'],pivots,jetminor['rows'],jetminor['columns']
    top_left = [[B0[i][j] for j in bc] for i in br]
    bottom_left = [[coefficient_observations[i][j] for j in bc] for i in jr]
    bottom_right = [[coefficients[i][j] for j in jc] for i in jr]
    mixed = [row+[0]*len(jc) for row in top_left]+[left+right for left,right in zip(bottom_left,bottom_right)]
    mixedcertificate = incoming.matrix_certificate(mixed)
    expected_determinant = boundary_minor['determinant_mod_prime']*jetminor['determinant_mod_prime'] % P
    assert mixedcertificate['rank_certificate']['determinant_mod_prime'] == expected_determinant
    assert mixedcertificate['rank_certificate']['rank'] == len(pivots)+jetcertificate['rank_certificate']['rank']
    result = dict(n=n,q=q,prime=P,G=G,time_factors=times,field_geometry=geometry,
                  original_source_columns=columns,
                  saved_boundary_reference='source24-zero-prefix-extension-results.json: boundary_full_space_followup',
                  saved_boundary_matrix_sha256=boundary_cert['sha256'],saved_boundary_point_count=len(B0),
                  boundary_rank=len(pivots),boundary_pivot_columns=pivots,boundary_free_columns=free,
                  original_source_kernel_basis=kernel,kernel_basis_orientation='Each listed vector has one coefficient per original source column.',
                  original_source_kernel_basis_sha256=residue.matrix_hash(kernel),
                  exact_boundary_kernel_equations_and_systematic_free_coordinates_verified=True,
                  trace_x_values=xs,rejected_initial_x_values=rejected,trace_controls=point_controls,
                  actual_cleared_derivative_observation_matrix=derivative_rows,
                  derivative_after_original_kernel=restricted,
                  normalized_kernel_trace_values=theta_values,
                  interpolation_monomials=['x^'+str(k) for k in range(target)],
                  interpolation_inverse_certificate=Vcertificate,
                  theta_coefficient_matrix=coefficients,theta_certificate=jetcertificate,
                  extra_interpolation_points=len(xs)-target,all_extra_interpolation_values_match=True,
                  degree_justification='Paper ZP35--36 on the actual boundary kernel; extra evaluations are controls, not a standalone polynomial-identity proof.',
                  generic_actual_dual_controls=generic_controls,
                  mixed_minor_source_pivot_columns=bc,mixed_minor_selected_kernel_indices=jc,
                  mixed_minor_boundary_rows=br,mixed_minor_theta_rows=jr,
                  mixed_boundary_plus_jet_matrix=mixed,mixed_boundary_plus_jet_certificate=mixedcertificate,
                  mixed_determinant_equals_boundary_minor_times_induced_jet_minor=True,
                  target_jet_dimension=target,target_full_dimension=9*n*(n-1)//2+3*n)
    if q in (4,5):
        result['inherited_old_scalar_kernel'] = inherited_kernel_check(
            q,times,columns,B0,derivative_rows,normalized_rows,xs,coefficient_observations,saved)
    result['elapsed_seconds'] = time.monotonic()-started
    print(json.dumps(dict(n=n,boundary_rank=len(pivots),kernel_dimension=len(kernel),
                          induced_jet_rank=jetcertificate['rank_certificate']['rank'],target=target,
                          mixed_rank=mixedcertificate['rank_certificate']['rank'],
                          mixed_determinant=mixedcertificate['rank_certificate']['determinant_mod_prime'],
                          inherited_kernel_jet_rank=(result['inherited_old_scalar_kernel']['theta_certificate']['rank_certificate']['rank'] if q in (4,5) else None),
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    saved = json.loads((HERE/'source24-zero-prefix-extension-results.json').read_text())
    started,cases,limitation = time.monotonic(),[],None

    def guard(_signal,_frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        for n in (4,5,6):
            case = next(c for c in saved['boundary_full_space_followup']['cases'] if c['m'] == n)
            cases.append(calculate(case,saved))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result = dict(status='Actual original-coordinate first splitting jet at the three recorded boundary fixtures.',
                  scope='Finite modular certificates and exact controls only. No uniform boundary-spanning or all-length jet-surjectivity theorem is claimed.',
                  cases=cases,elapsed_seconds=time.monotonic()-started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('elapsed_seconds','maximum_rss_bytes','bounded_limitation')}),flush=True)


if __name__ == '__main__':
    main()
