#!/usr/bin/env python3
"""Bounded sanity checks of terminal append, cubic clearing, and commutators.

For prefixes q=2,3,4, append one final block (m=q+1). Check the actual raw
and normalized completed rows, the marked-seed append correction, and the
old-pair transfer commutator on actual seed residue data. The small cubic
matrix identity is checked coefficientwise over the rationals, independently
of its finite-field kernel evaluation. No ambient projection, annihilator,
boundary determinant, or all-length rank theorem is constructed.

Reproduce:
  nice -n 19 python3 exploration/source24_terminal_peeling.py --output exploration/source24-terminal-peeling-results.json
"""

import argparse
from fractions import Fraction
import itertools as it
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming
import source24_residue_differences as differences


P, G = incoming.P, incoming.G
residue, schur, sparse = incoming.residue, incoming.schur, incoming.sparse
POINTS = ((1, 2, 3), (2, 3, 5), (3, 5, 7))


def row_times(row, matrix):
    return residue.matmul([row], matrix, P)[0]


def row_add(a, b):
    return [(x+y) % P for x, y in zip(a,b)]


def row_sub(a, b):
    return [(x-y) % P for x, y in zip(a,b)]


def row_scale(scalar, row):
    return [scalar*x % P for x in row]


def poly_add(a, b):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, Fraction(0)) + coefficient
        if not result[monomial]:
            del result[monomial]
    return result


def poly_scale(scalar, a):
    scalar = Fraction(scalar)
    return {monomial:scalar*coefficient for monomial,coefficient in a.items() if scalar*coefficient}


def poly_multiply(a, b):
    result = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            exponent = tuple(x+y for x,y in zip(ea,eb))
            result = poly_add(result, {exponent:ca*cb})
    return result


def poly_eval_mod(poly, X):
    return sum(coefficient.numerator * pow(coefficient.denominator,-1,P)
               * pow(X[0],e[0],P)*pow(X[1],e[1],P)*pow(X[2],e[2],P)
               for e,coefficient in poly.items()) % P


def rational_inverse3(A):
    adjugate = []
    for i in range(3):
        row = []
        for j in range(3):
            rr, cc = [r for r in range(3) if r!=j], [c for c in range(3) if c!=i]
            row.append((-1)**(i+j)*(A[rr[0]][cc[0]]*A[rr[1]][cc[1]]
                                   - A[rr[0]][cc[1]]*A[rr[1]][cc[0]]))
        adjugate.append(row)
    determinant = sum(A[0][i]*adjugate[i][0] for i in range(3))
    assert determinant
    inverse = [[Fraction(x,determinant) for x in row] for row in adjugate]
    assert [[sum(A[i][k]*inverse[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)] == residue.identity()
    return inverse, determinant


def cubic_identity(table):
    """T4 as an equality of sparse cubic polynomials over Q, not samples."""
    variables = [{tuple(int(i==a) for i in range(3)):Fraction(1)} for a in range(3)]
    forms = [{tuple(int(i==d) for i in range(3)):Fraction(table[a][d]) for d in range(3)}
             for a in range(3)]
    h = []
    for a in range(3):
        value = variables[a]
        for c in range(3):
            if c!=a:
                value = poly_multiply(value, forms[c])
        h.append(value)
    C = [[poly_scale(table[a][i],h[a]) for i in range(3)] for a in range(3)]
    inverse, determinant = rational_inverse3(table)
    product = []
    for a in range(3):
        row = []
        for i in range(3):
            value = {}
            for k in range(3):
                value = poly_add(value,poly_scale(inverse[k][i],C[a][k]))
            assert value == (h[a] if i==a else {}), ('T4 cubic identity failed.', a, i)
            row.append(value)
        product.append(row)
    assert all(sum(e)==3 for entry in h for e in entry)
    certificate = dict(coefficient_field='Q', cubic_matrix_times_actual_coefficient_inverse_is_diagonal=True,
                       coefficient_identities_checked=9, all_h_are_homogeneous_cubics=True,
                       coefficient_matrix_determinant=determinant,
                       coefficient_matrix_inverse=[[str(x) for x in row] for row in inverse],
                       h_coefficients=[[[list(e),str(c)] for e,c in sorted(poly.items())] for poly in h])
    return C, h, certificate


def raw_and_completed(A, blocks, kernels, X, t, s, a, b):
    word = residue.ordered_word([u for u in blocks if u!=t],s)
    product = residue.word_product(kernels,word,P)
    raw = row_scale(X[a]*kernels[t][a][b],product[b])
    diagonal = [X[a]*int(a==b and i==a) % P for i in range(3)]
    return raw, row_sub(raw,diagonal)


def marked_seed(A, blocks, kernels, X, t, a, constant):
    r = min(u for u in blocks if u!=t)
    s = min(u for u in blocks if u!=r)
    _, first = raw_and_completed(A,blocks,kernels,X,t,r,a,0)
    total = [0,0,0]
    for b in range(3):
        _, row = raw_and_completed(A,blocks,kernels,X,r,s,0,b)
        total = row_add(total,row)
    return row_add(row_scale(-1,first),row_scale(constant,total))


def ordinary_append_checks(q, A, constants, Cpoly, hpoly):
    old, full, terminal = list(range(2,q+2)), list(range(2,q+3)), q+2
    inverse, _ = schur.invert(A[terminal])
    raw_count = normalized_count = seed_count = cleared_count = correction_nonzero = 0
    cubic_evaluations = []
    for X in POINTS:
        kernels = {t:residue.ordinary_kernel(A,t,X,P) for t in full}
        K = kernels[terminal]
        lines = [residue.dot(A[terminal][a],X,P) for a in range(3)]
        D = lines[0]*lines[1]*lines[2] % P
        C = [[poly_eval_mod(Cpoly[a][i],X) for i in range(3)] for a in range(3)]
        actual = [[D*X[a]*K[a][i]*pow(X[i],-1,P) % P for i in range(3)] for a in range(3)]
        assert C == actual, 'Polynomial C does not evaluate to D*tilde K.'
        h = [poly_eval_mod(poly,X) for poly in hpoly]
        assert residue.matmul(C,inverse,P) == [[h[a]*int(a==i) % P for i in range(3)] for a in range(3)]
        Kinverse = [[pow(X[a],-1,P)*inverse[a][i]*lines[i] % P for i in range(3)] for a in range(3)]
        assert residue.matmul(K,Kinverse,P) == residue.matmul(Kinverse,K,P) == residue.identity()
        denominator_old = 1
        for t in old:
            for a in range(3):
                denominator_old = denominator_old*residue.dot(A[t][a],X,P) % P
        for t in old:
            for s in old:
                if s==t:
                    continue
                for a,b in it.product(range(3),repeat=2):
                    raw_old, Qold = raw_and_completed(A,old,kernels,X,t,s,a,b)
                    raw_new, Qnew = raw_and_completed(A,full,kernels,X,t,s,a,b)
                    assert raw_new == row_times(raw_old,K), ('T3 raw append failed.',q,t,s,a,b,X)
                    correction = row_scale(X[a]*int(a==b),row_sub(K[a],[int(i==a) for i in range(3)]))
                    assert Qnew == row_add(row_times(Qold,K),correction), ('Normalized append failed.',q,t,s,a,b,X)
                    correction_nonzero += bool(any(correction))
                    phi_old = [denominator_old*raw_old[i]*pow(X[i],-1,P) % P for i in range(3)]
                    phi_new = [denominator_old*D*raw_new[i]*pow(X[i],-1,P) % P for i in range(3)]
                    assert phi_new == row_times(phi_old,C), 'Clearing does not commute with append.'
                    assert row_times(phi_new,inverse) == [h[i]*phi_old[i] % P for i in range(3)]
                    raw_count += 1
                    normalized_count += 1
                    cleared_count += 1
        for (t,a),constant in constants.items():
            Rold = marked_seed(A,old,kernels,X,t,a,constant)
            Rnew = marked_seed(A,full,kernels,X,t,a,constant)
            d = (int(a==0)-constant) % P
            correction = row_scale(d*X[0],row_sub([1,0,0],K[0]))
            assert Rnew == row_add(row_times(Rold,K),correction), ('T11 seed append failed.',q,t,a,X)
            Rhat_old = row_sub(Rold,[d*X[0] % P,0,0])
            Rhat_new = row_sub(Rnew,[d*X[0] % P,0,0])
            assert Rhat_new == row_times(Rhat_old,K)
            seed_count += 1
        cubic_evaluations.append(dict(point=X, D=D, h=h, C_equals_D_tildeK=True,
                                      actual_kernel_inverse_verified=True))
    return dict(ordinary_points=POINTS,raw_append_rows_checked=raw_count,
                normalized_append_rows_checked=normalized_count,
                normalized_correction_nonzero_rows=correction_nonzero,
                cleared_append_and_cubic_division_rows_checked=cleared_count,
                marked_seed_append_rows_checked=seed_count,
                T3_raw_append_verified=True,normalized_append_correction_verified=True,
                T11_marked_seed_append_verified=True,raw_marked_seed_append_verified=True,
                cubic_kernel_evaluation_checks=cubic_evaluations)


def raw_pair_row(A, blocks, kernels, X, poles, t, s, a, b):
    """Actual completed/raw product pair residue, using its original ordered word."""
    if t in poles and poles[t]!=a:
        return [0,0,0]
    scalar = X[a]*A[t][a][b]*X[b] % P
    if t not in poles:
        scalar = scalar*pow(residue.dot(A[t][a],X,P),-1,P) % P
    product = residue.word_product(kernels,residue.ordered_word([u for u in blocks if u!=t],s),P)
    return row_scale(scalar,product[b])


def actual_seed_commutator(q, A, old_C, new_C, old_labels, new_labels, constants):
    old, terminal = list(range(2,q+2)), q+2
    old_O, old_geometry = residue.residue_matrix(q+2,A[:-1],P)
    new_O, new_geometry = residue.residue_matrix(q+3,A,P)
    old_S, new_S = schur.matrix_product(old_O,old_C),schur.matrix_product(new_O,new_C)
    old_pair_labels,_ = schur.canonical_labels(q+2)
    new_pair_labels,_ = schur.canonical_labels(q+3)
    new_pair_index = {label:i for i,label in enumerate(new_pair_labels)}
    new_seed_index = {label:i for i,label in enumerate(new_labels)}
    Ginv,_ = schur.invert([list(row) for row in G])
    w = Ginv[2]
    E = [[int(i==2)*w[j] % P for j in range(3)] for i in range(3)]
    assert sum(w) % P == 0
    actual_checks = commutator_checks = nonzero = ambient_checks = ambient_nonzero = 0
    first_nonzero = None
    commutator_matrix = []
    for position in range(0,len(old_pair_labels),2):
        u,v,cu,cv,_ = old_pair_labels[position]
        X = residue.cross(A[u][cu],A[v][cv],P)
        U = [A[u][cu][i]*X[i] % P for i in range(3)]
        V = [A[v][cv][i]*X[i] % P for i in range(3)]
        kernels = {t:([U[:] if a==cu else [0]*3 for a in range(3)] if t==u else
                      [V[:] if a==cv else [0]*3 for a in range(3)] if t==v else
                      residue.ordinary_kernel(A,t,X,P)) for t in old}
        K = residue.ordinary_kernel(A,terminal,X,P)
        commutator = schur.matrix_difference(residue.matmul(K,E,P),residue.matmul(E,K,P))
        ambient = row_times([1,P-1,0],commutator)
        u_time = A[terminal][0][1]*pow(G[0][1],-1,P) % P
        v_time = A[terminal][0][2]*pow(G[0][2],-1,P) % P
        closed = (v_time*X[2]*((G[0][2]-G[1][2])*X[0]
                  +u_time*(G[0][2]*G[1][1]-G[1][2]*G[0][1])*X[1])
                  *pow(residue.dot(A[terminal][0],X,P)*residue.dot(A[terminal][1],X,P) % P,-1,P)) % P
        assert closed == (K[0][2]-K[1][2]) % P
        assert ambient == row_scale(closed,w), 'T13 ambient commutator failed.'
        ambient_checks += 1
        ambient_nonzero += bool(any(ambient))
        alpha_row,beta_row = [],[]
        for j,(t,a) in enumerate(old_labels):
            r = row_add(row_scale(old_S[position][j],U),row_scale(old_S[position+1][j],V))
            newj = new_seed_index[t,a]
            newpos = new_pair_index[u,v,cu,cv,'alpha']
            appended = row_add(row_scale(new_S[newpos][newj],U),row_scale(new_S[newpos+1][newj],V))
            first = min(s for s in old if s!=t)
            second = min(s for s in old if s!=first)
            direct = row_scale(-1,raw_pair_row(A,old,kernels,X,{u:cu,v:cv},t,first,a,0))
            for b in range(3):
                direct = row_add(direct,row_scale(constants[t,a],
                    raw_pair_row(A,old,kernels,X,{u:cu,v:cv},first,second,0,b)))
            assert r == direct, 'Actual O*C seed residue differs from the completed-product seed.'
            assert sum(r) % P == sum(appended) % P == 0
            assert appended == row_times(r,K), 'T11 old-pair transport failed.'
            actual_checks += 1
            for B in range(3):
                factor = X[B]*pow(X[2],-1,P) % P
                transfer_after_append = row_scale(factor*appended[2],w)
                append_after_transfer = row_times(row_scale(factor*r[2],w),K)
                lhs = row_sub(transfer_after_append,append_after_transfer)
                rhs = row_scale(factor,row_times(r,commutator))
                assert lhs == rhs, ('T12 actual-seed commutator failed.',q,u,v,cu,cv,t,a,B)
                av,bv = residue.coordinates(lhs,U,V,P)
                alpha_row.append(av)
                beta_row.append(bv)
                commutator_checks += 1
                if any(lhs):
                    nonzero += 1
                    if first_nonzero is None:
                        first_nonzero = dict(old_pair=[u,v,cu,cv],point_mod_prime=X,
                                             seed=[t,a],coordinate_transfer_B=B,
                                             actual_seed_pair_residue=r,appended_seed_pair_residue=appended,
                                             actual_append_kernel=K,w=w,commutator_matrix=commutator,
                                             left_difference=lhs,right_commutator=rhs)
        commutator_matrix.extend((alpha_row,beta_row))
    assert nonzero, 'No nonzero actual-seed transport commutator found at this fixture.'
    return dict(old_geometry=old_geometry,appended_geometry=new_geometry,
                old_actual_source_sha256=residue.matrix_hash(old_O),appended_actual_source_sha256=residue.matrix_hash(new_O),
                old_actual_seed_pair_sha256=residue.matrix_hash(old_S),appended_actual_seed_pair_sha256=residue.matrix_hash(new_S),
                direct_completed_seed_pair_checks=actual_checks,old_pair_seed_transport_verified=True,
                T12_actual_seed_checks=commutator_checks,nonzero_actual_seed_commutators=nonzero,
                first_nonzero_actual_seed_commutator=first_nonzero,
                commutator_pair_coordinate_matrix_sha256=residue.matrix_hash(commutator_matrix),
                T13_ambient_node_checks=ambient_checks,nonzero_ambient_node_commutators=ambient_nonzero,
                scope='T12 is checked on actual marked-seed pair data and the nodewise coordinate-transfer map. The normalized ambient lifts themselves are not constructed.')


def check_case(q,mode):
    started = time.monotonic()
    times = sparse.factors(q+1,mode)
    A = [[list(row) for row in G] for _ in range(2)] + sparse.coefficient_tables(G,times)
    old_C,_,old_labels,old_constants = differences.seed_coefficients(q,A[:-1])
    new_C,_,new_labels,new_constants = differences.seed_coefficients(q+1,A)
    constants = {(x['t'],x['A']):x['c_tA'] for x in old_constants}
    new_by_label = {(x['t'],x['A']):x for x in new_constants}
    assert all(x==new_by_label[x['t'],x['A']] for x in old_constants), 'Old seed constants changed on append.'
    Cpoly,hpoly,cubic = cubic_identity(A[-1])
    ordinary = ordinary_append_checks(q,A,constants,Cpoly,hpoly)
    commutator = actual_seed_commutator(q,A,old_C,new_C,old_labels,new_labels,constants)
    result = dict(prefix_blocks=q,appended_blocks=q+1,time_fixture=mode,prime=P,G=G,
                  time_factors=times,old_H4_constants=old_constants,old_seed_constants_unchanged=True,
                  rational_cubic_identity=cubic,ordinary_append_checks=ordinary,
                  actual_seed_commutator_checks=commutator,elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(prefix_blocks=q,appended_blocks=q+1,time_fixture=mode,
                          raw_append_checks=ordinary['raw_append_rows_checked'],
                          exact_rational_cubic=True,actual_seed_commutator_checks=commutator['T12_actual_seed_checks'],
                          nonzero_seed_commutators=commutator['nonzero_actual_seed_commutators'],
                          seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    started,cases=time.monotonic(),[]

    def guard(_signal,_frame):
        if time.monotonic()-started>=28:
            raise TimeoutError('28-second terminal-peeling cutoff.')
        if incoming.maximum_rss_bytes()>=95*1024**2:
            raise TimeoutError('95MiB terminal-peeling RSS guard.')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    limitation=None
    try:
        for mode in ('economic','independent'):
            for q in (2,3,4):
                cases.append(check_case(q,mode))
    except TimeoutError as error:
        limitation=str(error)
        print(json.dumps(dict(limitation=limitation)),flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    result=dict(status='Bounded local algebra and finite-field sanity checks; no terminal-annihilator or all-length rank theorem.',
                indexing='Prefix sizes q=2,3,4 are appended to m=q+1=3,4,5 so every raw family and T11/T12 seed check is nontrivial.',
                formulas_checked='T3 raw append; normalized append correction; T4 coefficientwise rational cubic identity and actual-kernel clearing; T11 marked-seed append; T12 actual old-pair commutator; T13 ambient commutator.',
                limits='No construction or check of the large ambient projection, epsilon compression, recursive annihilator, or T10 boundary determinant. Finite examples do not prove a uniform rank theorem.',
                elapsed_seconds=time.monotonic()-started,maximum_rss_bytes=incoming.maximum_rss_bytes(),
                bounded_limitation=limitation,cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
