#!/usr/bin/env python3
"""Actual zero-prefix source family: base, append identities, and finite ranks.

Use G=((1,1,1),(1,2,1),(1,3,2)), block labels 1,...,m, and the actual
F_tsab=X_a K_t(a,b)e_b(I-P_s^omit_t), empty(t,a)=X_a e_a(I-P_t).
C_tsab=F_tsab-F_t,r(t),ab with r(t)=min(other blocks).
The family starts with empty(1,a)-empty(2,a), a=0,1,2.  At stage n=q+1,
append C_t,n,a,0 for t<=q,a=0,1; sum_b C_1,n,a,b for a=0,1; and
C_n,s,a,2 for 2<=s<=q,a=1,2.  Every inherited column uses the complete
actual word at the FINAL horizon, not its earlier shorter word.

At u_n=0, verify R_new=R_old K_n and h_new=mu*h_old for h=R_2/X_2.
The X_2=0 restrictions are exact first-order dual coefficients of R_2,
never an evaluation of 0/0.  The other boundary is evaluated at X_0=0.
Rank certificates use only the recorded finite fixtures and observations.
No sampled deficiency is a rational-function upper bound or generic claim.
"""

import argparse
import json
from pathlib import Path
import random
import signal
import time

import source24_odd_incoming as incoming


P, residue, schur, dual = incoming.P, incoming.residue, incoming.schur, incoming.dual
G = ((1, 1, 1), (1, 2, 1), (1, 3, 2))


def inverse(x):
    assert x % P, 'Nonunit denominator.'
    return pow(x % P, -1, P)


def tables_at(times):
    return {t: [[g[0], g[1]*u % P, g[2]*v % P] for g in G]
            for t, (u, v) in enumerate(times, start=1)}


def word(m, first, omit=None):
    return [first]+[t for t in range(1, m+1) if t not in (first, omit)]


def first_other(t):
    return 2 if t == 1 else 1


def Cterms(t, s, a, b):
    return [(1, ('F', t, s, a, b)), (-1, ('F', t, first_other(t), a, b))]


def column(label, terms):
    return dict(label=label, terms=terms)


def new_columns(n):
    q = n-1
    result = [column(dict(kind='A', stage=n, t=t, a=a), Cterms(t,n,a,0))
              for t in range(1, n) for a in (0, 1)]
    result += [column(dict(kind='A_star', stage=n, a=a),
                      [term for b in range(3) for term in Cterms(1,n,a,b)]) for a in (0, 1)]
    result += [column(dict(kind='B', stage=n, s=s, a=a), Cterms(n,s,a,2))
               for s in range(2, n) for a in (1, 2)]
    assert len(result) == 4*q
    return result


def family_columns(m):
    result = [column(dict(kind='H_base', a=a),
                     [(1, ('empty',1,a)), (-1, ('empty',2,a))]) for a in range(3)]
    for n in range(3, m+1):
        result += new_columns(n)
    assert len(result) == 2*m*(m-1)-1
    return result


def larger_columns(m):
    C = [column(dict(kind='C', t=t, s=s, a=a, b=b), Cterms(t,s,a,b))
         for t in range(1,m+1) for s in range(1,m+1) if s not in (t, first_other(t))
         for a in range(3) for b in range(3)]
    H = [column(dict(kind='H', t=t, a=a), [(1, ('empty',t,a)), (-1, ('empty',1,a))])
         for t in range(2,m+1) for a in range(3)]
    E = [column(dict(kind='long_empty', t=t, a=a), [(1, ('empty',t,a))])
         for t in range(1,m+1) for a in range(3)]
    F = [column(dict(kind='selected_output_zero', t=t, a=a),
                [(1, ('F',t,first_other(t),a,0))]) for t in range(1,m+1) for a in range(3)]
    return C+H, C+E+F


def coefficients(terms):
    result = {}
    for coefficient, primitive in terms:
        result[tuple(primitive)] = result.get(tuple(primitive), 0)+coefficient
    return {primitive: coefficient for primitive, coefficient in result.items() if coefficient}


def inclusion_maps(m, family, zero, N):
    Cids = {(c['label']['t'],c['label']['s'],c['label']['a'],c['label']['b']): i
            for i,c in enumerate(zero) if c['label']['kind'] == 'C'}
    Hids = {(c['label']['t'],c['label']['a']): i
            for i,c in enumerate(zero) if c['label']['kind'] == 'H'}
    Eids = {(c['label']['t'],c['label']['a']): i
            for i,c in enumerate(N) if c['label']['kind'] == 'long_empty'}
    rec_to_zero = []
    for c in family:
        label = c['label']
        kind, a = label['kind'], label['a']
        if kind == 'H_base':
            terms = [(Hids[2,a], -1)]
        elif kind == 'A':
            terms = [(Cids[label['t'],label['stage'],a,0], 1)]
        elif kind == 'A_star':
            terms = [(Cids[1,label['stage'],a,b], 1) for b in range(3)]
        else:
            terms = [(Cids[label['stage'],label['s'],a,2], 1)]
        rec_to_zero.append(terms)
        expanded = [(factor*k, primitive) for j,factor in terms for k,primitive in zero[j]['terms']]
        assert coefficients(expanded) == coefficients(c['terms'])
    zero_to_N = []
    for i,c in enumerate(zero):
        label = c['label']
        if label['kind'] == 'C':
            assert N[i] == c
            terms = [(i, 1)]
        else:
            terms = [(Eids[label['t'],label['a']], 1), (Eids[1,label['a']], -1)]
        zero_to_N.append(terms)
        expanded = [(factor*k, primitive) for j,factor in terms for k,primitive in N[j]['terms']]
        assert coefficients(expanded) == coefficients(c['terms'])
    return rec_to_zero, zero_to_N


def evaluator(tables, X):
    m = len(tables)
    denominators = [[residue.dot(tables[t][a], X, P) for a in range(3)] for t in range(1,m+1)]
    assert all(value for row in denominators for value in row)
    kernels = {t: residue.ordinary_kernel(tables, t, X, P) for t in tables}
    products, primitives = {}, {}

    def product(order):
        key = tuple(order)
        if key not in products:
            products[key] = residue.word_product(kernels, order, P)
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,t,a = key
                tail = product(word(m,t))[a]
                value = [X[a]*(int(a == d)-tail[d]) % P for d in range(3)]
            else:
                _,t,s,a,b = key
                tail = product(word(m,s,t))[b]
                value = [X[a]*kernels[t][a][b]*(int(b == d)-tail[d]) % P for d in range(3)]
            assert sum(value) % P == 0
            primitives[key] = value
        return primitives[key]

    def values(columns):
        return [[sum(coefficient*primitive(key)[d] for coefficient,key in c['terms']) % P
                 for d in range(3)] for c in columns]
    return values, kernels, product, denominators


def axis_evaluator(tables, y):
    """Actual R_2 in F_p[epsilon]/epsilon^2 at X=(1,y,epsilon)."""
    m, X = len(tables), (dual.ONE, (y % P,0), (0,1))
    kernels, denominator_constants = {}, []
    for t, table in tables.items():
        K = []
        for row in table:
            numerators = [dual.scale(row[d], X[d]) for d in range(3)]
            denominator = tuple(sum(v[k] for v in numerators) % P for k in (0,1))
            denominator_constants.append(denominator[0])
            assert denominator[0]
            K.append([dual.mul(v, dual.inverse(denominator)) for v in numerators])
        kernels[t] = K
    products, primitives = {}, {}

    def product(order):
        key = tuple(order)
        if key not in products:
            value = dual.identity()
            for t in order:
                value = dual.mmul(value, kernels[t])
            products[key] = value
        return products[key]

    def primitive(key):
        if key not in primitives:
            if key[0] == 'empty':
                _,t,a = key
                value = dual.mul(X[a], dual.sub(dual.ONE if a == 2 else dual.ZERO,
                                                product(word(m,t))[a][2]))
            else:
                _,t,s,a,b = key
                tail = dual.sub(dual.ONE if b == 2 else dual.ZERO, product(word(m,s,t))[b][2])
                value = dual.mul(dual.mul(X[a], kernels[t][a][b]), tail)
            primitives[key] = value
        return primitives[key]

    def values(columns):
        result = []
        for c in columns:
            value = dual.ZERO
            for coefficient,key in c['terms']:
                value = dual.add(value, dual.scale(coefficient, primitive(key)))
            assert value[0] == 0
            result.append(value[1])
        return result
    return values, product, denominator_constants


def base_check():
    times, points, lines = [(1,1),(6,3)], [(-3,-2,5),(-3,-1,5),(-3,-1,3)], [(0,0),(1,1),(2,0)]
    tables = tables_at(times)
    integer_matrix, actual_matrix = [], []
    for X,(i,j) in zip(points, lines):
        assert sum(tables[1][i][d]*X[d] for d in range(3)) == 0
        assert sum(tables[2][j][d]*X[d] for d in range(3)) == 0
        integer_matrix.append([X[a]*(int(a == j)*tables[2][j][i]*X[i]*tables[1][i][2]
                                     -int(a == i)*tables[1][i][j]*X[j]*tables[2][j][2]) for a in range(3)])
        K1 = [[tables[1][i][d]*X[d] % P for d in range(3)] if a == i else [0,0,0] for a in range(3)]
        K2 = [[tables[2][j][d]*X[d] % P for d in range(3)] if a == j else [0,0,0] for a in range(3)]
        difference = schur.matrix_difference(residue.matmul(K2,K1,P), residue.matmul(K1,K2,P))
        actual_matrix.append([X[a]*difference[a][2]*inverse(X[2]) % P for a in range(3)])
    expected = [[-18,0,0],[0,6,0],[-54,0,27]]
    assert integer_matrix == expected
    assert actual_matrix == [[x % P for x in row] for row in expected]
    certificate = incoming.matrix_certificate(actual_matrix)
    assert certificate['rank_certificate']['determinant_mod_prime'] == -2916 % P
    return dict(times=times, point_labels=[dict(first_state=i, second_state=j, point=X) for X,(i,j) in zip(points,lines)],
                columns=family_columns(2), observation='L_(1,i) L_(2,j) h, h=R2/X2, at the listed exact projective representative.',
                integer_matrix=integer_matrix, integer_determinant=-2916,
                independently_evaluated_actual_K_matrix=actual_matrix, certificate=certificate)


def points_off_poles(table_sets, count):
    rng, points, rejected = random.Random(190024+len(table_sets[0])), [], 0
    while len(points) < count:
        X = (1, rng.randrange(1,P), rng.randrange(1,P))
        if any(residue.dot(row,X,P) == 0 for tables in table_sets for table in tables.values() for row in table):
            rejected += 1
            continue
        if X not in points:
            points.append(X)
    return points, rejected


def append_controls(m, times, special, family):
    q, v = m-1, special[-1][1]
    old_tables, new_tables = tables_at(times[:-1]), tables_at(special)
    inherited, new = family_columns(q), new_columns(m)
    count = len(inherited)
    ordinary, scalar_checks, vector_checks = [], 0, 0
    for X in ((1,2,3),(2,3,5),(3,5,7)):
        old_values, _, _, old_denominators = evaluator(old_tables,X)
        new_values, kernels, _, new_denominators = evaluator(new_tables,X)
        old_rows, new_rows = old_values(inherited), new_values(family)[:count]
        denominator = (X[0]+v*X[2])*(X[0]+2*v*X[2]) % P
        mu = v*X[0]*X[2]*inverse(denominator) % P
        for before,after in zip(old_rows,new_rows):
            assert sum(before) % P == sum(after) % P == 0
            assert residue.matmul([before],kernels[m],P)[0] == after
            assert after[2]*inverse(X[2]) % P == mu*before[2]*inverse(X[2]) % P
            vector_checks += 3
            scalar_checks += 1
        ordinary.append(dict(point=X, mu=mu, mu_denominator=denominator,
                             old_denominators=old_denominators, new_denominators=new_denominators))

    axis_rows, axis_labels, axis_details, formula_checks, inherited_zero_checks = [], [], [], 0, 0
    boundary_count = 2*q+8
    for y in range(1,boundary_count+1):
        values, product, denominators = axis_evaluator(new_tables,y)
        actual = values(family)
        assert not any(actual[:count])
        inherited_zero_checks += count
        actual_new = actual[count:]
        w = {t: product([u for u in range(1,m) if u != t])[0][2][1] for t in range(1,m)}
        expected = []
        for c in new:
            label, a = c['label'], c['label']['a']
            if label['kind'] == 'A':
                t = label['t']
                expected.append((1 if a == 0 else y)*(v-w[t])*inverse(1+(1 if a == 0 else 2)*times[t-1][0]*y) % P)
            elif label['kind'] == 'A_star':
                expected.append((1 if a == 0 else y)*(v-w[1]) % P)
            else:
                expected.append(0)
        assert actual_new == expected
        formula_checks += len(new)
        axis_rows.append(actual_new)
        axis_labels.append(dict(axis='X2=0', point=[1,y,0], method='Coefficient of epsilon in actual R2 at X=(1,y,epsilon).'))
        axis_details.append(dict(y=y, w=w, denominator_constants=denominators))
    first_boundary_rows = len(axis_rows)
    for x in range(1,boundary_count+1):
        X = (0,x,1)
        values, _, product, denominators = evaluator(new_tables,X)
        actual = values(family)
        assert not any(row[2] for row in actual[:count])
        inherited_zero_checks += count
        actual_new = [row[2] for row in actual[count:]]
        for j,c in enumerate(new):
            label = c['label']
            if label['kind'] == 'B':
                delta = (product(word(q,label['s']))[2][2]-product(word(q,1))[2][2]) % P
                expected = -(x if label['a'] == 1 else 1)*delta % P
                assert actual_new[j] == expected
                formula_checks += 1
        axis_rows.append(actual_new)
        axis_labels.append(dict(axis='X0=0', point=X, method='Ordinary actual source evaluation; X2=1.'))
        axis_details.append(dict(x=x, denominators=denominators))
    Awidth = 2*q+2
    Acertificate = incoming.matrix_certificate([row[:Awidth] for row in axis_rows[:first_boundary_rows]])
    Bcertificate = incoming.matrix_certificate([row[Awidth:] for row in axis_rows[first_boundary_rows:]])
    return dict(special_time_factors=special, generic_chart_controls=ordinary,
                actual_vector_append_component_checks=vector_checks, scalar_mu_checks=scalar_checks,
                inherited_zero_boundary_checks=inherited_zero_checks,
                boundary_formula_checks=formula_checks,
                new_column_labels=new, boundary_row_labels=axis_labels, boundary_details=axis_details,
                actual_new_boundary_matrix=axis_rows, combined_new_boundary_certificate=incoming.matrix_certificate(axis_rows),
                X2_boundary_A_certificate=Acertificate, X0_boundary_B_certificate=Bcertificate,
                normalization='X2-axis h is the first Taylor coefficient of R2, after proving its constant term zero. No zero coordinate is inverted.')


def combine_values(values, terms):
    return [sum(coefficient*values[j] for j,coefficient in column_terms) % P for column_terms in terms]


def calculate(m):
    started = time.monotonic()
    times = [(6**(t-1),3**(t-1)) for t in range(1,m+1)]
    tables = tables_at(times)
    special = times[:-1]+[(0,times[-1][1])] if m >= 3 else None
    special_tables = tables_at(special) if special else None
    family = family_columns(m)
    compare = 3 <= m <= 5
    zero, N = larger_columns(m) if compare else (None,None)
    inclusions = inclusion_maps(m,family,zero,N) if compare else None
    desired_dimension = 9*m*(m-1)//2+3*m if compare else len(family)
    points, rejected = points_off_poles([tables]+([special_tables] if special else []), desired_dimension+12)
    matrix, special_matrix, zero_matrix, Nmatrix, denominators = [], [], [], [], []
    for X in points:
        values, _, _, denoms = evaluator(tables,X)
        row = [v[2]*inverse(X[2]) % P for v in values(family)]
        matrix.append(row)
        denominators.append(denoms)
        if special:
            special_values, _, _, _ = evaluator(special_tables,X)
            special_matrix.append([v[2]*inverse(X[2]) % P for v in special_values(family)])
        if compare:
            zrow = [v[2]*inverse(X[2]) % P for v in values(zero)]
            Nrow = [v[2]*inverse(X[2]) % P for v in values(N)]
            assert combine_values(zrow,inclusions[0]) == row
            assert combine_values(Nrow,inclusions[1]) == zrow
            zero_matrix.append(zrow)
            Nmatrix.append(Nrow)
    certificate = incoming.matrix_certificate(matrix)
    result = dict(m=m, prime=P, G=G, time_factors=times, family_columns=family,
                  expected_column_count=2*m*(m-1)-1,
                  ordinary_points=points, rejected_points=rejected, ordinary_denominators=denominators,
                  all_recorded_denominators_are_units=True,
                  actual_h_evaluation_matrix=matrix, family_certificate=certificate)
    if special:
        result['u_last_zero_family_matrix'] = special_matrix
        result['u_last_zero_family_certificate'] = incoming.matrix_certificate(special_matrix)
        result['append_controls'] = append_controls(m,times,special,family)
    if compare:
        result['larger_spaces'] = dict(zero_prefix_columns=zero, N_columns=N,
                                      recursive_in_zero_prefix_terms=inclusions[0], zero_prefix_in_N_terms=inclusions[1],
                                      source_coefficient_inclusions_verified=True,
                                      all_evaluated_inclusions_verified=True,
                                      zero_prefix_matrix=zero_matrix, N_matrix=Nmatrix,
                                      zero_prefix_certificate=incoming.matrix_certificate(zero_matrix),
                                      N_certificate=incoming.matrix_certificate(Nmatrix),
                                      scope='Ranks of sampled observations at this single fixture; deficient ranks alone are not rational-function upper bounds.')
    result['elapsed_seconds'] = time.monotonic()-started
    print(json.dumps(dict(m=m, family_rank=certificate['rank_certificate']['rank'], columns=len(family),
                          u_last_zero_family_rank=(result['u_last_zero_family_certificate']['rank_certificate']['rank'] if special else None),
                          new_boundary_rank=(result['append_controls']['combined_new_boundary_certificate']['rank_certificate']['rank'] if special else None),
                          full_zero_prefix_rank=(result['larger_spaces']['zero_prefix_certificate']['rank_certificate']['rank'] if compare else None),
                          N_rank=(result['larger_spaces']['N_certificate']['rank_certificate']['rank'] if compare else None),
                          elapsed_seconds=result['elapsed_seconds'])), flush=True)
    return result


def calculate_boundary_full_spaces(m, prior):
    """Coupled boundary comparison on identical rows; no sampled upper bound."""
    started, q = time.monotonic(), m-1
    times = [(6**(t-1),3**(t-1)) for t in range(1,m+1)]
    special = times[:-1]+[(0,times[-1][1])]
    tables, old_tables = tables_at(special), tables_at(times[:-1])
    zero, N = larger_columns(m)
    inherited, _ = larger_columns(q)
    new = new_columns(m)
    new_to_zero, zero_to_N = inclusion_maps(m,new,zero,N)
    zero_indices = {json.dumps(c,sort_keys=True): i for i,c in enumerate(zero)}
    inherited_indices = [zero_indices[json.dumps(c,sort_keys=True)] for c in inherited]
    assert [zero[i] for i in inherited_indices] == inherited
    points, rejected = points_off_poles([tables],len(N)+12)
    zero_matrix, Nmatrix, inherited_matrix, combined_matrix, denominators = [], [], [], [], []
    inherited_append_checks = 0
    for point_index, X in enumerate(points):
        values, _, _, denoms = evaluator(tables,X)
        zrow = [v[2]*inverse(X[2]) % P for v in values(zero)]
        Nrow = [v[2]*inverse(X[2]) % P for v in values(N)]
        assert combine_values(Nrow,zero_to_N) == zrow
        inherited_row = [zrow[i] for i in inherited_indices]
        new_row = combine_values(zrow,new_to_zero)
        assert new_row == [v[2]*inverse(X[2]) % P for v in values(new)]
        if point_index < 3:
            old_values, _, _, _ = evaluator(old_tables,X)
            old_row = [v[2]*inverse(X[2]) % P for v in old_values(inherited)]
            v = special[-1][1]
            mu = v*X[0]*X[2]*inverse((X[0]+v*X[2])*(X[0]+2*v*X[2])) % P
            assert inherited_row == [mu*x % P for x in old_row]
            inherited_append_checks += len(inherited)
        zero_matrix.append(zrow)
        Nmatrix.append(Nrow)
        inherited_matrix.append(inherited_row)
        combined_matrix.append(inherited_row+new_row)
        denominators.append(denoms)
    zero_cert = incoming.matrix_certificate(zero_matrix)
    Ncert = incoming.matrix_certificate(Nmatrix)
    inherited_cert = incoming.matrix_certificate(inherited_matrix)
    combined_cert = incoming.matrix_certificate(combined_matrix)
    zrank, Nrank, oldrank, combinedrank = [certificate['rank_certificate']['rank']
                                         for certificate in (zero_cert,Ncert,inherited_cert,combined_cert)]
    assert oldrank <= combinedrank <= zrank <= Nrank
    assert combinedrank <= oldrank+4*q
    saved_old_rank = None
    if prior is not None:
        if q == 2:
            saved_old_rank = prior['base']['certificate']['rank_certificate']['rank']
        else:
            oldcase = next(case for case in prior['cases'] if case['m'] == q)
            saved_old_rank = oldcase['larger_spaces']['zero_prefix_certificate']['rank_certificate']['rank']
    result = dict(m=m, prime=P, G=G, positive_reference_time_factors=times,
                  special_time_factors=special, point_count=len(points), ordinary_points=points,
                  rejected_points=rejected, ordinary_denominators=denominators,
                  all_recorded_denominators_are_units=True,
                  zero_prefix_columns=zero, N_columns=N,
                  inherited_zero_prefix_columns=inherited, selected_new_columns=new,
                  inherited_indices_in_full_zero_prefix=inherited_indices,
                  new_columns_in_full_zero_prefix_terms=new_to_zero,
                  zero_prefix_in_N_terms=zero_to_N,
                  original_source_coefficient_inclusions_verified=True,
                  all_observed_coefficient_inclusions_verified=True,
                  inherited_scalar_append_checks=inherited_append_checks,
                  full_zero_prefix_matrix=zero_matrix, full_N_matrix=Nmatrix,
                  inherited_zero_prefix_matrix=inherited_matrix,
                  inherited_plus_selected_new_matrix=combined_matrix,
                  full_zero_prefix_certificate=zero_cert, full_N_certificate=Ncert,
                  inherited_zero_prefix_certificate=inherited_cert,
                  inherited_plus_selected_new_certificate=combined_cert,
                  observed_full_zero_prefix_gain=zrank-oldrank,
                  observed_selected_new_gain=combinedrank-oldrank,
                  observed_directions_beyond_selected_extension=zrank-combinedrank,
                  saved_old_positive_sample_rank=saved_old_rank,
                  scope='All four ranks use identical ordinary-point rows. They are exact finite observation ranks and nonzero minor certificates, not upper bounds on the rational-function spaces or a proof of forced boundary rank loss.',
                  elapsed_seconds=time.monotonic()-started)
    print(json.dumps(dict(m=m, points=len(points), inherited_rank=oldrank,
                          inherited_plus_selected_rank=combinedrank,
                          full_zero_prefix_rank=zrank, full_N_rank=Nrank,
                          selected_gain=combinedrank-oldrank, full_zero_prefix_gain=zrank-oldrank,
                          directions_beyond_selected_extension=zrank-combinedrank,
                          elapsed_seconds=result['elapsed_seconds'])),flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--boundary-full-spaces',action='store_true',
                        help='Run only the focused m=3,...,6 full-space boundary comparison; retain existing core results when --output exists.')
    args = parser.parse_args()
    prior = (json.loads(args.output.read_text())
             if args.boundary_full_spaces and args.output and args.output.exists() else None)
    started, cases, limitation, base = time.monotonic(), [], None, None

    def guard(_signal, _frame):
        if time.monotonic()-started >= 28 or incoming.maximum_rss_bytes() >= 95*1024**2:
            raise TimeoutError('28-second / 95 MiB guard')

    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    try:
        if args.boundary_full_spaces:
            for m in (3,4,5,6):
                cases.append(calculate_boundary_full_spaces(m,prior))
        else:
            base = base_check()
            print(json.dumps(dict(base_integer_determinant=base['integer_determinant'], base_rank=3)),flush=True)
            for m in (2,3,4,5,6):
                cases.append(calculate(m))
    except TimeoutError as error:
        limitation = str(error)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    stats = dict(elapsed_seconds=time.monotonic()-started,
                 maximum_rss_bytes=incoming.maximum_rss_bytes(),bounded_limitation=limitation)
    if args.boundary_full_spaces:
        result = prior if prior is not None else {}
        result['boundary_full_space_followup'] = dict(
            status='Finite coupled full-space comparison at u_last=0.',
            scope='Only m=3,...,6 at recorded fixtures; sampled deficiencies do not prove rational-function upper bounds.',
            cases=cases,**stats)
    else:
        result = dict(status='Exact actual-source base and append controls with finite zero-prefix family certificates.',
                      scope='The recursive ranks concern only m=2,...,6 at recorded fixtures. Boundary restrictions and larger-space observations are combined before ranking; no ranks of overlapping channels are added.',
                      base=base,cases=cases,**stats)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(stats),flush=True)


if __name__ == '__main__':
    main()
