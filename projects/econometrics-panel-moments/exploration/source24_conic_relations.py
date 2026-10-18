#!/usr/bin/env python3
"""Exact three-block conic source relations using small Laurent dictionaries.

The variables are (p1,p2,p3,k,h), with q_t=(p_t,h*p_t,k*p_t).
Source coefficients are supported on shared/divergent states 0 and 2.
For each fixed assignment of states to the three blocks, sum all six
actual generation orders. Their denominator and X-state factors coincide;
the remaining ordered-path coefficient is
  sum_(t,s,r) c_(t,s,a_t,a_s) q_(t,a_t)^a_s q_(s,a_s)^a_r q_(r,a_r)^d.
Check these polynomials over Z[p1^+-1,p2^+-1,p3^+-1,k,h], not by sampling.

The first two combinations have only one possible output component in
both their prefix and chain terms; the actual zero row sum makes them
rationally zero. The third chain term has only output 1, while its prefix
has only outputs 0 and 2. The row sum therefore makes the third complete
combination a single-pole row, proving its double residues vanish.

Finite-field checks compare actual ordered source residues with the
existing source24_residue implementation at three conic fixtures, check
coefficient rank three, and evaluate the actual full source rows. No
all-length or general rank assertion is made.

Reproduce:
  nice -n 19 python3 exploration/source24_conic_relations.py --output exploration/source24-conic-relations-results.json
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming


P = incoming.P
residue, schur = incoming.residue, incoming.schur
VARIABLES = ('p1', 'p2', 'p3', 'k', 'h')
ZERO_EXPONENT = (0,) * len(VARIABLES)
PERMUTATIONS = tuple(itertools.permutations(range(3)))
POINTS = ((1, 2, 3), (2, 3, 5), (3, 5, 7))


def monomial(exponent=ZERO_EXPONENT, coefficient=1):
    return {tuple(exponent): coefficient} if coefficient else {}


def variable(index, exponent=1):
    powers = [0] * len(VARIABLES)
    powers[index] = exponent
    return monomial(powers)


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] = result.get(exponent, 0) + coefficient
            if not result[exponent]:
                del result[exponent]
    return result


def scale(scalar, polynomial):
    return {exponent: scalar * coefficient for exponent, coefficient in polynomial.items()
            if scalar * coefficient}


def multiply(*polynomials):
    result = monomial()
    for polynomial in polynomials:
        product = {}
        for left, a in result.items():
            for right, b in polynomial.items():
                exponent = tuple(x + y for x, y in zip(left, right))
                product[exponent] = product.get(exponent, 0) + a * b
        result = {exponent: coefficient for exponent, coefficient in product.items() if coefficient}
    return result


def power(polynomial, exponent):
    assert exponent >= 0
    return multiply(*(polynomial for _ in range(exponent)))


def serialize(polynomial):
    return [[list(exponent), coefficient] for exponent, coefficient in sorted(polynomial.items())]


def evaluate(polynomial, values):
    assert len(values) == len(VARIABLES)
    total = 0
    for exponent, coefficient in polynomial.items():
        term = coefficient
        for value, e in zip(values, exponent):
            term = term * pow(value, e, P) % P
        total = (total + term) % P
    return total


def epsilon(order):
    return (-1) ** sum(order[i] > order[j] for i in range(3) for j in range(i + 1, 3))


def q(t, state):
    assert state in (0, 1, 2)
    return multiply(variable(t), monomial() if state == 0 else variable(4 if state == 1 else 3))


def source_coefficients(t, s, a, b):
    """Return all three proposed coefficient polynomials, including epsilon."""
    if a not in (0, 2) or b not in (0, 2):
        return {}, {}, {}
    r = next(u for u in range(3) if u not in (t, s))
    pt, ps, pr, k = variable(t), variable(s), variable(r), variable(3)
    Pi = multiply(*(variable(u) for u in range(3)))
    first = {(0, 0): scale(-1, pt), (0, 2): pr,
             (2, 0): multiply(k, Pi), (2, 2): scale(-1, multiply(ps, power(pr, 2)))}[a, b]
    second = {(0, 0): multiply(pt, variable(r, -1)), (0, 2): scale(-1, k),
              (2, 0): scale(-1, multiply(power(k, 2), pt, ps)),
              (2, 2): multiply(power(k, 2), ps, pr)}[a, b]
    sign = epsilon((t, s, r))
    first, second = scale(sign, first), scale(sign, second)
    third = multiply(first, add(q(t, a), q(s, b)))
    return first, second, third


SYMBOLIC_COLUMNS = [(t, s, a, b) for t in range(3) for s in range(3) if t != s
                    for a in range(3) for b in range(3)]
COEFFICIENTS = {label: source_coefficients(*label) for label in SYMBOLIC_COLUMNS}


def ordered_path_coefficient(family, states, output):
    terms = []
    for t, s, r in PERMUTATIONS:
        a, b, c = states[t], states[s], states[r]
        terms.append(multiply(COEFFICIENTS[t, s, a, b][family],
                              power(q(t, a), b), power(q(s, b), c), power(q(r, c), output)))
    return add(*terms)


def prefix_coefficient(family, t, a, output):
    # The omitted factor Xa*q_(t,a)^output*Xoutput/L_(t,a) is independent of s.
    return add(*(COEFFICIENTS[t, s, a, output][family] for s in range(3) if s != t))


def symbolic_checks():
    zero_outputs = ((0, 1), (1, 2), (0, 2))
    remaining_outputs = (2, 0, 1)
    path_checks, prefix_checks, records = 0, 0, []
    for family in range(3):
        remaining = []
        for states in itertools.product(range(3), repeat=3):
            for output in zero_outputs[family]:
                value = ordered_path_coefficient(family, states, output)
                assert not value, ('Proposed path identity failed.', family + 1, states, output, serialize(value))
                path_checks += 1
            value = ordered_path_coefficient(family, states, remaining_outputs[family])
            if value:
                remaining.append(dict(states=states, coefficient=serialize(value)))
        # Families 1/2 have only prefix output 2/0. Family 3 has no prefix output 1.
        forbidden_prefix = ((0, 1), (1, 2), (1,))[family]
        for t in range(3):
            for a in range(3):
                for output in forbidden_prefix:
                    value = prefix_coefficient(family, t, a, output)
                    assert not value, ('Proposed prefix identity failed.', family + 1, t, a, output, serialize(value))
                    prefix_checks += 1
        records.append(dict(family=family + 1, zero_chain_outputs=zero_outputs[family],
                            remaining_chain_output=remaining_outputs[family],
                            nonzero_remaining_path_coefficients=len(remaining),
                            remaining_path_coefficients=remaining,
                            zero_prefix_outputs=forbidden_prefix))
    coefficient_data = [dict(label=label, polynomials=[serialize(poly) for poly in COEFFICIENTS[label]])
                        for label in SYMBOLIC_COLUMNS if any(COEFFICIENTS[label])]
    return dict(coefficient_ring='Z[p1^+-1,p2^+-1,p3^+-1,k,h]', variables=VARIABLES,
                state_parameters='q_t=(p_t,h*p_t,k*p_t)',
                ordered_path_vanishing_identities=path_checks,
                prefix_vanishing_identities=prefix_checks,
                all_27_fixed_block_state_assignments_checked=True,
                coefficient_sha256=hashlib.sha256(json.dumps(coefficient_data, sort_keys=True).encode()).hexdigest(),
                coefficient_polynomials=coefficient_data, families=records,
                rational_function_consequence='Families 1 and 2 have only one possible output component; the zero row sum of every actual source row makes both combinations identically zero.',
                pair_residue_consequence='Family 3 has chain output only 1 and prefix outputs only 0 and 2. Zero row sum makes it (S0,-S0-S2,S2), where S is the single-pole prefix, so every double residue vanishes.')


def finite_coefficients(alpha, times):
    values = [alpha[0] * b % P for b in times]
    values += [alpha[2] * pow(alpha[0], -1, P) % P, alpha[1] * pow(alpha[0], -1, P) % P]
    return [[evaluate(poly, values) for poly in COEFFICIENTS[label]] for label in SYMBOLIC_COLUMNS], values


def direct_pair_checks(A, O, C):
    rows, columns = schur.canonical_labels(5)
    checks = 0
    for row in range(0, len(rows), 2):
        u, v, c, d, _ = rows[row]
        X = residue.cross(A[u][c], A[v][d], P)
        U = [A[u][c][j] * X[j] % P for j in range(3)]
        V = [A[v][d][j] * X[j] % P for j in range(3)]
        kernels = {}
        for t in range(2, 5):
            if t == u:
                kernels[t] = [U[:] if a == c else [0, 0, 0] for a in range(3)]
            elif t == v:
                kernels[t] = [V[:] if a == d else [0, 0, 0] for a in range(3)]
            else:
                kernels[t] = residue.ordinary_kernel(A, t, X, P)
        products = {(t, s): residue.word_product(kernels, [s] + [r for r in range(2, 5) if r not in (t, s)], P)
                    for t in range(2, 5) for s in range(2, 5) if s != t}
        raw_rows = [[], [], []]
        for j, (t, s, a, b) in enumerate(columns):
            scalar = -X[a] * A[t][a][b] * X[b] % P
            if (t == u and a != c) or (t == v and a != d):
                scalar = 0
            elif t not in (u, v):
                scalar = scalar * pow(residue.dot(A[t][a], X, P), -1, P) % P
            vector = [scalar * value % P for value in products[t, s][b]]
            existing = [(O[row][j] * U[e] + O[row + 1][j] * V[e]) % P for e in range(3)]
            assert vector == existing, ('Direct ordered pair residue differs from existing O.', u, v, c, d, t, s, a, b)
            assert sum(vector) % P == 0
            for e in range(3):
                raw_rows[e].append(vector[e])
            checks += 1
        assert schur.matrix_product(raw_rows, C) == [[0] * 3 for _ in range(3)]
    return checks


def ordinary_checks(A, C):
    _, columns = schur.canonical_labels(5)
    records = []
    for X in POINTS:
        kernels = {t: residue.ordinary_kernel(A, t, X, P) for t in range(2, 5)}
        products = {(t, s): residue.word_product(kernels, [s] + [r for r in range(2, 5) if r not in (t, s)], P)
                    for t in range(2, 5) for s in range(2, 5) if s != t}
        source, prefix = [[], [], []], [[], [], []]
        for t, s, a, b in columns:
            scalar = X[a] * kernels[t][a][b] % P
            vector = [scalar * (int(b == d) - products[t, s][b][d]) % P for d in range(3)]
            assert sum(vector) % P == 0
            for d in range(3):
                source[d].append(vector[d])
                prefix[d].append(scalar * int(b == d) % P)
        full, S = schur.matrix_product(source, C), schur.matrix_product(prefix, C)
        assert all(full[d][j] == 0 for d in range(3) for j in (0, 1))
        assert S[0][0] == S[1][0] == S[1][1] == S[2][1] == S[1][2] == 0
        third = [full[d][2] for d in range(3)]
        expected = [S[0][2], -(S[0][2] + S[2][2]) % P, S[2][2]]
        assert third == expected
        records.append(dict(point=X, first_two_full_source_combinations_zero=True,
                            third_full_source_combination=third, third_nonzero=bool(any(third)),
                            third_single_pole_prefix_formula_verified=True))
    assert any(record['third_nonzero'] for record in records), 'Third source combination vanishes at every selected ordinary point.'
    return records


def finite_case(alpha, times):
    started = time.monotonic()
    A = [[[1, a, a * a] for a in alpha] for _ in range(2)]
    A += [[[1, alpha[a] * b % P, pow(alpha[a] * b, 2, P)] for a in range(3)] for b in times]
    C, values = finite_coefficients(alpha, times)
    _, columns = schur.canonical_labels(5)
    assert columns == [(t + 2, s + 2, a, b) for t, s, a, b in SYMBOLIC_COLUMNS]
    O, geometry = residue.residue_matrix(5, A, P)
    actual_product = schur.matrix_product(O, C)
    assert actual_product == [[0] * 3 for _ in O]
    coefficient_certificate = incoming.matrix_certificate(C)
    assert coefficient_certificate['rank_certificate']['rank'] == 3
    direct_checks = direct_pair_checks(A, O, C)
    ordinary = ordinary_checks(A, C)
    result = dict(alpha=alpha, times=times, prime=P, formal_variable_values=values,
                  actual_source_geometry=geometry,
                  actual_source_matrix_sha256=residue.matrix_hash(O),
                  coefficient_matrix=coefficient_certificate, coefficient_columns=C,
                  actual_source_residue_product_is_zero=True,
                  direct_ordered_pair_vectors_compared_with_existing_O=direct_checks,
                  ordinary_source_checks=ordinary, elapsed_seconds=time.monotonic() - started)
    print(json.dumps(dict(alpha=alpha, times=times, coefficient_rank=3, actual_residues_zero=True,
                          direct_pair_vector_checks=direct_checks,
                          third_ordinary_nonzero=any(x['third_nonzero'] for x in ordinary),
                          seconds=result['elapsed_seconds'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started, cases = time.monotonic(), []

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second conic-relations cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024 ** 2:
            raise TimeoutError('95 MiB conic-relations RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    limitation, symbolic = None, None
    try:
        symbolic = symbolic_checks()
        for alpha, times in (((1, 2, 3), (2, 5, 11)), ((1, 2, 4), (8, 64, 512)), ((2, 5, 9), (2, 7, 19))):
            cases.append(finite_case(alpha, times))
    except TimeoutError as error:
        limitation = str(error)
        print(json.dumps(dict(bounded_limitation=limitation)), flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='Exact symbolic ordered-path identities plus finite checks against actual source formulas; no general rank theorem.',
                  scope='Three conic blocks only. Two rational-zero source combinations and one combination with only single poles, using the exact zero row sum of actual sources.',
                  symbolic=symbolic, finite_cases=cases,
                  elapsed_seconds=time.monotonic() - started, maximum_rss_bytes=incoming.maximum_rss_bytes(),
                  bounded_limitation=limitation)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
