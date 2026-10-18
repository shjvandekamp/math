#!/usr/bin/env python3
"""Targeted finite-field test of the auxiliary U_tA feedback support.

U_tA=F_(t,r,A,0)/A_t(A,0)-c_tA*F_r0, r=min(old blocks except t),
with c_tA from H4 and F_r0=E_r0+sum_b F_(r,s,0,b).
For E_r0 the extended J and T values are both -1 at ALL THREE
output rows (r,0,d), hence B(E_r0)=0. Binary rows mean d=1,2,
including every old-line state. This is a finite test, not a theorem.

Run:
  nice -n 19 python3 exploration/source24_auxiliary_feedback.py --output exploration/source24-auxiliary-feedback-results.json
"""

import argparse
import json
from pathlib import Path
import signal
import time

import source24_odd_incoming as incoming


P, G = incoming.P, incoming.G


def surviving_entry_formula(m, times, A, actual):
    """Independently evaluate U4/U5 at two projective representatives."""
    first, last = 2, m + 1
    delta = (G[1][1] * G[2][2] - G[2][1] * G[1][2]) % P
    z = -A[first][0][1] * pow(A[first][0][2], -1, P) % P
    checks = []
    for scale in (1, 7):
        X = [0, scale, scale * z % P]
        assert incoming.residue.dot(A[first][0], X, P) == 0
        determinants, ratios, theta_checks = {}, {}, []
        for t in range(first + 1, last + 1):
            K = incoming.residue.ordinary_kernel(A, t, X, P)
            d = (K[1][1] * K[2][2] - K[1][2] * K[2][1]) % P
            L1, L2 = (incoming.residue.dot(A[t][a], X, P) for a in (1, 2))
            theta = (pow(L1, -1, P) - pow(L2, -1, P)) % P
            ratio = theta * pow(d, -1, P) % P
            u, v = times[t - 2]
            closed = pow(delta, -1, P) * (
                (G[2][1] - G[1][1]) * pow(v * X[2] % P, -1, P)
                + (G[2][2] - G[1][2]) * pow(u * X[1] % P, -1, P)) % P
            assert ratio == closed
            determinants[t], ratios[t] = d, ratio
            theta_checks.append(dict(block=t, d=d, theta=theta, theta_over_d=ratio,
                                     U5_closed_form=closed, equal=True))
        product = 1
        for t in range(first + 1, last):
            product = product * determinants[t] % P
        difference = (ratios[last - 1] - ratios[last]) % P
        residue_component = A[first][0][1] * X[1] % P
        expected = [X[a] * pow(incoming.residue.dot(A[last][a], X, P), -1, P)
                    * residue_component * product * difference % P for a in range(3)]
        assert expected == actual
        checks.append(dict(projective_scale=scale, point_mod_prime=X,
                           first_residue_coordinate_1=residue_component,
                           middle_determinant_product=product, last_ratio_difference=difference,
                           U4_predicted_entries_A0_A1_A2=expected, U5_checks=theta_checks))
    return dict(delta=delta, actual_H2_entries_A0_A1_A2=actual,
                sign_and_U4_formula_verified=True, U5_closed_form_verified=True,
                projective_rescaling_verified=True, representatives=checks)


def check_case(m, mode):
    times = incoming.sparse.factors(m, mode)
    A = [[list(row) for row in G] for _ in range(2)] + incoming.sparse.coefficient_tables(G, times)
    B, J, T = incoming.feedback_limit(m, A)
    old = list(range(2, m + 2))
    _, pair_labels = incoming.schur.canonical_labels(m + 2)
    pair_index = {label: i for i, label in enumerate(pair_labels)}
    row_labels = [(u, c, d) for u in old for c in range(3) for d in range(3)]
    U_labels = [(t, a) for t in old for a in range(3)]
    BU, JU, TU = [[] for _ in row_labels], [[] for _ in row_labels], [[] for _ in row_labels]
    constants = []
    for t, a in U_labels:
        r = min(u for u in old if u != t)
        s = min(u for u in old if u != r)
        X = [0, A[r][0][2], -A[r][0][1] % P]
        K = incoming.residue.ordinary_kernel(A, t, X, P)
        determinant = (K[1][1] * K[2][2] - K[1][2] * K[2][1]) % P
        c_tA = X[a] * pow(incoming.residue.dot(A[t][a], X, P) * determinant % P, -1, P) % P if a else 0
        constants.append(dict(t=t, A=a, r=r, s=s, c_tA=c_tA))
        first = pair_index[t, r, a, 0]
        summed = [pair_index[r, s, 0, b] for b in range(3)]
        inverse_A = pow(A[t][a][0], -1, P)
        for i, (u, state, d) in enumerate(row_labels):
            BU[i].append((B[i][first] * inverse_A - c_tA * sum(B[i][j] for j in summed)) % P)
            E_correction = c_tA if (u, state) == (r, 0) else 0
            JU[i].append((J[i][first] * inverse_A - c_tA * sum(J[i][j] for j in summed) + E_correction) % P)
            TU[i].append((T[i][first] * inverse_A - c_tA * sum(T[i][j] for j in summed) + E_correction) % P)
    assert BU == incoming.schur.matrix_difference(JU, TU)
    nonzero = [dict(row=row_labels[i], column=U_labels[j], value=value)
               for i, row in enumerate(BU) for j, value in enumerate(row) if value]
    exceptions = [entry for entry in nonzero if entry['column'][0] < old[-1]
                  or entry['row'] != (old[0], 0, 0) or entry['column'][1] == 0]
    binary_rows = [i for i, (_, _, d) in enumerate(row_labels) if d in (1, 2)]
    binary_J = [[*JU[i]] for i in binary_rows]
    binary_T = [[*TU[i]] for i in binary_rows]
    surviving_row = row_labels.index((old[0], 0, 0))
    surviving_entries = [BU[surviving_row][U_labels.index((old[-1], a))] for a in range(3)]
    closed_check = surviving_entry_formula(m, times, A, surviving_entries)
    result = dict(m=m, time_fixture=mode, prime=P, G=G, old_time_factors=times,
                  feedback_row_labels=row_labels, U_column_labels=U_labels, H4_constants=constants,
                  B_U=incoming.matrix_certificate(BU),
                  extended_J_U=incoming.matrix_certificate(JU), extended_T_U=incoming.matrix_certificate(TU),
                  binary_J_U=incoming.matrix_certificate(binary_J), binary_T_U=incoming.matrix_certificate(binary_T),
                  exact_nonzero_feedback_entries=nonzero,
                  conjectured_support_holds=(not exceptions), support_counterexamples=exceptions,
                  binary_J_identically_zero=(not any(x for row in binary_J for x in row)),
                  binary_T_identically_zero=(not any(x for row in binary_T for x in row)),
                  extended_B_equals_J_minus_T_verified=True,
                  U4_U5_surviving_entry_check=closed_check,
                  E_convention='J(E_r0)=T(E_r0)=-1 for every row(r,0,d), d=0,1,2; B(E_r0)=0.',
                  scope='Four finite common-G fixtures; these support or refute the proposed cancellation at those points only.')
    print(json.dumps(dict(m=m, time_fixture=mode, B_rank=result['B_U']['rank_certificate']['rank'],
                          support_holds=not exceptions, nonzero_entries=nonzero,
                          binary_J_zero=result['binary_J_identically_zero'], binary_T_zero=result['binary_T_identically_zero'],
                          U4_U5_and_projective_scale_verified=True,
                          first_counterexample=exceptions[0] if exceptions else None)), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('28-second auxiliary-feedback cutoff.')
        if incoming.maximum_rss_bytes() >= 95 * 1024**2:
            raise TimeoutError('95MiB auxiliary-feedback RSS guard.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    try:
        cases = [check_case(m, mode) for m in (3, 5) for mode in ('economic', 'independent')]
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result = dict(status='External exact modular support diagnostic; no uniform theorem.',
                  elapsed_seconds=time.monotonic() - started,
                  maximum_rss_bytes=incoming.maximum_rss_bytes(), cases=cases)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
