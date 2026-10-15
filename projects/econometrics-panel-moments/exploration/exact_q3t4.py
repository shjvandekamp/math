#!/usr/bin/env python3
"""Exact discovery certificates, NOT a substitute for the Lean proof.

Python standard library only. Integer coefficient expansion, integer source
moment numerators, finite-field pivot selection, Bareiss integer determinants.
Time and outcome labels in this program start at zero; the paper starts at one.
"""
import argparse
import hashlib
import itertools as it
import json
import math
from pathlib import Path

Q, T = 3, 4
PATHS = list(it.product(range(Q), repeat=T))
MONOMIALS = [(a, b) for a in range(11) for b in range(11 - a)]
G = [[1, 1, 1], [1, 2, 4], [1, 4, 16]]
# Scalar x_t=3(t+1)log(2); beta=(0,1,2); gamma_qr=q*r*log(2).
PI = [[[G[q][r] * (1, 2 ** (3*(t + 1)), 2 ** (6*(t + 1)))[q]
        for r in range(Q)] for q in range(Q)] for t in range(T)]


def mul(p, q):
    ans = {}
    for (a, b), x in p.items():
        for (c, d), y in q.items():
            ans[a + c, b + d] = ans.get((a + c, b + d), 0) + x * y
    return {e: c for e, c in ans.items() if c}


def coefficient_matrix(pi, initial=0):
    columns, scales = [], []
    for y in PATHS:
        p = {(y.count(1), y.count(2)): 1}
        a = pi[0][y[0]][initial]
        for t in range(1, T):
            a *= pi[t][y[t]][y[t - 1]]
            for r in range(Q):
                if r != y[t - 1]:
                    p = mul(p, {(0, 0): pi[t][0][r],
                                (1, 0): pi[t][1][r], (0, 1): pi[t][2][r]})
        columns.append([p.get(e, 0) for e in MONOMIALS])
        scales.append(a)
    # C0 contains F_y/A_y; the actual coefficient matrix is C0 diag(A_y).
    return [list(r) for r in zip(*columns)], scales


def source_indices():
    ans = []
    for j in range(T - 2):
        for shared in it.combinations(range(T - 1), j):
            remaining = sorted(set(range(T - 1)) - set(shared))
            s1 = remaining[0]
            for s2 in remaining[1:]:
                tail = sorted(set(remaining) - {s1, s2})
                tau1 = list(shared) + [s1] + tail + [s2, T - 1]
                tau2 = list(shared) + [s2] + tail + [s1, T - 1]
                for values in it.product(range(Q), repeat=j + 1):
                    ans.append(dict(j=j, shared=shared, s1=s1, s2=s2,
                                    values=values, tau1=tau1, tau2=tau2))
    return ans


def transformed_numerator(pi, y, tau, initial):
    # sigma(T)=tau(1), sigma(tau(k))=tau(k+1).
    sigma = dict(zip([T - 1] + tau[:-1], tau))
    ans = pi[0][y[sigma[T - 1]]][initial]
    for t in range(1, T):
        ans *= pi[t][y[sigma[t - 1]]][y[t - 1]]
    return ans


def moment_numerators(pi, initial=0):
    # K=M diag(A_y); row scaling is NOT being used here.
    ans = []
    for idx in source_indices():
        row = []
        for y in PATHS:
            if any(y[t] != q for t, q in zip(idx['shared'], idx['values'][1:])):
                row.append(0)
                continue
            q = idx['values'][0]
            row.append((transformed_numerator(pi, y, idx['tau1'], initial)
                        if y[idx['s1']] == q else 0)
                       - (transformed_numerator(pi, y, idx['tau2'], initial)
                          if y[idx['s2']] == q else 0))
        ans.append(row)
    return ans


def pivot_minor(a, p=1000003):
    """Select a fixed integer minor using modular elimination; not final proof."""
    a = [[x % p for x in row] for row in a]
    ids = list(range(len(a)))
    rows, cols = [], []
    r = 0
    for c in range(len(a[0])):
        pick = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pick is None:
            continue
        a[r], a[pick] = a[pick], a[r]
        ids[r], ids[pick] = ids[pick], ids[r]
        rows.append(ids[r]); cols.append(c)
        inv = pow(a[r][c], -1, p)
        for i in range(r + 1, len(a)):
            f = a[i][c] * inv % p
            if f:
                a[i][c:] = [(x - f * y) % p for x, y in zip(a[i][c:], a[r][c:])]
        r += 1
        if r == len(a):
            break
    return rows, cols


def bareiss(a):
    """Exact integer determinant, checking every division for remainder zero."""
    a = [row[:] for row in a]
    n, prev, sign = len(a), 1, 1
    for k in range(n - 1):
        if not a[k][k]:
            j = next((j for j in range(k + 1, n) if a[j][k]), None)
            if j is None:
                return 0
            a[k], a[j] = a[j], a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                quotient, remainder = divmod(numerator, prev)
                if remainder:
                    raise ArithmeticError('Bareiss division was not exact')
                a[i][j] = quotient
            a[i][k] = 0
        prev = pivot
    return sign * a[-1][-1]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def geometry(pi):
    lines = {(t, r): [pi[t][q][r] for q in range(Q)]
             for t in range(1, T) for r in range(Q)}
    points = []
    for t in range(1, T):
        for a, b in it.combinations(range(Q), 2):
            points.append(dict(t=t, kind='pair', labels=[a, b],
                               point=cross(lines[t, a], lines[t, b])))
        for a in range(Q):
            e = [int(q == a) for q in range(Q)]
            points.append(dict(t=t, kind='diagonal', labels=[a],
                               point=cross(e, lines[t, a])))
    # Homogenize separators with dot(P,eta): nonzero at P over the reals.
    values = []
    for target in points:
        t = target['t']; row = []
        for point in points:
            z = point['point']
            val = math.prod(dot(l, z) for (s, r), l in lines.items() if s != t)
            if target['kind'] == 'pair':
                a, b = target['labels']; c = 3 - a - b
                val *= dot(lines[t, c], z) * z[a] * z[b]
                val *= dot(target['point'], z)
            else:
                a, = target['labels']
                val *= math.prod(dot(lines[t, b], z) for b in range(Q) if b != a)
                val *= dot(target['point'], z) ** 2
            row.append(val)
        values.append(row)
    assert all(values[i][j] == 0 for i in range(18) for j in range(18) if i != j)
    assert all(values[i][i] != 0 for i in range(18))
    evals = [[p['point'][0] ** (10-a-b) * p['point'][1] ** a * p['point'][2] ** b
              for a, b in MONOMIALS] for p in points]
    return points, values, evals


def certificate(a):
    rows, cols = pivot_minor(a)
    minor = [[a[i][j] for j in cols] for i in rows]
    det = bareiss(minor)
    assert det != 0
    return dict(size=len(rows), rows=rows, columns=cols, determinant=str(det))


def run():
    c0, scales = coefficient_matrix(PI)
    k = moment_numerators(PI)
    assert len(PATHS) == 81 and len(k) == 33 and len(c0) == 66
    assert all(dot(c, m) == 0 for c in c0 for m in k)
    points, separators, evals = geometry(PI)
    assert all(dot(e, col) == 0 for e in evals for col in zip(*c0))
    c_cert, m_cert = certificate(c0), certificate(k)
    assert c_cert['size'] == 48 and m_cert['size'] == 33
    # Check the other two initial states independently. F/A is initial-state free.
    initials = {str(0): m_cert}
    for initial in (1, 2):
        kk = moment_numerators(PI, initial)
        assert all(dot(c, m) == 0 for c in c0 for m in kk)
        initials[str(initial)] = certificate(kk)
        assert initials[str(initial)]['size'] == 33
    return dict(status='exact external discovery, not Lean-verified',
                indexing='zero based, lexicographic paths; monomials (a,b) eta2^a eta3^b',
                G=G, PI=PI, paths=PATHS, monomials=MONOMIALS,
                moment_indices=source_indices(), path_scales=scales,
                coefficient_matrix_scaled=c0, moment_numerators=k,
                coefficient_minor=c_cert, moment_minors_by_initial=initials,
                basepoints=points, separator_diagonal=[separators[i][i] for i in range(18)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    data = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    print(json.dumps(dict(coefficient_minor=result['coefficient_minor']['size'],
                          moment_minor_sizes={k: v['size'] for k, v in result['moment_minors_by_initial'].items()},
                          annihilation='C0 K^T=0 and E C0=0 exactly',
                          basepoint_separators='18 nonzero diagonal entries',
                          certificate_sha256=hashlib.sha256(data.encode()).hexdigest(),
                          formal_status=result['status']), indent=2))
