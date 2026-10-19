#!/usr/bin/env python3
"""l-adic Smith exponents of an exact rational matrix (python-flint fmpq_mat).

smith_exponents(M, l, K): elementary-divisor valuations of M over the local
ring Z_(l), computed by full minimal-valuation pivoting modulo l^K.  With
epsilon = l these are the epsilon-orders of the Smith form of the generic
Laurent matrix (barring accidental cancellation mod l).  Exponents >= K are
reported as K (insufficient precision).
"""
import flint


def _val(x, l):
    v = 0
    while x % l == 0:
        x //= l
        v += 1
    return v


def smith_exponents(M, l, K=40):
    nr, nc = M.nrows(), M.ncols()
    # common scaling to make entries l-integral: multiply by l^m
    minv = None
    entries = [[M[i, j] for j in range(nc)] for i in range(nr)]
    for row in entries:
        for x in row:
            if x != 0:
                num, den = int(x.p), int(x.q)
                v = _val(abs(num), l) - _val(den, l)
                minv = v if minv is None else min(minv, v)
    if minv is None:
        return [K] * min(nr, nc)
    m = -minv
    mod = l ** K
    A = []
    for row in entries:
        r = []
        for x in row:
            if x == 0:
                r.append(0)
                continue
            num, den = int(x.p), int(x.q)
            vd = _val(den, l)
            den_u = den // l ** vd
            # x * l^m = num * l^(m - vd) / den_u
            e = m - vd
            val = num * pow(l, e, mod) if e >= 0 else None
            if val is None:
                raise ValueError('scaling error')
            r.append(val * pow(den_u, -1, mod) % mod)
        A.append(r)
    exps = []
    rows = list(range(nr))
    cols = list(range(nc))
    while rows and cols:
        best = None
        for i in rows:
            Ai = A[i]
            for j in cols:
                x = Ai[j]
                if x:
                    v = _val(x, l)
                    if best is None or v < best[0]:
                        best = (v, i, j)
                        if v == 0:
                            break
            if best is not None and best[0] == 0:
                break
        if best is None or best[0] >= K:
            exps.extend([K] * min(len(rows), len(cols)))
            break
        v, pi, pj = best
        exps.append(v)
        piv = A[pi][pj]
        unit = piv // l ** v
        inv = pow(unit, -1, mod)
        rows.remove(pi)
        cols.remove(pj)
        prow = A[pi]
        for i in rows:
            x = A[i][pj]
            if x:
                # factor = x / piv = (x / l^v) * inv  (x divisible by l^v)
                f = (x // l ** v) * inv % mod
                Ai = A[i]
                for j in cols:
                    if prow[j]:
                        Ai[j] = (Ai[j] - f * prow[j]) % mod
                Ai[pj] = 0
    exps = sorted(e - m for e in exps)
    return exps


def summarize(exps):
    from collections import Counter
    c = Counter(exps)
    return ', '.join(f'{k}:{c[k]}' for k in sorted(c))
