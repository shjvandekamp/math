#!/usr/bin/env python3
"""Shared tools for the agent_per2_* experiments (E1 induction step in the persistence limit).

Builds on agent_per_lib / agent_per_reduced (normalised families, eps-series mod P at points).

coords_mod(basis, targets, r, e): exact coordinates modulo eps^r of target rows in a
C[[eps]]-lattice basis (rows = eps-series evaluated at points), assuming every target lies in
the lattice and eps^e L_sat ⊆ lattice.  Method: block-Toeplitz system with unknown polynomial
coefficients of degree < e + r, constraints on orders 0..e+r-1 (exact, because the order-m
blocks use both components at 3(m+1)^2 + 5 points; every eps^m-coefficient that occurs has pole
order <= m); coefficients of eps^0..eps^(r-1) are unique because eps^(e+r) L_sat ⊆ eps^r L.
The particular solution read off from the reduced row echelon form (free variables 0) therefore
has the correct low coefficients; the script asserts consistency (targets in the lattice).

System setup: m blocks, newest N = m - 1, old S = {0..N-1}; labels of the normalised DHW family
('E', s, a), ('F', t, s, a, b) and of the normalised standard-tail family ('E', s, a),
('G', t, r, a, b) (agent_per_reduced.normalised_rows; G_{t,N} = B_{t,N}).
What this module does not do: prove anything; all computations are mod P at one random point.
"""
import sys
from pathlib import Path

import flint
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per_lib import P, Q, Model, PointSeries, saturate  # noqa: E402,F401
from agent_per_reduced import normalised_rows  # noqa: E402


def nm(arr):
    return flint.nmod_mat((np.asarray(arr) % P).tolist(), P)


def order_coords(M, mm):
    npts = M // 2
    h = min(npts, 3 * (mm + 1) ** 2 + 5)
    return list(range(h)) + list(range(npts, npts + h))


def shift(rows, k):
    out = np.zeros_like(rows)
    if k > 0:
        out[:, k:, :] = rows[:, :rows.shape[1] - k, :]
    else:
        out[:] = rows
    return out


def coords_mod(basis, targets, r, e):
    """Return gam with shape (r, nb, nt): targets_j = sum_l eps^l sum_i gam[l, i, j] basis_i mod eps^r L."""
    nb, K1, M = basis.shape
    nt = targets.shape[0]
    E = e + r
    assert K1 >= E, 'series precision too low'
    cs = [order_coords(M, mm) for mm in range(E)]
    assert all(len(c) == 2 * (3 * (mm + 1) ** 2 + 5) for mm, c in enumerate(cs)), 'too few points'
    offs = np.concatenate([[0], np.cumsum([len(c) for c in cs])])
    nrow = int(offs[-1])
    A = np.zeros((nrow, nb * E), dtype=np.int64)
    RHS = np.zeros((nrow, nt), dtype=np.int64)
    for mm in range(E):
        r0, r1 = int(offs[mm]), int(offs[mm + 1])
        for l in range(mm + 1):
            A[r0:r1, l * nb:(l + 1) * nb] = basis[:, mm - l, cs[mm]].T
        RHS[r0:r1, :] = targets[:, mm, cs[mm]].T
    Aug = nm(np.hstack([A, RHS]))
    R, rk = Aug.rref()
    Rl = R.tolist()
    ncA = nb * E
    piv = []
    for i in range(rk):
        row = Rl[i]
        for c in range(len(row)):
            if int(row[c]):
                piv.append(c)
                break
    assert all(c < ncA for c in piv), 'inconsistent: some target is not in the lattice'
    pivset = set(piv)
    for l in range(r):
        for i in range(nb):
            assert (l * nb + i) in pivset, 'low coefficient not determined (increase e)'
    sol = np.zeros((ncA, nt), dtype=np.int64)
    for i, c in enumerate(piv):
        sol[c, :] = [int(x) for x in Rl[i][ncA:]]
    # uniqueness of the low coefficients: pivot rows of low variables must not involve free columns
    free = [c for c in range(ncA) if c not in pivset]
    if free:
        fr = np.array(free)
        for i, c in enumerate(piv):
            if c < r * nb:
                rowv = np.array([int(x) for x in Rl[i][:ncA]], dtype=np.int64)
                assert not rowv[fr].any(), 'low coefficients not unique'
    gam = np.zeros((r, nb, nt), dtype=np.int64)
    for l in range(r):
        gam[l] = sol[l * nb:(l + 1) * nb, :]
    return gam % P


class System:
    """Normalised families of an m-block persistence system at one random point."""

    def __init__(self, m, seed, K=None, npts=None, kinds=('F', 'G', 'B')):
        self.m = m
        self.N = m - 1
        self.d = 9 * m * m - 6 * m
        emax = 2 * m + 2
        self.K = K if K is not None else emax + 5
        npts = npts if npts is not None else max(self.d // 2 + 20, 3 * (emax + 3) ** 2 + 10)
        self.model = Model(m, seed=seed, hi=10 ** 6)
        self.ps = PointSeries(self.model, npts, self.K, seed=seed + 1)
        self.lab = {}
        self.rows = {}
        for kind in kinds:
            lab, rows = normalised_rows(self.ps, kind)
            self.lab[kind] = lab
            self.rows[kind] = rows[:, :self.K - 1, :].copy()
        self.pos = {k: {l: i for i, l in enumerate(v)} for k, v in self.lab.items()}

    def emax(self, kind):
        return int(saturate(self.rows[kind], self.K - 2)['shifts'].max())


def coords_peel(basis, targets, r, prec_basis=None):
    """Same output as coords_mod (coefficients eps^0..eps^(r-1) of the coordinates of targets in
    the lattice basis), computed through the tracked saturated basis S = T * basis:
    targets = sum_j beta_j S_j with beta in C[[eps]] (peeled order by order against the
    independent leading rows of S, which lie in W^0, so d/2 + O(1) points suffice), then
    gamma = beta T (T has negative eps-powers down to -max shift).  Asserts that the negative
    powers of gamma vanish (targets in the lattice) and that the precision suffices."""
    nb, K1, M = basis.shape
    nt = targets.shape[0]
    Kb = K1 - 1 if prec_basis is None else prec_basis
    res = saturate(basis[:, :Kb + 1, :].copy(), Kb, track=True)
    S, prec, T, sh = res['S'], res['prec'], res['T'], res['shifts']
    smax = int(sh.max())
    O = r - 1 + smax
    assert int(prec.min()) >= O, f'precision too low: min prec {int(prec.min())} < {O} (raise K)'
    assert targets.shape[1] - 1 >= O
    lead = S[:, 0, :] % P
    Rl, rk = nm(lead).rref()
    assert rk == nb
    Rll = Rl.tolist()
    piv = []
    for i in range(nb):
        for j, x in enumerate(Rll[i]):
            if int(x):
                piv.append(j)
                break
    Linv = nm(lead[:, piv]).inv()                      # nb x nb
    Sp = [nm(S[:, k, :][:, piv]) for k in range(O + 1)]  # S[k] at pivot coords
    beta = []
    for o in range(O + 1):
        resid = nm(targets[:, o, :][:, piv])
        for k in range(1, o + 1):
            resid = resid - beta[o - k] * Sp[k]
        beta.append(resid * Linv)                       # nt x nb
    # T as matrices T_o (nb_S x nb), o from -smax .. maxo
    orders = sorted({o for Tj in T for o in Tj})
    Tm = {}
    for o in orders:
        A = np.zeros((nb, nb), dtype=np.int64)
        for j, Tj in enumerate(T):
            if o in Tj:
                A[j, :] = Tj[o] % P
        Tm[o] = nm(A)
    gam = np.zeros((r, nb, nt), dtype=np.int64)
    zero = nm(np.zeros((nt, nb), dtype=np.int64))
    for l in range(-smax, r):
        acc = zero
        for o in orders:
            q = l - o
            if 0 <= q <= O:
                acc = acc + beta[q] * Tm[o]
        A = np.array(acc.tolist(), dtype=np.int64) % P   # nt x nb
        if l < 0:
            assert not A.any(), f'negative power eps^{l} in coordinates: target not in lattice'
        else:
            gam[l] = A.T
    return gam
