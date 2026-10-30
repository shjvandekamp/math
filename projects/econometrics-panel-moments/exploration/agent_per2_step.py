#!/usr/bin/env python3
"""Task (1): the 18n x 18n first-order new-column step for E1(n) -> E1(n+1).

m = n+1 blocks, newest N = n.  Everything is expressed in G'^(m)-coordinates modulo eps^2
(standard-tail basis of the m-system: eta, G'^(n)K_N (old labels), B'_{t,N} = G'_{t,N}, G'_{N,r}),
computed for all normalised DHW columns by agent_per2_lib.coords_peel.  With
  L1 = {eta_all} ∪ {F'_{t,s} : t,s < N}     (appended old columns),
  Z  = span{(g0(l), g1(l)), (0, g0(l)) : l in L1}  ⊆ C^d ⊕ C^d  (image of L1 + eps^2 L_B'),
  Z0 = span g0(L1),  Z1 = {x : (0,x) in Z} = Z0 + g1(ker g0|L1),
  T  = C^d / Z1  (= (eps L_B' + L1 + eps^2 L_B')/(L1 + eps^2 L_B')),
  V  = the 18n new columns F'_{t,N,a,b}, F'_{N,s,a,b};  S00 = g0|V mod Z0,  K0 = ker S00,
  Step(k) = [g1(k) - g1(l_k)] (where g0(k) = g0(l_k), l_k in span L1),  Step(v) = [g0(v)] (= [eps v]).
E1(m) <=> Step : K0 ⊕ V/K0 -> T is onto (AGENT_PER2_NOTES sec. 0).
Prints dim T, whether the 18n target classes eps B'_{t,N}, eps G'_{N,r} form a basis of T,
dim K0, rank of pi on Im S00, rank of Step(K0), total rank, and the coverage of the two target
types by the two parts.
What this does not show: structure beyond the reported ranks (see agent_per2_stepstruct).
"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from agent_per2_lib import P, System, coords_peel, nm  # noqa: E402


def colbasis(A):
    """Independent columns of A (pivot columns of rref of A)."""
    if A.shape[1] == 0:
        return A
    R, rk = nm(A).rref()
    Rl = R.tolist()
    piv = []
    for i in range(rk):
        for j, x in enumerate(Rl[i]):
            if int(x):
                piv.append(j)
                break
    return A[:, piv]


def nullspace(A):
    if A.shape[1] == 0:
        return np.zeros((0, 0), dtype=np.int64)
    X, nul = nm(A).nullspace()
    Xl = X.tolist()
    return np.array([[int(Xl[i][q]) for q in range(nul)] for i in range(A.shape[1])], dtype=np.int64).reshape(A.shape[1], nul)


def rank(A):
    return nm(A).rank() if A.size else 0


def mul(A, B):
    return np.array((nm(A) * nm(B)).tolist(), dtype=np.int64)


def step_data(m, seed, verbose=True):
    n = m - 1
    N = n
    t0 = time.time()
    sysm = System(m, seed=seed, npts=9 * m * m // 2 + 30, kinds=('F', 'G'))
    eG = sysm.emax('G')
    if sysm.K < 2 * eG + 4:
        sysm = System(m, seed=seed, K=2 * eG + 4, npts=9 * m * m // 2 + 30, kinds=('F', 'G'))
    G, F = sysm.rows['G'], sysm.rows['F']
    labG, labF = sysm.lab['G'], sysm.lab['F']
    d = sysm.d
    gam = coords_peel(G, F, 2)
    g0, g1 = gam[0] % P, gam[1] % P
    L1 = [j for j, l in enumerate(labF) if l[0] == 'E' or (l[1] < N and l[2] < N)]
    newtN = [j for j, l in enumerate(labF) if l[0] == 'F' and l[2] == N]
    newNs = [j for j, l in enumerate(labF) if l[0] == 'F' and l[1] == N]
    new = newtN + newNs
    tgt_tN = [i for i, l in enumerate(labG) if l[0] == 'G' and l[2] == N]
    tgt_Nr = [i for i, l in enumerate(labG) if l[0] == 'G' and l[1] == N]
    tgt = tgt_tN + tgt_Nr
    assert len(new) == 18 * n and len(tgt) == 18 * n
    Z0 = colbasis(g0[:, L1])
    kL1 = nullspace(g0[:, L1])
    Z1 = colbasis(np.hstack([Z0, mul(g1[:, L1], kL1) if kL1.size else np.zeros((d, 0), dtype=np.int64)]))
    dimT = d - Z1.shape[1]
    Etgt = np.zeros((d, len(tgt)), dtype=np.int64)
    for q, i in enumerate(tgt):
        Etgt[i, q] = 1
    basisT = rank(np.hstack([Z1, Etgt])) == d and dimT == len(tgt)
    # coordinates in T w.r.t. the target basis: solve [Etgt | Z1] y = x
    Minv = nm(np.hstack([Etgt, Z1])).inv() if basisT else None

    def Tcoords(X):
        Y = np.array((Minv * nm(X)).tolist(), dtype=np.int64)
        return Y[:len(tgt), :] % P

    V0, V1 = g0[:, new], g1[:, new]
    # K0: c with V0 c in span Z0  -> nullspace of [V0 | Z0], projected to c; and the compensating l
    NS = nullspace(np.hstack([V0, g0[:, L1]]))          # (18n + |L1|) x k
    cK = NS[:len(new), :]
    lK = NS[len(new):, :]
    # Step on K0: g1 V c + g1 L1 l  (signs: V0 c + g0 L1 l = 0)
    StepK = (mul(V1, cK) + mul(g1[:, L1], lK)) % P if NS.size else np.zeros((d, 0), dtype=np.int64)
    dimK0 = rank(cK) if cK.size else 0
    r00 = rank(np.hstack([V0, Z0])) - Z0.shape[1]
    rpi = rank(np.hstack([V0, Z1])) - Z1.shape[1]
    rK = rank(np.hstack([StepK, Z1])) - Z1.shape[1]
    rtot = rank(np.hstack([StepK, V0, Z1])) - Z1.shape[1]
    res = dict(n=n, d=d, dimT=dimT, basisT=basisT, dimK0=dimK0, r00=r00, rpi=rpi, rK=rK, rtot=rtot,
               time=time.time() - t0)
    if basisT:
        A_pi = Tcoords(V0)            # 18n x 18n : columns = new columns (eps v)
        A_K = Tcoords(StepK)          # 18n x (#K0 generators)
        res['A_pi'], res['A_K'] = A_pi, A_K
        res['cover'] = {
            'pi part on tN rows': rank(A_pi[:9 * n, :]), 'pi part on Nr rows': rank(A_pi[9 * n:, :]),
            'K0 part on tN rows': rank(A_K[:9 * n, :]) if A_K.size else 0,
            'K0 part on Nr rows': rank(A_K[9 * n:, :]) if A_K.size else 0,
            'pi from F_tN cols': rank(A_pi[:, :9 * n]), 'pi from F_Ns cols': rank(A_pi[:, 9 * n:]),
        }
    res['labels'] = dict(new=[labF[j] for j in new], tgt=[labG[i] for i in tgt])
    res['g'] = (g0, g1, labG, labF)
    if verbose:
        print(f'm={m} (n={n}): dim T = {dimT} (18n = {18 * n}); target classes form a basis of T: {basisT}; '
              f'dim K0 = {dimK0}; rank S00 = {r00}; rank pi(Im S00) = {rpi}; rank Step(K0) = {rK}; '
              f'total rank = {rtot}  -> E1(m) via the step: {rtot == 18 * n}  [{res["time"]:.0f}s]', flush=True)
        if 'cover' in res:
            print('   coverage:', res['cover'], flush=True)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, nargs='+', default=[5])
    ap.add_argument('--seed', type=int, default=101)
    args = ap.parse_args()
    for m in args.m:
        step_data(m, args.seed)


if __name__ == '__main__':
    main()
