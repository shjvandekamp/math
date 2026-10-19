#!/usr/bin/env python3
"""Inductive step map T = beta - Hd*alpha on the tau-kernel B0 (sec. 4.7 of HQ_FRESH_APPROACH.md).

Basis of W_{n+1} mod E: {F_k K_N, B_{t,N,a,b}, B_{N,r,a,b} K_{>r}} (Theorem A structure).
New columns are expanded in it; B0 = combinations with zero B_N K_> coordinates;
T(gamma) = B_{t,N}-coordinates minus head sums of F K-coordinates.  det R_{n+1} != 0 iff T is
invertible (given det R_n != 0).  Prints ranks and the new-line sector pattern of T.
"""
import sys, random
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import flint
from hq_fresh_fast import Ring, product_blocks, row_index
from hq_fresh_words import build_cols
p=(1<<61)-1; R=Ring(p); Q=3
def word_F(t,s,n): return [s]+[u for u in range(n) if u not in (s,t)]
for n in (2,3,4,5):
    N=n; nb=n+1
    A=product_blocks(nb,R,random.Random(700+n))
    cols=[]; lab=[]
    # basis part 1: F_k K_N  (old F with N appended) minus B_{head,N}:  F_k K = h(I-W) K = h(I - W K) - h(I-K)
    for t in range(n):
        for s in range(n):
            if s==t: continue
            w=word_F(t,s,n)
            for a in range(Q):
                for b in range(Q):
                    cols.append((t,a,b,[(1,w+[N]),(-1,[N])])); lab.append(('FK',t,s,a,b))
    # basis part 2: B_{t,N,a,b} = h(I-K_N)
    for t in range(n):
        for a in range(Q):
            for b in range(Q):
                cols.append((t,a,b,[(1,[N])])); lab.append(('BtN',t,a,b))
    # basis part 3: B_{N,r,a,b} K_{>r}  (r old, tail = old blocks > r)
    for r in range(n):
        tail=[u for u in range(n) if u>r]
        for a in range(Q):
            for b in range(Q):
                cols.append((N,a,b,[(1,[r]+tail),(-1,tail)] if tail else [(1,[r])])); lab.append(('BNr',r,a,b))
    nbasis=len(cols)
    # new columns: F_{t,N,a,b} (word N then old increasing w/o t) and F_{N,s,a,b} (word s then old increasing w/o s)
    for t in range(n):
        for a in range(Q):
            for b in range(Q):
                cols.append((t,a,b,[(1,[N]+[u for u in range(n) if u!=t])])); lab.append(('FtN',t,a,b))
    for s in range(n):
        for a in range(Q):
            for b in range(Q):
                cols.append((N,a,b,[(1,[s]+[u for u in range(n) if u!=s])])); lab.append(('FNs',s,a,b))
    rows=build_cols(A,nb,R,cols)
    keys=row_index(nb)
    M=flint.nmod_mat([[int(rows[k][j]) for j in range(len(cols))] for k in keys],p)
    Bm=flint.nmod_mat([[int(M[i,j]) for j in range(nbasis)] for i in range(M.nrows())],p)
    Nm=flint.nmod_mat([[int(M[i,j]) for j in range(nbasis,len(cols))] for i in range(M.nrows())],p)
    assert Bm.rank()==nbasis, 'basis not a basis'
    Co=Bm.solve(Nm)   # coordinates of new columns in the basis (mod E)
    iFK=[j for j in range(nbasis) if lab[j][0]=='FK']; iB=[j for j in range(nbasis) if lab[j][0]=='BtN']; iG=[j for j in range(nbasis) if lab[j][0]=='BNr']
    nn=Nm.ncols()
    Gp=flint.nmod_mat([[int(Co[i,j]) for j in range(nn)] for i in iG],p)
    # B0 = right kernel of Gp (combinations of new columns)
    # compute nullspace via rref
    Rr,rk=Gp.rref()
    piv=[];r=0
    for c in range(nn):
        if r<rk and int(Rr[r,c])!=0: piv.append(c); r+=1
    free=[c for c in range(nn) if c not in piv]
    B0=[]
    for f in free:
        v=[0]*nn; v[f]=1
        for i,pc in enumerate(piv): v[pc]=(-int(Rr[i,f]))%p
        B0.append(v)
    B0m=flint.nmod_mat([[B0[k][j] for k in range(len(B0))] for j in range(nn)],p)  # nn x dimB0
    alpha=flint.nmod_mat([[int(Co[i,j]) for j in range(nn)] for i in iFK],p)*B0m
    beta=flint.nmod_mat([[int(Co[i,j]) for j in range(nn)] for i in iB],p)*B0m
    heads=[(t,a,b) for t in range(n) for a in range(Q) for b in range(Q)]
    Hd=flint.nmod_mat(len(heads),len(iFK),[1 if (lab[j][1],lab[j][3],lab[j][4])==h else 0 for h in heads for j in iFK],p)
    HA=Hd*alpha
    T=beta-HA
    print(f'n={n}: dim B0={len(B0)} (9n={9*n}); rank beta={beta.rank()}, rank Hd*alpha={HA.rank()}, rank T={T.rank()}; Hd*alpha==0: {all(int(HA[i,j])==0 for i in range(HA.nrows()) for j in range(HA.ncols()))}',flush=True)
    # sector structure: columns of B0 by sector (which new line d the free variable belongs to)
    newlab=lab[nbasis:]
    def sector(l):
        return l[3] if l[0]=='FtN' else l[2]
    colsec=[sector(newlab[f]) for f in free]
    rowsec=[h[2] for h in heads]   # B_{t,N,a,b}: new line b
    blk=[[0]*3 for _ in range(3)]
    for i in range(T.nrows()):
        for j in range(T.ncols()):
            if int(T[i,j])!=0: blk[rowsec[i]][colsec[j]]+=1
    print('   T nonzeros by (row new-line b, col sector d):',blk)
    if n <= 3:
        ranks=[[0]*3 for _ in range(3)]
        for rb in range(3):
            for cd in range(3):
                ri=[i for i in range(T.nrows()) if rowsec[i]==rb]; ci=[j for j in range(T.ncols()) if colsec[j]==cd]
                sub=flint.nmod_mat([[int(T[i,j]) for j in ci] for i in ri],p)
                ranks[rb][cd]=sub.rank()
        print('   rank of sector blocks (row b, col d):',ranks)
