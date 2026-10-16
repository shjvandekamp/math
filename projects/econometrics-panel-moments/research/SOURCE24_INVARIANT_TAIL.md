# A three-evaluation invariant tail proves paired independence

**Status, 16 October 2026:** independently audited paper proof with a
locally reproduced exact finite initialization. This establishes the
generic paired boundary determinant at every length. The argument is
not yet formalized end to end in Lean, and does not prove independence
of the full equation-(24) source list.

The construction was proposed by
[Pro61](https://chatgpt.com/c/6ad1f993-e268-83ed-af10-0177500354c5).
Two independent local audits checked the tail argument and the
specialization bridge. A separately written standard-library verifier
reconstructed the actual base and all finite initialization matrices;
it did not execute the supplied external program.

Use the actual definitions and forward identities (NH1)--(NH32) in
[SOURCE24_NONZERO_H_WEAK_TRANSFER.md](SOURCE24_NONZERO_H_WEAK_TRANSFER.md).
In particular, the polynomial heads of the source combinations are
retained. All function-space coefficients are constant in the effect
coordinate \(r\). The bounded ambient \(\mathcal F_m\) has simple
poles at the \(3m\) binary nodes and dimension \(3m+1\).

## A specialization where three evaluations describe the entire image

Fix \(z=2h\ne0\), a positive scalar \(\tau\), and impose on consecutive
tail blocks
\[
 b_t=\frac{\tau a_t}{1+za_t}.
 \tag{IT1}
\]
Write \(k=m+1\), \(A=a_k\), \(B=a_m\), \(b=b_k\), \(b_-=b_m\),
and \(\ell=(b-b_-)/3\). Then
\[
 \frac bA-\frac{b_-}B=-z(b-b_-),\qquad
 \Delta_k(r)=\ell\,\frac{r-z}{r}.
 \tag{IT2}
\]
Define
\[
 E_m=\{c\in\mathcal F_m:c(0)=c(\infty)=c(z)=0\}.
 \qquad \dim E_m=3m-2.
 \tag{IT3}
\]
The three evaluations are independent: the constant function and two
distinct simple-pole functions give an invertible evaluation matrix
when the poles avoid zero and \(z\).

Under the ordinary pole and denominator conditions, the exact
forward transfer satisfies
\[
 \boxed{E_k=\mathcal N_k\oplus\mathscr T^{\rm full}_{k,h}E_m.}
 \tag{IT4}
\]
The generic ambient inverse of (NH49) is not used here: its
\(\Delta_k(z)\) denominator vanishes on this specialization.

Here is the direct proof. For an endpoint-zero old function,
the forward formula is
\[
 Tc=\chi c-\Delta_k\lambda D_m d_kQ_{k,h},\qquad
 \lambda=c(\xi)/D_m(\xi),\quad \xi=1/A.
 \tag{IT5}
\]
Every element of \(\mathcal N_k\) is regular at the new state-2
pole \(\xi\). Its potential pole cancels between the two terms of
\(\beta_2\). On the other hand,
\[
 [(1-Ar)Tc]_{r=\xi}
   =(\xi-z)\left(\frac{4b}{3}+\Delta_k(\xi)\right)c(\xi).
 \tag{IT6}
\]
Thus \(Tc\in\mathcal N_k\) forces \(c(\xi)=0\), provided the
displayed factors are nonzero. Then \(\lambda=0\) and \(Tc=\chi c\).
This has no new binary poles. Canceling those two poles in
\(\mathcal N_k\) leaves exactly the line
\(\operatorname{span}\{\Delta_kD_m\bar\beta\}\), with
\(\bar\beta\) defined in (NH12). Consequently the kernel of
\(T\bmod\mathcal N_k\) on endpoint-zero old functions is exactly
\[
 \operatorname{span}\{\psi_{m,k}\},\qquad
 \psi_{m,k}=
 \frac{b-b_-}{4b}\frac{1-Ar}{r}D_m\bar\beta .
 \tag{IT7}
\]
Indeed \(\Delta_k/\chi=(b-b_-)(1-Ar)/(4br)\). The function
\(\psi_{m,k}\) has only old poles, vanishes at \(\xi\), and has
endpoint orders at least \(m-1\) at both ends. It belongs to the
endpoint-zero old ambient for every \(m\ge2\). Conversely its
transfer is \(\Delta_kD_m\bar\beta\).

The already audited identity (NH13) gives
\[
 \psi_{m,k}(z)=
 \frac{b-b_-}{4b}\frac{1-Az}{z}D_m(z)\bar\beta(z)\ne0.
 \tag{IT8}
\]
Therefore this kernel line misses \(E_m\). Both \(\mathcal N_k\)
and \(T(E_m)\) vanish at zero, infinity, and \(z\): the first
two vanishings follow from the endpoint formulas; the last follows
from \(\Delta_k(z)=\chi(z)=0\), with no endpoint corrections
on \(E_m\). The three generators of \(\mathcal N_k\) remain
independent. Their two new binary residues give two directions,
and \(\bar\beta\ne0\) gives the third. Injectivity and directness
now give dimension \(3+(3m-2)=3k-2\), proving (IT4).

The newly reset gauge space is transverse to \(E_k\). In fact,
the evaluation determinant from (NH35) becomes
\[
 \boxed{\det\operatorname{ev}_{0,\infty,z}(1,W_0,W_1)
 =\frac{\tau^2z(A-B)^2}
 {12(1+zA)^2(1+zB)^2}\ne0.}
 \tag{IT9}
\]
This checks the new gauge space directly; it does not assert that
the old gauge space is preserved by transfer.

## Exact actual-source initialization at length five

Set
\[
 z=\frac1{10},\qquad
 (a_1,\ldots,a_5)=\left(\frac65,\frac75,\frac32,\frac85,\frac{17}{10}\right),
 \quad
 (b_1,\ldots,b_5)=\left(1,2,\frac52,\frac{20}{9},\frac{2465}{1053}\right).
 \tag{IT10}
\]
At step three \(\kappa_0=0\), at step four
\(\kappa_\infty=0\), and at step five \(\Delta_5(z)=0\).
Thus the recursively generated columns first acquire a zero at
zero, then at infinity, and then at \(z\). No inverse endpoint
multiplier is taken. The last two weights already satisfy (IT1)
with \(\tau=29/18\).

The actual four-column base is specified as follows. Order the
completed source coefficients by
\[
 (H_{10},H_{11},H_{12},H_{20},H_{21},H_{22},
   J_{10},J_{11},J_{12},J_{20},J_{21},J_{22}),
\]
and set
\[
 \Gamma=M\operatorname{diag}(1/176400,1/20580,1/49392,1/246960),
 \quad
 M=\begin{pmatrix}
 -12586&-2387&217&-15841\\
 777245&-3710&-31535&1250270\\
 197960&-15680&-9800&344960\\
 6048&2016&0&6048\\
 -842625&0&33705&-1348200\\
 -263340&11970&11970&-442890\\
 -28620&-18810&1710&-50742\\
 121086&-4788&-40698&131796\\
 176400&0&0&0\\
 0&20580&0&0\\
 0&0&49392&0\\
 0&0&0&246960
 \end{pmatrix}.
 \tag{IT11}
\]
Direct exact identities over \(\mathbb Q(r)\) verify that each
completed binary output is zero and its row sum is exactly zero.
The retained polynomial heads are \(\theta_j(z,-r,r-z)\), where
\[
 (\theta_1,\theta_2,\theta_3,\theta_4)
 =(-467/1260,-53/294,155/3528,-1399/3528).
 \tag{IT12}
\]
These are genuine nonzero-\(z\) actual kernel columns, not the
unchanged \(h=0\) coefficients. The eight constraints consist of
the two coefficients of the row sum followed by ordinary residues
of binary output one at
\(2/a_1,1/(2a_1),1/a_1,2/a_2,1/(2a_2),1/a_2\).
Their minor on the first eight source columns is
\(-1075/117504\ne0\), and the final four rows of \(\Gamma\)
are the identity. This also supplies a rational local continuation
of the base in its parameters.

The first weak functions are derived from the actual words. For
\(s,t\in\{1,2\}\), \(s\ne t\), put
\(u_t=(1/l_{t0},1/l_{t1},2/l_{t2})^{\mathsf T}\). Then
\[
 w^H_{sc}=b_tX_ce_cK_s^0u_t,\qquad
 w^J_{sc}=b_t\mu_{sc}^0vu_t,\qquad
 c_j=\sum_i\Gamma_{ij}w_i .
 \tag{IT13}
\]
The derivative of an earlier factor contributes zero because the
final binary kernel's output-two column is zero. This explains
the normalization \(c=[\delta]C_2/(r-z)\).

Starting with these four functions, use the ordered forward columns
\[
 S_k=(\Delta_kD_{k-1}\beta_0,\Delta_kD_{k-1}\beta_1,
       \Delta_kD_{k-1}\beta_2,\ T_kS_{k-1}).
 \tag{IT14}
\]
Multiply \((S_k,1,W_0,W_1)\) by
\(\Lambda_k=\prod_{t\le k}(2-a_tr)(1-2a_tr)(1-a_tr)\),
and take coefficients of \(r^0,\ldots,r^{3k}\). This gives square
matrices of sizes \(10,13,16\). The independently reconstructed
matrices have determinants, modulo \(1000003\),

| Length \(k\) | Matrix size | Determinant modulo \(1000003\) |
|---|---:|---:|
| 3 | 10 | 162385 |
| 4 | 13 | 696500 |
| 5 | 16 | 789105 |

All rational denominators are units modulo this prime. Hence these
are exact certificates of nonzero rational determinants. They do
not establish the much larger exact determinant fractions printed
by the external response; only their reductions were compared.
In particular \(S_5\) consists of thirteen independent functions
in \(E_5\), and therefore
\[
 \operatorname{span}S_5=E_5.
 \tag{IT15}
\]

The [independent verifier](../exploration/source24_invariant_tail_base.py)
and [saved certificate](../certificates/source24_invariant_tail_base.json)
record all 252 rational identities, full rational matrices, modular
elimination pivots and operation replays, and 703 denominator-unit
certificates. The single prescribed run took 0.39 seconds and
19,726,336 bytes maximum RSS, with no parameter search or rerun.
This finite evidence initializes (IT4); it is not extrapolated to
larger lengths.

## Uniform tail and generic paired conclusion

For \(t\ge6\), choose
\[
 a_t=2-\frac1{t-1},\qquad
 b_t=\frac{29}{18}\frac{a_t}{1+a_t/10}.
 \tag{IT16}
\]
All \(a_t\) are distinct in \((1,2)\), and all \(b_t\) are
positive. The three node intervals are disjoint, so there are no
cross-type binary collisions; within a type distinct \(a_t\)
give distinct nodes. The point \(z=1/10\) avoids them.
The function \(Q_{1,h}\) has numerator
\((6/5)r^2-(44/25)r-1/10\). It is negative at
\(1/(2A),1/A,2/A\) for the tail values \(A\in[17/10,2)\),
and its pole \(5/6\) is avoided there. Thus all three required
\(Q\)-values are nonzero. Formula (NH13) gives
\(\bar\beta(z)\ne0\). Also \(b>b_-\), \(Az<1\), and
\(\Delta_k(1/A)=\ell(1-Az)>0\), so the coefficient in (IT6)
is nonzero.

Equations (IT4) and (IT15) now prove
\(\operatorname{span}S_k=E_k\) for every \(k\ge5\).
Equation (IT9) proves its transversality to the reset gauge
space at every such length. Lengths three and four use the
separate nonzero determinants above, and length two uses the
previous audited symbolic base (TB1)--(TB29).

The passage back to generic parameters is important. The forward
functions in (IT14) are rational and regular at (IT10)--(IT16);
they do not divide by \(\kappa_0,\kappa_\infty,\Delta_k(z)\).
They represent actual promoted weak columns over the generic
parameter field by (NH7)--(NH26). Even if a particular generic
source coefficient representation has a pole at the specialization,
the nonzero specialized scalar determinant proves rational
nonidentity. Its nonzero open intersects the finitely many
generic realization-denominator conditions near the positive
specialization. Thus no actual source-basis inverse on the
singular specialization is assumed.

For every fixed length \(m\ge2\), (NH32) is consequently true
generically. The \(3m-2\) promoted columns and two actual gauges
give \(3m\) independent weak residue directions. Together with
the \(3m\) strong binary pivots, this proves that the normalized
paired \(6m\)-square residue determinant is not the zero
rational function. It supplies generic positive parameters with
full paired rank \(6m\) in each state sector.

This conclusion concerns the paired boundary matrix. The actual
full-source elimination still leaves the retained-old block
\[
 D_q+Z_T-Z_BC_B^{-1}C_T
 \tag{IT17}
\]
from (LC113). Its nonvanishing is not implied by invertibility
of \(C_B\). All insertion and polynomial-head corrections remain
in (IT17). Proving that determinant, formalizing the complete new
argument, and connecting the result to the full equation-(24)
family are unfinished work.

## Polynomial form of the tail step

The following normalization was derived locally and independently audited.
It gives an elementary polynomial route to (IT4), with no residue operator
or function-space rank premise inside its separation argument.
Put \(a=a_1\) and
\[
 \Lambda_m=\prod_{t\le m}(2-a_tr)(1-2a_tr)(1-a_tr),\quad
 U_m=\prod_{t\le m}(1-a_tr),\quad C_m=(-3)^m\prod_{t\le m}a_t.
 \tag{IT18}
\]
Then \(D_m=C_mr^mU_m/\Lambda_m\). The map
\[
 P\longmapsto c=\frac{r(r-z)P}{\Lambda_m},\qquad
 \deg P\le3m-3,
 \tag{IT19}
\]
identifies the polynomial space with \(E_m\): vanishing at infinity
removes the top numerator coefficient, and the other two evaluations
give the factors \(r(r-z)\).

Write \(N_A=Ar^2+(2Az-2)r-z\) and
\(H_A=(r-z)(2-Ar)(1-2Ar)\). Direct substitution into (IT5) gives
\[
 \frac{\Lambda_{m+1}Tc}{r(r-z)}
 =F P+P(\xi)K,\quad F=\frac{4b}{3}H_A,\quad
 K=\frac{\ell A(\xi-z)r^{m-1}U_mN_A}
          {\xi^{m-1}U_m(\xi)}.
 \tag{IT20}
\]
In particular
\[
 F(\xi)+K(\xi)=-(\xi-z)\eta,\qquad
 \eta=\frac{4b}{3}+\Delta_k(\xi)\ne0.
 \tag{IT21}
\]
For the three normalized new columns, let
\(B_m=\ell C_mr^{m-2}U_m/(1-ar)\). Their polynomial factors are
\[
\begin{aligned}
 n_0&=\tfrac23N_a(1-2Ar)(1-Ar),\\
 n_1&=-\tfrac r3N_a(2-Ar)(1-Ar),\\
 n_2&=-Ar(1-ar)N_A+
       \frac{(r-z)N_a(2-Ar)(1-2Ar)}{3Q_{1,h}(\xi)}.
\end{aligned}
 \tag{IT22}
\]
Thus the original ordered generators normalize to \(B_mn_j\).
Use the invertible column change
\[
 \bar n_2=n_2+\frac{z\,n_0}{Q_{1,h}(2/A)}
                   +\frac{n_1}{Q_{1,h}(1/(2A))}.
 \tag{IT23}
\]
Every \(n_j(\xi)\) is zero. At \(p_0=2/A,p_1=1/(2A)\),
\[
\begin{array}{c|cc}
 &p_0&p_1\\ \hline
 n_0&2N_a(p_0)&0\\
 n_1&0&-N_a(p_1)/(8A)\\
 n_2&-6z(1-2a/A)&3(1-a/(2A))/(8A)
\end{array}
 \tag{IT24}
\]
so \(\bar n_2(p_0)=\bar n_2(p_1)=0\). Also
\[
 \bar n_2(z)
 =(1-az)(2-Az)(1-2Az)(1-Az)\bar\beta(z)\ne0.
 \tag{IT25}
\]
The common factor \(B_m\) is nonzero at all three nodes
\(p_0,p_1,z\) under the established tail conditions.

Now suppose
\[
 xB_mn_0+yB_mn_1+wB_m\bar n_2+FP+P(\xi)K=0.
 \tag{IT26}
\]
Evaluation at \(\xi\) first gives \(P(\xi)=0\), by (IT21).
Evaluation at \(p_0\), then \(p_1\), then \(z\) gives
\(x=y=w=0\), by (IT24)--(IT25). Finally \(FP=0\) and
\(F\ne0\) imply \(P=0\). This proves joint injectivity of
the three new scalars and the old polynomial.
The degree bounds are
\(\deg(FP)\le3m\), \(\deg K\le2m+1\), and
\(\deg(B_mn_j)\le2m+2\le3m\) for \(m\ge2\).
The domain and target therefore both have dimension \(3m+1\);
the polynomial extension is an isomorphism.

The general four-evaluation separation mechanism and the displayed
concrete polynomial identities are being formalized separately.
Their identification with actual promoted source columns is still
the external algebra (IT18)--(IT23); this paragraph does not claim
an end-to-end Lean proof of paired or full-source independence.
