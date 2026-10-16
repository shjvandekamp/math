# Actual-source confluence: second-order obstruction and a cubic minor

**Status: independently audited paper calculation, 16 October 2026.**
This note records the checked Pro62 construction using the actual source
conventions of [SOURCE24_INDUCTION.md](SOURCE24_INDUCTION.md).
Explicit constant column operations remove the constant and first
coefficients of every retained source. A constructed coefficient subspace
of dimension \(3(q^2-5q+8)/2\) also has zero second coefficient.
This is an obstruction to a second-order confluence certificate, not a
counterexample to generic independence.

An independently reconstructed exact-arithmetic certificate verifies a
nonzero cubic minor of ordinary source functions. Those observations do
not descend to the actual new-source quotient: they already have full
rank on three new \(E_c\) sources. Survival of the cubic classes in the
required quotient remains open. These results are not an end-to-end Lean
proof of equation (24).

## Actual sources and the confluence curve

Label the new earliest block \(c\), and the old blocks \(1,\ldots,q\).
All products below use increasing time order unless displayed otherwise;
empty products are the identity. State indices are \(a,b,d\in\{0,1,2\}\),
and \(e_a\) denotes a row vector. Write \([A,B]=AB-BA\).

Take an analytic common-\(G\) time curve
\(A(\theta)=G\operatorname{diag}(1,u(\theta),v(\theta))\), with
\(\theta_c=0\) and \(\theta_j=j\varepsilon\). Its actual row-normalized
kernel is
\[
 K(\theta)_{ab}
 =\frac{A(\theta)(a,b)X_b}
        {\sum_d A(\theta)(a,d)X_d}.
\]
The coefficient calculations take place in rational functions of the
effect coordinates \(X\), over a characteristic-zero parameter field.
Write
\[
 K(\theta)=K+\theta U+\theta^2V+O(\theta^3),
 \qquad p^{ab}(\theta)=X_aK(\theta)_{ab}.
 \tag{SC1}
\]
Thus \(V\) is the second Taylor coefficient, not the full second
derivative. The explicit cubic witness uses
\[
 G=I+\mathbf1\mathbf1^{\mathsf T},\qquad
 u(\theta)=1+\theta+O(\theta^3),\qquad
 v(\theta)=1+\theta^2+O(\theta^3).
 \tag{SC2}
\]
For fixed finite higher Taylor coefficients, the parameters are positive
for sufficiently small positive \(\varepsilon\). This is a curved time
family. The word identities first proved below allow arbitrary \(G\)
and analytic curves for which the baseline row denominators are nonzero
rational functions.

Put \(K_j=K(\theta_j)\), \(p_t^{ab}=p^{ab}(\theta_t)\), and
\[
 B_t^{ab}=F_{(t,c,a,b)},\qquad N_s^{ab}=F_{(c,s,a,b)},\qquad
 L_{t,s}=\prod_{\substack{j<s\\j\ne t}}^\nearrow K_j,\qquad
 R_{t,s}=\prod_{\substack{j>s\\j\ne t}}^\nearrow K_j.
\]
Temporarily suppress \(a,b\). The retained and incoming sources are
\[
 T_{ts}=p_t^{ab}e_b(I-K_sK_cL_{t,s}R_{t,s}),\qquad
 B_t=p_t^{ab}e_b(I-K_cL_{t,s}K_sR_{t,s}).
\]
Their polynomial heads cancel exactly:
\[
 T_{ts}-B_t
 =p_t^{ab}e_b[K_cL_{t,s},K_s]R_{t,s}.
 \tag{SC3}
\]
Likewise, with \(\mathcal N_s=N_s-N_1\) and \(\mathcal N_1=0\),
\[
 \mathcal N_s
 =p_c^{ab}e_b
   \left[\prod_{j<s}K_j,K_s\right]\prod_{j>s}K_j .
 \tag{SC4}
\]
Here \(N_1\) contains the ascending old product, so its head cancels
the head of \(N_s\).

## Exact removal of the first retained coefficient

For \(q\ge2\), define
\[
 C=[K,U],\qquad
 \mathcal V_r^{ab}=p^{ab}(0)e_bK^rCK^{q-2-r},
 \qquad 0\le r\le q-2.
 \tag{SC5}
\]
Expanding SC4 gives
\[
 [\varepsilon]\mathcal N_s
 =\sum_{r=0}^{s-2}(s-r-1)\mathcal V_r^{ab}.
 \tag{SC6}
\]
The prefix in SC3 contains \(c,1,\ldots,s-1\), omitting \(t\) when
\(t<s\). Its expansion therefore yields
\[
 [\varepsilon](T_{ts}-B_t)=
 \begin{cases}
  [\varepsilon]\mathcal N_{s+1},&t>s,\\
  [\varepsilon](\mathcal N_s+\mathcal N_{t+1}-\mathcal N_t),&t<s.
 \end{cases}
 \tag{SC7}
\]
There are no out-of-range indices: \(t>s\) implies \(s+1\le q\),
and \(t<s\) implies \(t+1\le q\). The derivative of \(p_t^{ab}\)
multiplies a zero baseline commutator, so no first-order head factor
has been omitted.

Define the actual new-source combination
\[
 M_{ts}^{ab}=
 \begin{cases}
  \mathcal N_{s+1}^{ab},&t>s,\\
  \mathcal N_s^{ab}+\mathcal N_{t+1}^{ab}-\mathcal N_t^{ab},&t<s,
 \end{cases}
 \qquad
 \widehat T_{ts}^{ab}=T_{ts}^{ab}-B_t^{ab}-M_{ts}^{ab}.
 \tag{SC8}
\]
Both its constant and first coefficients vanish:
\[
 \widehat T_{ts}^{ab}=O(\varepsilon^2).
 \tag{SC9}
\]
All coefficients in this column operation are integers, independent of
\(X\) and \(\varepsilon\). It uses the actual \(N\) and \(B\) columns,
including their old-pair residues.

## Relation to the exact Schur regularization

Use the elimination in LC113 and LC177 of
[SOURCE24_LAST_TIME_COALESCENCE.md](SOURCE24_LAST_TIME_COALESCENCE.md).
In this paragraph, \(\Pi\) and \(\mathsf C\) include composition with
the new-pole observation map, so
\(\Pi N=I\), \(\mathsf C N=0\), and \(C_B=\mathsf C B\).
Assume \(C_B\) is invertible over the Laurent parameter field. Then
\[
 \mathscr R(f)
 =f-N\Pi f-(B-N\Pi B)C_B^{-1}\mathsf C f .
 \tag{SC10}
\]
Direct substitution gives \(\mathscr R(N)=\mathscr R(B)=0\).
Consequently the exact retained Schur matrix satisfies
\[
 H_q=D_{\rm old}\mathscr R(T)
     =D_{\rm old}\mathscr R(\widehat T).
 \tag{SC11}
\]
If \(BJ\) selects the \(B_t\) correction in SC8 and \(M=N\Lambda\),
put \(\widehat\alpha=\alpha-J\) and
\(\widehat\gamma=\gamma-\Lambda\). Then
\[
 T-B\alpha-N\gamma
 =\widehat T-B\widehat\alpha-N\widehat\gamma .
 \tag{SC12}
\]
No finite limit of \(C_B^{-1}\) is asserted or needed for these exact
identities. Its Laurent invertibility is an explicit condition for
comparison with \(H_q\), not a consequence of the confluence
calculation. The intrinsic quotient argument below does not require it.

For clarity, an actual new-head column generally has nonzero old-pair
residues. At a generic old crossing
\(P:\ L_{s,b}=L_{t,d}=0\), \(s\ne t\), set
\[
 U_{s,t}=\prod_{\substack{j<t\\j\ne s}}^\nearrow K_j,\qquad
 V_{s,t}=\prod_{\substack{j>t\\j\ne s}}^\nearrow K_j,\qquad
 v_{j,e}=A_j(e,:)\operatorname{diag}(X).
\]
Its double-pole coefficient is
\[
 \rho_{sb,td}(N_s^{ab})
 =-\left.
 p_c^{ab}(v_{s,b}U_{s,t}e_d^{\mathsf T})v_{t,d}V_{s,t}
 \right|_P .
 \tag{SC13}
\]
All other denominators must be units at this crossing. When the displayed
products are empty, this is
\(-p_c^{ab}A_s(b,d)X_dv_{t,d}\), generically nonzero. The residue
is computed at generic nonzero \(\varepsilon\), before taking a
confluent limit; substituting a colliding point before pole cancellation
would not justify SC13.

## Circulations and the second coefficient

Assume \(q\ge3\). Fix the state \(a\) and orient each old edge as
\(t<s\). A circulation is a coefficient vector satisfying
\[
 \sum_{s>t}\lambda_{ts}-\sum_{r<t}\lambda_{rt}=0
 \qquad(1\le t\le q).
 \tag{SC14}
\]
The incidence matrix of the connected complete graph has rank \(q-1\),
so its circulation space has dimension
\[
 g_q=\binom q2-q+1=\frac{(q-1)(q-2)}2 .
 \tag{SC15}
\]
Define the retained source combination
\[
 Z_{\lambda,a}
 =\sum_{t<s}\lambda_{ts}\sum_b(T_{ts}^{ab}-T_{st}^{ab}).
 \tag{SC16}
\]
The polynomial heads cancel by SC14. Since
\(\sum_b p_t^{ab}e_b=X_ae_aK_t\), the exact remaining word is
\[
 Z_{\lambda,a}
 =-X_ae_a\sum_{t<s}\lambda_{ts}[K_t,K_s]K_cR_{ts},
 \qquad
 R_{ts}=\prod_{j\notin\{t,s\}}^\nearrow K_j .
 \tag{SC17}
\]
For \(t<s\), SC8 gives
\(M_{ts}-M_{st}=\mathcal N_s-\mathcal N_t\).
Both these differences and the \(B_t-B_s\) corrections sum to zero
against a circulation. Hence
\[
 Z_{\lambda,a}(T)=Z_{\lambda,a}(\widehat T).
 \tag{SC18}
\]

To calculate the second coefficient, put
\(M_r=K^rUK^{q-3-r}\), \(0\le r\le q-3\). The increasing sequence
obtained by deleting \(t<s\) from \(1,\ldots,q\) gives
\[
 [\varepsilon]R_{ts}
 =\sum_{r=0}^{q-3}
  \left(r+1+\mathbf1_{r\ge t-1}+\mathbf1_{r\ge s-2}\right)M_r .
 \tag{SC19}
\]
Summing the circulation equations against \(t\) and \(t^2\) gives
\[
 \sum_{t<s}\lambda_{ts}(s-t)=0,\qquad
 \sum_{t<s}\lambda_{ts}(s^2-t^2)=0.
 \tag{SC20}
\]
In
\[
 [K_t,K_s]
 =\varepsilon(s-t)C
  +\varepsilon^2(s^2-t^2)[K,V]+O(\varepsilon^3),
\]
the putative \([U,U]\) term is zero. Thus SC20 removes both the
first coefficient and the \([K,V]\) part of the second coefficient.
Only the first variation of the deleted tail remains.

Define
\[
 b_r(\lambda)
 =\sum_{t<s}\lambda_{ts}(s-t)
   \left(\mathbf1_{r\ge t-1}+\mathbf1_{r\ge s-2}\right),
 \qquad 0\le r\le q-3 .
 \tag{SC21}
\]
Summing the indicators over \(r\) gives \(2q-1-t-s\);
SC20 therefore implies \(\sum_r b_r(\lambda)=0\). Put
\[
 w_r(\lambda)=-\sum_{h=0}^r b_h(\lambda),
 \qquad 0\le r\le q-4.
 \tag{SC22}
\]
Discrete summation gives
\(\sum_rb_rM_r=\sum_rw_r(M_{r+1}-M_r)\), while
\(M_{r+1}-M_r=K^rCK^{q-4-r}\). It follows that
\[
 [\varepsilon^2]Z_{\lambda,a}
 =-X_ae_a\sum_{r=0}^{q-4}
    w_r(\lambda)\,CK^{r+1}CK^{q-4-r}.
 \tag{SC23}
\]
For \(q=3\), this sum is empty and equals zero.

For \(1\le i\le q-3\), consider the triangle circulation
\[
 \tau_i=(i,i+1)+(i+1,i+3)-(i,i+3).
 \tag{SC24}
\]
Its only nonzero \(b\)-coordinates are \(b_{i-1}=-1\) and
\(b_i=1\), so
\[
 w_r(\tau_i)=\mathbf1_{r=i-1}.
 \tag{SC25}
\]
Thus \(w:\operatorname{Circ}(K_q)\longrightarrow\mathbb Q^{q-3}\)
is onto, with an integer right inverse. For \(q=3\) the target is
zero-dimensional. In all cases,
\[
 k_q:=\dim\ker w
 =g_q-(q-3)=\frac{q^2-5q+8}{2}.
 \tag{SC26}
\]
Equations SC17, SC20 and SC23 imply
\[
 \lambda\in\ker w\quad\Longrightarrow\quad
 Z_{\lambda,a}=O(\varepsilon^3).
 \tag{SC27}
\]
An explicit projection of any circulation onto this kernel is
\[
 \lambda-\sum_{r=0}^{q-4}w_r(\lambda)
 \bigl((r+1,r+2)+(r+2,r+4)-(r+1,r+4)\bigr).
 \tag{SC28}
\]
For a fixed \(a\), the map from circulation coefficients to the ordered
source coefficients in SC16 is injective. The three choices of \(a\)
have disjoint coefficient supports. Therefore the constructed
old-source coefficient subspace has dimension
\[
 3k_q=\frac{3(q^2-5q+8)}2.
 \tag{SC29}
\]
This is the exact dimension of this constructed subspace. It is only a
lower bound on the kernel of the full second-coefficient map: the matrix
words in SC23 could satisfy additional relations, and further relations
could appear after taking a quotient.

## The saturated actual-source quotient

Let \(R=\mathbb K[[\varepsilon]]\), where \(\mathbb K\) contains
parameter constants but not the effect coordinates \(X\). Clear every
source by the same denominator
\[
 Q_\varepsilon(X)
 =\prod_{j=c,1,\ldots,q}\prod_{a=0}^2 L_{j,a}(X).
\]
Each source word visits a time block at most once. This product therefore
clears its denominators, and all cleared sources lie in a finite free
polynomial coefficient lattice \(\mathscr L\) over \(R\), of a fixed
sufficient homogeneous degree. Crucially, \(Q_0\) is a nonzero
polynomial. A rational-row identity \(O(\varepsilon^k)\) consequently
gives divisibility by \(\varepsilon^k\) in this polynomial lattice:
its lower coefficient polynomials vanish as rational functions, hence
vanish as polynomials.

Let
\[
 \mathscr S^{\rm sat}
 =\mathscr L\cap
   \operatorname{span}_{\mathbb K((\varepsilon))}
   \{Q_\varepsilon N,\ Q_\varepsilon B,\ Q_\varepsilon E\},
 \qquad
 \mathscr Q=\mathscr L/\mathscr S^{\rm sat}.
\]
Here \(E_{t,a}=X_ae_a(I-K_t)\) are the actual single-block columns
used in the pair-residue reduction, including the new \(E_c\) columns.
Saturation includes every regular lattice representative of a Laurent,
parameter-dependent combination of these columns. It does not allow
coefficients depending on \(X\), or place arbitrary pole-valued vectors
inside \(\mathscr L\).

The quotient is finite and torsion-free over the discrete valuation
ring \(R\), hence free. Put \(d_q=9q(q-1)\), the number of retained
ordered sources. Write \(\overline T\) for the classes of
\(Q_\varepsilon T\). SC8–SC9 place every retained class in
\(\varepsilon^2\mathscr Q\). SC27–SC29 give \(3k_q\) independent
constant coefficient combinations in \(\varepsilon^3\mathscr Q\).
Extend those coefficient vectors to a constant basis of
\(\mathbb K^{d_q}\); its determinant is an \(\varepsilon\)-unit.
Taking the wedge in this basis proves
\[
 \bigwedge\nolimits^{d_q}[\overline T]
 \in
 \varepsilon^{\,2d_q+3k_q}\,
 \bigwedge\nolimits^{d_q}\mathscr Q .
 \tag{SC30}
\]
This also holds if the target rank is below \(d_q\), when the wedge is
zero. The second graded retained map has a kernel of dimension at least
\(3k_q\), so a square leading determinant at second order vanishes for
every \(q\ge3\).

SC30 requires neither a regular inverse nor Laurent invertibility of
\(C_B\). It is an intrinsic statement about the saturated actual-source
quotient. The old-pair residue chart used for \(H_q\) can be singular
during confluence. Converting SC30 into a valuation of a determinant in
that chart requires its change-of-coordinates determinant; no
unqualified order of the raw \(\det H_q\) follows.

## Consecutive triangles and an ordinary cubic minor

The consecutive triangle
\((i,i+1)+(i+1,i+2)-(i,i+2)\), \(1\le i\le q-2\), lies in
\(\ker w\). Write its actual source as \(Z_{i,a}\). For arbitrary
fixed \(W\), define the trilinear alternating expression
\[
 \operatorname{Alt}_W(A,B,C)
 =[A,B]WC+[B,C]WA+[C,A]WB .
 \tag{SC31}
\]
The three consecutive deleted-tail words have the same remaining
prefix and suffix. SC17 becomes the exact identity
\[
 Z_{i,a}
 =-X_ae_a
   \operatorname{Alt}_{K_cK_1\cdots K_{i-1}}
     (K_i,K_{i+1},K_{i+2})K_{i+3}\cdots K_q .
 \tag{SC32}
\]
Alternation kills all terms below order three. The first surviving
Taylor orders are \(0,1,2\); their Vandermonde determinant at
\(i,i+1,i+2\) is \(2\). The varying prefix contributes only its
constant term at this order. Hence
\[
 Z_{i,a}
 =-2\varepsilon^3X_ae_a
   \operatorname{Alt}_{K^i}(K,U,V)K^{q-i-2}
   +O(\varepsilon^4).
 \tag{SC33}
\]
For \(i=1\), set
\[
 S=[K,U]KV+[U,V]K^2+[V,K]KU .
 \tag{SC34}
\]
Then
\[
 Z_{1,a}
 =-2\varepsilon^3X_ae_aSK^{q-3}
  +O(\varepsilon^4).
 \tag{SC35}
\]

Use the specialization SC2 and the three ordinary source observations
\[
 \Phi_1(f)=f_1(1,1,1),\qquad
 \Phi_2(f)=f_2(1,1,1),\qquad
 \Phi_3(f)=\partial_{X_0}f_1(1,1,1).
 \tag{SC36}
\]
At \(X=(x,1,1)\), the baseline kernel is
\[
 K(x)=
 \begin{pmatrix}
  2x/(2x+2)&1/(2x+2)&1/(2x+2)\\
  x/(x+3)&2/(x+3)&1/(x+3)\\
  x/(x+3)&1/(x+3)&2/(x+3)
 \end{pmatrix}.
\]
For \(D=\operatorname{diag}(0,1,0)\) and
\(E=\operatorname{diag}(0,0,1)\), its actual Taylor coefficients are
\[
 U=KD-\operatorname{diag}(Ke_1^{\mathsf T})K,\qquad
 V=KE-\operatorname{diag}(Ke_2^{\mathsf T})K
      -\operatorname{diag}(Ke_1^{\mathsf T})U .
 \tag{SC37}
\]
These follow from expanding the actual row numerators and normalizers;
\(U,V\) are not independent matrix variables.

Put \(Y(x)=\operatorname{diag}(x,1,1)S(x)\). Exact calculation gives
\[
 Y(1)=\frac1{4096}
 \begin{pmatrix}6&-13&7\\7&-12&5\\5&-11&6\end{pmatrix},
 \qquad
 Y'(1)=\frac1{65536}
 \begin{pmatrix}120&-261&141\\29&-64&35\\23&-63&40\end{pmatrix}.
 \tag{SC38}
\]
Thus the determinant with observation rows and state columns is
\[
 \frac{
 \det\begin{pmatrix}
  -13&-12&-11\\
  7&5&6\\
  -261&-64&-63
 \end{pmatrix}}
 {4096^2\,65536}
 =\frac{3176}{2^{40}}=\frac{397}{2^{37}}.
 \tag{SC39}
\]
Every row of \(Y(1)\) and \(Y'(1)\) has sum zero. At \(x=1\),
\(K=(I+\mathbf1\mathbf1^{\mathsf T})/4\), so right multiplication
by \(K\) scales any zero-sum row by \(1/4\). With \(n=q-3\),
the tail \(K(x)^n\) therefore scales the first two observations by
\(4^{-n}\). Differentiating that tail adds a fixed linear combination
of those two observation rows to the third, as well as the factor
\(4^{-n}\) on the derivative observation. The determinant changes
by exactly \(4^{-3n}\). Including the three source factors \(-2\)
from SC35 gives, for every \(q\ge3\),
\[
 \det[\Phi_i(Z_{1,a})]_{\substack{i=1,2,3\\a=0,1,2}}
 =-\frac{397}{2^{34}4^{3(q-3)}}\,\varepsilon^9
   +O(\varepsilon^{10}).
 \tag{SC40}
\]
This is a nonzero ordinary actual-source minor. It has not been shown
to survive the quotient by the actual new sources, or the subsequent
quotient by the second-order retained image.

## Exact certificate and the observation limitation

The independent reconstruction is saved in
[source24_confluent_cubic.py](../exploration/source24_confluent_cubic.py),
with its passed record in
[source24_confluent_cubic.json](../certificates/source24_confluent_cubic.json).
It uses rational arithmetic and dual numbers for the \(x\)-derivative.
Its 54 exact checks comprise 18 comparisons of the actual row-normalizer
Taylor coefficients with SC37, 18 entries of \(Y,Y'\), six zero-sum
checks, the determinant and \(q=3\) source coefficient, and ten checks
of the following new-source obstruction. The first 44 checks concern
the ordinary cubic certificate. The uniform tail argument after SC39
is a separate paper argument, not an all-\(q\) computational check.

For the actual new single-block sources
\(E_{c,a}=X_ae_a(I-K)\), the same observations give
\[
 [\Phi_i(E_{c,a})]_{\substack{i=1,2,3\\a=0,1,2}}
 =
 \begin{pmatrix}
  -1/4&1/2&-1/4\\
  -1/4&-1/4&1/2\\
  -1/8&1/8&1/16
 \end{pmatrix},
 \qquad
 \det=\frac3{256}.
 \tag{SC41}
\]
The observation map is already onto on the span of these new sources.
No nonzero linear combination of \(\Phi_1,\Phi_2,\Phi_3\) annihilates
that span. Consequently these observations cannot serve as quotient
functionals, and SC40 alone says nothing about the rank of the
projected cubic classes. SC41 does not prove those classes vanish;
it identifies the missing projection step.

The fixed-curve matrix algebra now has a Lean companion,
[SourceConfluentCubicAlgebra.lean](../formal/PanelMoments/SourceConfluentCubicAlgebra.lean).
It identifies K with the actual homogeneous kernel, proves the genuine
entrywise x-derivatives, and proves the matrices and determinants in
SC38--SC39 and SC41. Its emptySources is the displayed single-block
matrix diag(X)(I-K). The module does not identify U and V as time-Taylor
coefficients, identify S as the source circulation coefficient, prove
the all-length factor in SC40, or establish quotient rank. Those source
and asymptotic identifications remain paper arguments.

## Higher-order interpolation and the remaining test

The first two curve coefficients can be kept fixed while allowing
independent old time parameters. For fixed \(q\), use
\[
 u(\theta)=1+\theta+\sum_{\ell=3}^{q+2}c_\ell\theta^\ell,\qquad
 v(\theta)=1+\theta^2+\sum_{\ell=3}^{q+2}d_\ell\theta^\ell.
\]
At any fixed \(\varepsilon\ne0\), the \(q\)-by-\(q\) evaluation matrix
\(((j\varepsilon)^\ell)_{1\le j\le q,\ 3\le\ell\le q+2}\)
is a nonzero diagonal matrix times a Vandermonde matrix in the
distinct nodes \(j\varepsilon\). It is invertible. Thus the higher
coefficients can prescribe the \(q\) old \(u\)-values and \(q\) old
\(v\)-values independently, while preserving the value at \(c\) and
the first two Taylor coefficients.

This is a nonidentity bridge: an already-known nonzero polynomial
condition on the old times pulls back to a nonzero condition on this
extended curve family. For a rational condition, first clear its
denominators and retain their nonvanishing conditions. When the
condition also varies with \(G\), allow \(G\) to vary in a neighborhood
of the positive witness SC2; the cubic coefficient remains nonzero
there. This avoids assuming that an old generic condition holds at
that one fixed \(G\).

The interpolation is used at fixed nonzero \(\varepsilon\) to prove
nonidentity, after which fixed generic higher coefficients are chosen.
Allowing coefficients to diverge with \(\varepsilon\) would not
justify preservation of the stated jets. With fixed coefficients,
positivity holds for sufficiently small positive \(\varepsilon\),
and a finite list of known nonzero generic conditions can be imposed
simultaneously. The higher terms do not change SC9, SC27 or SC33.
This bridge does not supply a missing old-independence theorem or a
nonzero projected determinant.

A concrete next test is available already at \(q=3\). Let
\(\mathscr L_0=\mathscr L/\varepsilon\mathscr L\), let
\(\mathscr S_0=(\mathscr S^{\rm sat}+\varepsilon\mathscr L)/
\varepsilon\mathscr L\), and write
\(\widehat T=\varepsilon^2T_2+\varepsilon^3T_3+\cdots\).
Inside \(\mathscr L_0\), set
\[
 \mathscr V_2=\mathscr S_0+
              \operatorname{span}_{\mathbb K}(Q_0T_2).
\]
For a circulation combination whose second coefficient is zero as an
actual rational row, its cubic class in
\(\mathscr L_0/\mathscr V_2\) is represented by \(Q_0Z_3\), where
\(Z_3=[\varepsilon^3]Z\). The \(Q_1T_2\) contribution is zero for
that combination; no varying projection is needed to identify this
representative.

At \(q=3\), there are \(d_3=54\) retained columns and three
constructed cubic directions. It would suffice for this graded test
to prove that \(T_2\) has rank \(51\) modulo \(\mathscr S_0\), and
to find three functionals annihilating \(\mathscr V_2\) whose
determinant on the three \(Q_0Z_{3,a}\) is nonzero. Both claims remain
open. The retained second-order family must not be saturated into
the source submodule: doing so could absorb the cubic classes that
this test is meant to examine.
