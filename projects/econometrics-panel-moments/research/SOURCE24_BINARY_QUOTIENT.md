# The binary-output quotient and an explicit incoming lift

**Status: audited algebraic reductions; no incoming-rank theorem.**
This identifies an explicit quotient for the two binary output blocks of
the remaining map, and polynomial annihilator conditions for that quotient.
It does not prove that the incoming columns span it. The constructions use
the actual ordered source products throughout.

Use the geometry and spaces of `SOURCE24_COMPLETION_QUOTIENT.md` and
`SOURCE24_RESIDUE_DIFFERENCES.md`, including the global pole condition and
the nonzero-coordinate condition at every old-line intersection. Put
\(n=9m(m-1)\), \(p=9m\), and \(m\ge2\). Let
\(\mathscr W_0\) be the zero-sum moment-row space, \(W\) the completion
space, and \(\mathcal Q\) the span of the actual completed products.
Fix \(r(t)=\min(B\setminus\{t\})\). The identities below hold without
old-source independence. The dimension and quotient-basis conclusions
additionally assume that the old pair-source matrix \(O\) is invertible.

## The explicit subspace to annihilate

The actual rows satisfy

\[
 F_{t,s,a,b}=V_{t,a,b}-Q_{t,s,a,b}. \tag{B1}
\]

Consequently

\[
 Q_{t,s,a,b}-Q_{t,r(t),a,b}
   =-(F_{t,s,a,b}-F_{t,r(t),a,b}). \tag{B2}
\]

For the long empty row \(F_{t,a}\), with word starting at \(t\)
and then following ascending order,

\[
 \sum_bQ_{t,r(t),a,b}=-F_{t,a}. \tag{B3}
\]

Indeed, \(\sum_bV_{t,a,b}=-E_{t,a}\) and
\(F_{t,a}=E_{t,a}+\sum_bF_{t,r(t),a,b}\).

Define \(N\subset\mathscr W_0\) to be the span of all same-label
first-slot differences \(F_{t,s,a,b}-F_{t,r(t),a,b}\), all long empty
rows \(F_{t,a}\), and all selected output-zero rows
\(F_{t,r(t),a,0}\). The differences with \(s=r(t)\) are omitted.

Let \(\sigma\) denote row sum. Since \(F\) is zero-sum,

\[
 \sigma(Qy)=\sigma(VJy). \tag{B4}
\]

The kernel of \(\sigma V\) consists exactly of triples constant in
the output index on each old line. Thus \(Qy\) is zero-sum exactly when

\[
 J_{t,a,0}y=J_{t,a,1}y=J_{t,a,2}y\quad\text{for every }(t,a). \tag{B5}
\]

The corresponding coefficient space has a basis of the same-label
first-slot differences and one selected triple sum per old line. Their
images are the rows in (B2)–(B3), spanning
\(\mathcal Q_0=\mathcal Q\cap\mathscr W_0\). If \(O\) is invertible,
then \(\rho Q=-O\) makes the completed columns independent, and

\[
 \dim\mathcal Q_0=9m(m-2)+3m=n-6m. \tag{B6}
\]

Let \(V_0\) be the span of the \(3m\) rows \(V_{t,a,0}\).
Since \(\sigma\mathcal Q=\sigma W\), as proved below, inclusion gives

\[
 \mathscr W_0/(\mathscr W_0\cap(\mathcal Q+V_0))
       \simeq W/(\mathcal Q+V_0). \tag{B7}
\]

Using \(V_{t,a,0}-Q_{t,r(t),a,0}=F_{t,r(t),a,0}\) shows directly that

\[
 \mathscr W_0\cap(\mathcal Q+V_0)
 =\mathcal Q_0+\operatorname{span}\{F_{t,r(t),a,0}\}=N. \tag{B8}
\]

The actual completion decomposition \(W=\mathcal Q\oplus VK^p\) implies

\[
 \dim N=n-3m,\qquad \dim(\mathscr W_0/N)=6m, \tag{B9}
\]

with quotient basis

\[
 [F_{t,r(t),a,1}],\qquad [F_{t,r(t),a,2}]. \tag{B10}
\]

The signs are positive: modulo \(\mathcal Q\), (B1) gives \([F]=[V]\).

## Polynomial annihilator conditions

Use \(\Phi(R)=DR\operatorname{diag}(X)^{-1}\), where
\(D=\prod_tD_t\), \(D_t=\prod_aL_{ta}\), and
\(C_t=D_t\widetilde K_t\). With \(D_{\widehat t}=\prod_{j\ne t}D_j\),
the actual source polynomials are

\[
 \mathcal P_{t,s,a,b}:=\Phi(F_{t,s,a,b})
 =A_t(a,b)X_a\frac{D_t}{L_{ta}}e_b
 \left[D_{\widehat t}I-
 C_s\prod_{j\ne t,s}^{\rm ascending}C_j\right]. \tag{B11}
\]

The vertex subtractions in \(\Phi(V)\) and \(\Phi(Q)\) cancel here.
The corresponding long-empty polynomial is

\[
 \mathcal P^\emptyset_{t,a}
 =e_a\left[DI-C_t\prod_{j\ne t}^{\rm ascending}C_j\right]. \tag{B12}
\]

Every component in (B11)–(B12) is homogeneous of degree \(3m\).
A linear coefficient functional \(\ell\) on \(\Phi(\mathscr W_0)\)
descends to the binary quotient exactly when

\[
 \begin{aligned}
 \ell(\mathcal P_{t,s,a,b}-\mathcal P_{t,r(t),a,b})&=0,\\
 \ell(\mathcal P^\emptyset_{t,a})&=0,\\
 \ell(\mathcal P_{t,r(t),a,0})&=0.
 \end{aligned} \tag{B13}
\]

Under old-source independence this annihilator has dimension \(6m\).
Prescribing values on the selected output-one/two polynomials gives its
normalized dual basis. These are concrete constraints on actual ordered
polynomials; their statement needs no source inverse.

For odd-length incoming data, the residue split gives
\(z_0=z-S(I+e\gamma^\top)\mathcal Dz\), with \(\mathcal Dz_0=0\).
Then \(\mathcal U z_0\) is zero-sum, and its coordinates in (B10) are
the binary entries of \(B_0O^{-1}z\): the removed seed contribution is
supported in an output-zero completion direction. The required incoming
pairing with a dual basis of (B13) is still unproved.

## An explicit zero-sum lift of the incoming data

For an auxiliary seed \(U=U_{tA}\) and coordinate \(B\), let
\(z=\rho[(X_B/X_2)U_2w]\). Cancel the global factors in

\[
 r=\frac{U_2}{X_0X_2},\qquad
 R_i=\frac{\operatorname{Res}_{L_i}r}{X_c},\qquad
 \mu_{i,d}=[X_BR_i](Q_{i,d}),\quad d=1,2. \tag{B15}
\]

Here \(i=(u,c)\), and the regularity of \(R_i\) at every coordinate
point is R7. After cancellation, \(r\) has only old-line poles.
On \(X_d=0\), the homogeneous degree-zero function

\[
 g_d=X_Br-\sum_i\mu_{i,d}\frac{X_c}{L_i}
\]

has no poles, and is therefore a constant \(\kappa_d\). For \(c\ne d\)
the displayed subtraction cancels the pole coefficient. For \(c=d\)
the restricted residue already vanishes; its \(\mu_{i,d}\) will enforce
the second matching factor in the ambient plane. At \(E_0=(1,0,0)\),

\[
 \kappa_d=\delta_{B0}r(E_0)-\sum_{i=(u,0)}\mu_{i,d}. \tag{B16}
\]

Define

\[
 F_d^*=w_dX_0(g_d-\kappa_d)\quad(d=1,2),\qquad
 F_0^*=-F_1^*-F_2^*. \tag{B17}
\]

Then

\[
 F^*\in\mathscr W_0,\qquad \rho F^*=z,\qquad
 T_{i,1}(F^*)=T_{i,2}(F^*)=0. \tag{B18}
\]

For completeness, its binary line residues are
\(w_dX_0X_c[X_BR_i-\mu_{i,d}]\). Subtracting \(\kappa_d\) makes
the full component vanish on \(X_d=0\), so division by \(X_d\)
has no coordinate pole. When \(c=d\), the bracket vanishes at the
matching point and supplies the additional factor needed after division.
When \(c=0\), the binary normalized residue still contains one factor
\(X_0\), proving (B18) in that case as well. The vertices vanish by
the coordinate identities and the outside factor \(X_0\). Corrections
have only single old poles, so the pair data and same-block conditions
are unchanged. The component-zero assertions follow from the zero-sum
definition and its outside factor \(X_0\).

The canonical completion decomposition and R6 now give

\[
 F^*=\mathcal U z+\sum_iV_{i,0}(\mathcal Dz)_i. \tag{B19}
\]

Thus \(F^*\) directly represents the incoming class in the binary
quotient. One may use \(\Phi(F^*)\) in the pairing (B13); the actual
incoming column includes its nonzero factor \(A_t(A,B)\). This removes
both the source inverse and any interpolation solve from the representative.
The individual correction terms in (B17) need not be moment rows, so they
cannot separately be reduced modulo \(N\).

## An explicit scalar sector with component two zero

Put \(r=9\binom m2\), so \(n=2r\), and let
\(W_{01}=\{R\in\mathscr W_0:R_2=0\}\). For a cross-block
line pair \(i=(t,c),j=(s,d)\), write
\(Q_i=L_i\cap\{X_c=0\}\), \(Q_j=L_j\cap\{X_d=0\}\).
Let \(\ell_{ij}\) be a nonzero linear form vanishing at these
two matching points, and define

\[
 H_{ij}=\frac{X_0X_1\ell_{ij}}{L_iL_j}(e_1-e_0).
 \tag{B20}
\]

The points \(Q_i,Q_j\) are distinct, and
\(\ell_{ij}(P_{ij})\ne0\). Otherwise their joining line
would coincide with \(L_i\), forcing \(Q_j=P_{ij}\),
contrary to the nonzero-coordinate hypothesis. The row (B20) belongs
to \(W_{01}\): the two zeros of \(\ell_{ij}\) supply the
matching factors, its vertices vanish, and its only pair residue is

\[
 \rho_{ij}H_{ij}=P_0P_1\ell_{ij}(P)(e_1-e_0)\ne0.
 \tag{B21}
\]

These rows are a basis of \(W_{01}\). To prove spanning, subtract
their uniquely determined multiples to remove every pair residue of
\(R\in W_{01}\). Coordinate divisibility gives
\(R=X_0X_1f(e_1-e_0)\), with \(f\) homogeneous of degree
minus one and only simple old-line poles. Its pair residues and same-block
double residues vanish, so each line residue is a constant. Matching-point
vanishing of both \(-X_1f\) and \(X_0f\) forces that constant
to be zero, including matching states zero and one. The remaining
pole-free function of negative degree is zero. Thus

\[
 \dim W_{01}=r. \tag{B22}
\]

There is a corresponding complete observation map for component two:

\[
 \mathscr C_2(R)=
 \big((\rho_{ij}R)_2\ ;\ (T_{i,2}R)_i\big)
       \in K^{r+3m}. \tag{B23}
\]

Its kernel is exactly \(W_{01}\). Indeed, zero pair observations
leave each residue of \(R_2/X_2\) equal to \(k_iX_c\).
The normalized observations \(T_{i,2}=0\) kill these constants,
and the vertex condition at \(e_2\) kills the remaining polynomial
constant. Since \(\dim\mathscr W_0=2r+3m\), (B23) is onto.
This lemma needs no old-source inverse.

In particular, if one can prove \(\mathscr C_2(N)=K^{r+3m}\),
then every binary quotient class has a representative in \(W_{01}\),
and under old-source independence

\[
 \mathscr W_0/N\simeq W_{01}/(N\cap W_{01}),\qquad
 \dim(N\cap W_{01})=r-6m. \tag{B24}
\]

The required surjectivity on \(N\) is an additional claim; it does
not follow from (B20)–(B23). It is impossible at \(m=2\) by
dimension. Even where it holds, independence of the specific incoming
classes in the resulting scalar quotient still requires proof.

The exact local script `exploration/source24_component_two.py` constructs
(B23) on the actual generators of N and independently checks every long
empty row from its full ordered word, including its single-block correction.
At the recorded prime and full-old-source economic fixtures it finds:

| m | rank of component-two observations on N | target r+3m | coefficient kernel dimension |
|---:|---:|---:|---:|
| 3 | 27 | 36 | 18 |
| 4 | 66 | 66 | 30 |
| 5 | 105 | 105 | 60 |

The full row minors at m=4,5 lift to characteristic zero after clearing
denominators, so the conditional scalar representation (B24) is realized
at those rational fixtures and generically at those two fixed lengths.
The m=3 modular deficiency alone is not an upper-bound proof over the reals;
the path factorization B38–B42 below now supplies that upper bound.
The run took 0.597 seconds and 21,217,280 bytes maximum RSS; results are
in `exploration/source24-component-two-results.json`. The primary
researcher reviewed the implementation. No all-length surjectivity follows.

## Why row sum alone cannot produce the annihilators

Let \(\Psi(P)=\sum_dX_dP_d\), so
\(\Psi(\Phi(R))=D\sigma(R)\). The \(6m\) rows
\(\sigma(V_{t,a,1})\), \(\sigma(V_{t,a,2})\) are independent:
taking the unique residue on \(L_{ta}\) would require
\(A_t(a,1)c_1X_1+A_t(a,2)c_2X_2\) to be divisible by
\(L_{ta}=X_0+A_t(a,1)X_1+A_t(a,2)X_2\). Its missing \(X_0\)
term forces both coefficients to vanish. They span \(\sigma(W)\),
because the unnormalized local-pair lift is zero-sum and normalization
changes row sum only by combinations of \(V\). Moreover \(\sigma Q=\sigma VJ\),
and every shared label occurs, so

\[
 \sigma(\mathcal Q)=\sigma(W). \tag{B14}
\]

Any polynomial functional factoring only through \(\Psi\) and annihilating
the completed products therefore vanishes on the entire completion space.
Row-sum conditions alone cannot provide nonzero completion annihilators.

## A parity-aware component-two annihilator reduction

Let Lcol collect the 3m long-empty rows F_ta, distinct from local E_ta.
Set

\[
 A_L=\rho_2(\mathrm{Lcol}),\qquad B_L=T_2(\mathrm{Lcol}). \tag{B25}
\]

Assume m>=3, the full old-line geometry, positive normalized
G=(1,alpha,beta), and alpha1 beta2−alpha2 beta1 !=0. Retain the
binary theorem's nonzero, adjacent-distinct time parameters and distinct
binary poles, including distinctness from each row-zero axis point.
For the actual move-t-first product P_t,

\[
 (B_L)_{(u,c),(t,a)}=-\left[
 \frac{X_a\operatorname{Res}_{L_{uc}}(P_t)_{a2}}
      {A_u(c,2)X_cX_2}\right]_{Q_{uc,0}}. \tag{B26}
\]

Use the regular extension when c=0. Ordering state-zero rows and columns
first gives

\[
 B_L=\begin{pmatrix}D&H\\0&\widetilde M\end{pmatrix},\qquad
 D_{ut}=-\delta_{ut}\prod_{j\ne t}d_j(Q_{t0,0}), \tag{B27}
\]

where d_j is the determinant of the binary restriction of K_j. In the
lower-left block the initial X0 factor remains after matching division,
so the value is zero. In the upper-left block a later row-zero pole has
an additional X0 from entering state zero. Only the first pole survives;
its binary zero-sum residue is multiplied by each later determinant.
All factors in D are nonzero under the assumptions.

For the upper-right block, parametrize L_u0 by X0=x, X2=1 and
X1=−(x+A_u(0,2))/A_u(0,1). For a=1,2 the exact entry is

\[
 H_{u,(t,a)}=-\frac1{A_u(0,2)}
   \left.\frac{d}{dx}\left[X_a(x)
          \operatorname{Res}_{L_{u0}}(P_t)_{a2}(x)\right]\right|_{x=0}.
 \tag{B28}
\]

The differentiated numerator vanishes at zero. If u=t its residue is
identically zero because the initial state is not zero. No rank assumption
on H is needed.

To identify the remaining block, set X0=0, X1=1, X2=z,
c_t=beta1 v_t/(alpha1 u_t), and rho=alpha1 beta2/(alpha2 beta1).
The binary kernels are

\[
 \overline K_t(z)=\begin{pmatrix}
 (1+c_tz)^{-1}&c_tz(1+c_tz)^{-1}\\
 (1+\rho c_tz)^{-1}&\rho c_tz(1+\rho c_tz)^{-1}
 \end{pmatrix}.
\]

Use the actual move-first order in Pbar_t, and put
phi_t1=(Pbar_t)_12, phi_t2=z(Pbar_t)_22. For c=1,2 let
z_uc=−A_u(c,1)/A_u(c,2), and
Mres_((u,c),(t,a))=[(A_u(c,1)+A_u(c,2)z) phi_ta(z)] at z_uc.
Equation B26 gives the exact row scaling

\[
 \widetilde M_{(u,c),(t,a)}=
 -\frac{M^{\rm res}_{(u,c),(t,a)}}
 {A_u(c,2)X_c(0,1,z_{uc})z_{uc}}. \tag{B29}
\]

Write q_t=(Pbar_t)_12 and r_t=(Pbar_t)_21. The second family is
phi_t2=z−z r_t, so its residues equal those of −z r_t.
Both q_t and z r_t vanish at zero, are bounded at infinity, and have
only the stated simple poles. Their residue map is injective: vanishing
residues leave a bounded pole-free function, hence a constant, and its
value at zero makes it zero. The established binary rank theorem gives

\[
 \operatorname{rank}B_L=
 \begin{cases}3m,&m\text{ odd},\\3m-2,&m\text{ even}.\end{cases} \tag{B30}
\]

This uses no old-source inverse. For an annihilator
Lambda(R)=a^T rho2 R+beta^T T2 R, long-empty constraints are

\[
 a^TA_L+\beta^TB_L=0. \tag{B31}
\]

The exact seed identity F_t,r(t),A,0=U_tA+c_tA F_r(t),0 and T2 U=0
then reduces all selected output-zero constraints, in either parity, to

\[
 a^T\rho_2U_{tA}=0. \tag{B32}
\]

For odd m, eliminate every axis coefficient using
beta^T=−a^T A_L B_L^-1 and define

\[
 \mathcal P_2(F)=\rho_2F-A_LB_L^{-1}T_2F. \tag{B33}
\]

The remaining conditions are exactly B32 and

\[
 a^T\mathcal P_2(F_{t,s,A,b}-F_{t,r(t),A,b})=0. \tag{B34}
\]

Equivalently,

\[
 \operatorname{rank}\mathscr C_2(N)=3m+
 \operatorname{rank}[\rho_2(U)\mid
   \mathcal P_2(F_{t,s,A,b}-F_{t,r(t),A,b})]. \tag{B35}
\]

The remaining matrix has r=9 choose(m,2) rows. No full-row-rank assertion
is supplied by this elimination.

For even m choose full two-column and two-row kernel bases R_L,L_L of
B_L. Equation B31 is solvable for beta exactly when

\[
 a^T A_LR_L=0. \tag{B36}
\]

Its solutions then have the form beta^T=beta_particular^T(a)+nu^T L_L.
The selected output-zero rows do not constrain these two remaining
axis coefficients. A necessary condition for surjectivity is therefore

\[
 \operatorname{rank}[L_LT_2(F_{t,s,A,b}-F_{t,r(t),A,b})]=2. \tag{B37}
\]

Otherwise a nonzero pure-axis annihilator survives every generator of N.
First-slot differences are essential to remove this ambiguity. Neither
B35 nor B37 proves uniform surjectivity or the observed m=3 deficiency.

The extended exact script checks B27's triangular block, B28's matching
first derivatives, B29's binary residue scaling and B32's seed subtraction.
At m=3,4,5 it finds long-empty ranks 9,10,15 respectively. The odd
remaining matrices have ranks 18 and 90; at m=4 the difference columns
remove both pure-axis directions in B37. The complete extended run took
0.719 seconds and 23,363,584 bytes maximum RSS. The primary researcher
reviewed these additions; all statements remain fixed-fixture certificates.

## A path factorization explains the three-block deficiency

For a state assignment a=(a_1,...,a_m), define

\[
 \phi_a=X_2\prod_{t=1}^m\frac{X_{a_t}}{L_{t,a_t}},\qquad
 c_\omega(a)=\left(\prod_{j=1}^{m-1}
 A_{\omega_j}(a_{\omega_j},a_{\omega_{j+1}})\right)
 A_{\omega_m}(a_{\omega_m},2). \tag{B38}
\]

Expanding the actual transition word, without commuting any factors, gives

\[
 (\widehat Q_{t,s,a,b})_2=
 \sum_{\substack{\mathbf a_t=a\\\mathbf a_s=b}}
 c_{(t,s,\mathrm{ascending\ remainder})}(\mathbf a)\phi_{\mathbf a}.
 \tag{B39}
\]

The analogous expansion of X_a e_a P_t restricts only the initial state
at block t. For every order the all-two coefficient is the same number
C=prod_t A_t(2,2). Replace just that path by

\[
 \psi_a=\phi_a\quad(a\ne(2,\ldots,2)),\qquad
 \psi_{(2,\ldots,2)}=\phi_{(2,\ldots,2)}-X_2/C. \tag{B40}
\]

Every component-two generator of N is a parameter-only combination of
these 3^m functions. For selected output-zero sources the prefix component
is zero and the all-two path is absent. For first-slot differences the
prefixes cancel, as do the identical all-two coefficients. For long-empty
rows the term delta_(a,2) X2 is exactly the correction supplied by B40.
This establishes the factorization for the three actual generator types,
including their signs and complete word orders.

By B23, the observation map C2 has precisely the kernel R2=0, so its
rank on N equals the dimension of the scalar component-two image. Hence

\[
 \operatorname{rank}\mathscr C_2(N)
 \le\min\{9\tbinom m2+3m,\ 3^m\}. \tag{B41}
\]

This needs neither a conic specialization nor an old-source inverse.
At m=3 it proves the upper bound 27. The existing nonzero 27-minor then
proves generic rank exactly 27 and a structural deficiency of nine in the
36-dimensional observation target. At m=4 the bound 81 exceeds the target
66, so this particular obstruction no longer prevents surjectivity.

For a polynomial formulation put D=prod_(t,a) L_ta and
f_ta=X_a prod_(b!=a) L_tb. Clearing B40 and dividing by X2 gives

\[
 \frac{D\psi_a}{X_2}=\prod_t f_{t,a_t}
       -\boldsymbol1_{a=(2,\ldots,2)}D/C. \tag{B42}
\]

These degree-3m forms vanish at each block's three line intersections,
at its three matching points L_ta=X_a=0, and at e2. The formula offers
a polynomial spanning problem, but counting these 6m+1 points alone
does not prove their independent conditions or that the path products
span every form satisfying them. Even full path spanning would leave
the rank of the actual N coefficient combinations to establish.

## Review and remaining work

An independent Astra researcher derived B1–B14; the primary researcher
checked the dimensions, signs, and polynomial formulas. A separate Astra
researcher derived the explicit lift B15–B19, which the first reviewer
audited, including every coordinate point and the matching-state cases.
The primary researcher also checked the lift and constant formula.
The primary researcher derived B20–B24; an independent Astra reviewer
checked the coordinate factors, pair basis, observation kernel, and
dimension argument. B24 is explicitly conditional on surjectivity for N.
An independent Astra researcher derived B25–B37; the primary researcher
checked the matching zero, binary residue scaling, parity hypotheses,
and annihilator elimination against the established binary theorem.
The same independent researcher derived B38–B41. The primary researcher
checked the ordered-path coefficients, all-two normalization and rank
factorization, and derived the explicit clearing formula B42.

The unresolved target is rank \(6m\) of the pairing between (B13) and
the incoming polynomials \(\Phi(F^*)\), followed by the remaining output-zero
directions. Neither this target nor the full regular determinant is proved.
No result in this note is yet formalized in Lean.
