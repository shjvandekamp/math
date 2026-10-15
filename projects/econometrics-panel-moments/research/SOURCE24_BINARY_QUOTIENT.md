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

## Review and remaining work

An independent Astra researcher derived B1–B14; the primary researcher
checked the dimensions, signs, and polynomial formulas. A separate Astra
researcher derived the explicit lift B15–B19, which the first reviewer
audited, including every coordinate point and the matching-state cases.
The primary researcher also checked the lift and constant formula.

The unresolved target is rank \(6m\) of the pairing between (B13) and
the incoming polynomials \(\Phi(F^*)\), followed by the remaining output-zero
directions. Neither this target nor the full regular determinant is proved.
No result in this note is yet formalized in Lean.
