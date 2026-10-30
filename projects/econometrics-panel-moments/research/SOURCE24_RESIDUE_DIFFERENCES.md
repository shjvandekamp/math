# Residue differences and the marked seed decomposition

**Status: independently audited paper calculations; not Lean formalized.** No Lean
formalization or all-length transversality assertion is made here.
The definitions of the old source rows, the axis feedback operator,
and the auxiliary rows are those of H2 and U1–U6 in
`SOURCE24_INDUCTION.md`. This note does not modify the earlier
checkpoints.

## The domain and its residue data

Write an old line as

\[
 L_i=L_{uc}=X_0+a_1X_1+a_2X_2,
 \qquad a_d=A_u(c,d),\quad a_0=1.
\]

Assume the common normalized matrix has nonzero entries, old lines
are distinct, no three old lines are concurrent, and every intersection,
including same-block intersections, has nonzero effect coordinates. Each coordinate-edge point
\(Q_{i,d}=\{L_i=X_d=0\}\) lies on no other old line.
All projective representatives below can be chosen arbitrarily;
the displayed degree-zero expressions do not depend on their scale.

Let \(\mathscr W_0\) denote the old **zero-sum moment-row space**.
Its elements are homogeneous degree-one rational rows \(F\) with
\(F_0+F_1+F_2=0\), whose components have the form
\(F_d=X_dg_d/D\). The cleared coefficient polynomials vanish at
the matching old base points, and same-block double residues vanish.
These are the established moment-space properties used here. In
particular, on \(L_i\),

\[
 r_d=\frac{\operatorname{Res}_{L_i}F_d}{X_cX_d}
 \tag{R1}
\]

is a homogeneous degree-zero rational function, regular at all three
coordinate-edge points. Its only possible poles are the intersections
with lines in other blocks. Matching division when \(c=d\) is
included: the matching-point vanishing supplies the second factor.

For different blocks, put \(P_{ij}=\{L_i=L_j=0\}\), and define
the vector pair data by

\[
 z_{ij}=(L_iL_jF)(P_{ij}).
\]

Thus \(z_{ij}\) is a zero-sum row, homogeneous of degree three
in the chosen representative of \(P_{ij}\). Denote this pair map
by \(\rho\). The canonical two-local-pair construction from the
induction note lifts arbitrary zero-sum pair data to \(\mathscr W_0\).
No independence of the specified old source family is needed for that
canonical lift. The full pair space has dimension
\(n=9m(m-1)\).

The axis operator is

\[
 T_{i,d}(F)=\frac{r_d(Q_{i,0})}{a_d}.
\]

The zero-sum identity on \(L_i\cap\{X_0=0\}\) gives
\(T_{i,1}=T_{i,2}\). The local single-block row \(E_{u,c}\)
changes all three of these values by \(-1\), so their differences
are unchanged by the old single-block gauge.

## An inverse-free difference operator

On \(L_i\), define

\[
 h_i=\frac{r_0-r_1/a_1}{a_2X_2}. \tag{R2}
\]

This function is homogeneous of degree minus one and has no coordinate
pole. At \(X_2=0\), the identity
\(X_0r_0+X_1r_1+X_2r_2=0\), together with
\(X_0=-a_1X_1\), makes its numerator vanish. At the other two
coordinate points regularity follows directly from (R1).

Its pole coefficient at \(P_{ij}\) is the scale-independent scalar

\[
 \kappa_{ij}(z)=
 \left.
 \frac1{a_2X_cX_2}
 \left(\frac{z_{ij,0}}{X_0}
              -\frac{z_{ij,1}}{a_1X_1}\right)
 \right|_{P_{ij}}. \tag{R3}
\]

Consequently the following partial-fraction identity is exact on
\(L_i\):

\[
 h_i=\sum_{j\text{ in another block}}
                 \frac{\kappa_{ij}(z)}{L_j}. \tag{R4}
\]

Indeed the right side has the same pole coefficient at each allowed
point. Their difference is pole-free and homogeneous of degree minus
one on a projective line, hence zero. Equivalently, after multiplying
by the product of the distinct restricted line forms, this is ordinary
one-variable polynomial interpolation of degree at most one less than
the number of poles.

Define a linear map on the **full vector pair space**, with one output
per old line, by

\[
 (\mathcal D z)_i
 =a_2X_2(Q_{i,0})
       \sum_j\frac{\kappa_{ij}(z)}{L_j(Q_{i,0})}. \tag{R5}
\]

Every coefficient is a parameter-only number obtained at a specified
intersection. Equations (R1)–(R4) prove

\[
 \mathcal D\rho F=(T_{i,0}(F)-T_{i,1}(F))_i,
 \qquad T_{i,1}(F)=T_{i,2}(F). \tag{R6}
\]

There is no old source inverse in (R5). For the fixed-direction scalar
data of H5, simply substitute \(z_{ij,d}=f_{ij}w_d\) in (R3),
where \(w=e_2G^{-1}\). The vector extension is essential below:
the marked seeds need not have pair residues parallel to \(w\).

## Evaluation formula for the incoming columns

Let \(U=U_{tA}\) be one of the auxiliary zero-sum rows of U1.
The proved binary-feedback cancellation says
\(T_{i,1}(U)=T_{i,2}(U)=0\) for every old line. Hence

\[
 R_i=\frac{\operatorname{Res}_{L_i}U_2}{X_cX_2X_0}
 \tag{R7}
\]

is regular at all three \(Q_{i,d}\). At \(Q_{i,0}\), this
uses the additional vanishing of the normalized binary residue before
division by \(X_0\). Thus this value can encode an additional
normal jet; it is not being identified with the earlier insufficient
family of axis observations and one scalar jet.

For the normalized incoming pair data
\(z^B=\rho[(X_B/X_2)U_2w]\), formula (R5) reduces to

\[
 (\mathcal D z^B)_i
     =\sum_{d=0}^2w_d[X_BR_i](Q_{i,d}). \tag{R8}
\]

To check the identity, start on \(L_i\) with

\[
 H=X_B\left(\frac{w_1}{a_1X_1}
                  -\frac{w_2}{a_2X_2}\right)R_i.
\]

Using \(w_0+w_1+w_2=0\) and \(L_i=0\), its old cross-pole
coefficients are exactly (R3) for \(z^B\). Its only additional
poles have coefficients

\[
 \mu_1=\frac{w_1}{a_1}[X_BR_i](Q_{i,1}),\qquad
 \mu_2=-\frac{w_2}{a_2}[X_BR_i](Q_{i,2}).
\]

Thus the unique coordinate-regular function (R4) is
\(H-\mu_1/X_1-\mu_2/X_2\). Multiplying its value at
\(Q_{i,0}\) by \(a_2X_2\) gives (R8), including all three
positive signs in the sum. The actual H5 column also has the nonzero
parameter factor \(A_t(A,B)\), which multiplies (R8).

These calculations determine feedback differences, not source incidence.
In an old source representation, put
\(\widehat J_{i,d}=J_{i,d}-T_{i,1}\), which is invariant under
adding a local single-block row. Then the exact remaining map is

\[
 B_{i,0}=\widehat J_{i,0}-(\mathcal D z)_i,
 \qquad B_{i,1}=\widehat J_{i,1},\qquad
 B_{i,2}=\widehat J_{i,2}. \tag{R9}
\]

Equivalently, its two difference rows are
\(B_{i,0}-B_{i,1}=J_{i,0}-J_{i,1}-(\mathcal D z)_i\)
and \(B_{i,2}-B_{i,1}=J_{i,2}-J_{i,1}\). The common remaining
row is still \(J_{i,1}-T_{i,1}\). The failed incidence-recovery
tests are not bypassed by (R5) or (R8).

## The seed frame and the full-space rank

Assume \(m\ge3\) and the binary invertibility hypotheses of U1–U5.
Index \(3m\) seed columns by \((t,A)\), and write
\(S=\rho(U_{tA})\). Let \(e\) be the coordinate vector
indexed by \((1,0)\). Write \(\gamma^\top\) for the row of
the rank-one feedback calculation U4: it is supported only at
\((m,1),(m,2)\), and

\[
 B_0(U_{tA})=e_{(1,0,0)}\gamma_{tA}.
\]

Extended incidence on these rows is
\(J(U_{tA})=e_{(t,A,0)}\). Their two binary feedback rows are
zero. Therefore (R6) gives the exact identity

\[
 \mathcal D S=I-e\gamma^\top. \tag{R10}
\]

Since \(\gamma^\top e=0\), the rank-one matrix
\(N=e\gamma^\top\) satisfies \(N^2=0\). Hence

\[
 (\mathcal D S)^{-1}=I+e\gamma^\top. \tag{R11}
\]

This does not require \(\gamma\ne0\), nor old source
independence. It proves that the \(3m\) seed pair vectors are
independent and that \(\mathcal D\) has rank \(3m\).
Every pair vector has the unique decomposition

\[
 z=S\eta+z_0,\qquad
 \eta=(I+e\gamma^\top)\mathcal D z,\qquad
 \mathcal D z_0=0. \tag{R12}
\]

On the **entire** old moment-row space, the operator \(T_0\) has
rank exactly \(6m\). Its image has dimension at most \(6m\)
because its two binary output values coincide on every line. The local
\(E_{tA}\) give the \(3m\) common-triple directions, while
the \(U_{tA}\) have zero binary values and the invertible
state-zero matrix (R10). In particular,

\[
 \mathscr W_0=\ker T_0\ \oplus\
              \operatorname{span}\{E_{tA}\}\ \oplus\
              \operatorname{span}\{U_{tA}\}. \tag{R13}
\]

Using the previously established \(\dim\mathscr W_0=n+3m\),
one gets \(\dim\ker T_0=n-3m\). This is a full-space rank
statement. It is not an assertion about the rank of \(T_0\)
on a particular list of old pair-source representatives alone.

## Relation to the actual completion quotient

Use the actual completed products \(Q\), the elementary single-pole
rows \(V\), and the normalized lift \(\mathcal U\) of
`SOURCE24_COMPLETION_QUOTIENT.md`; distinguish \(\mathcal U\)
from the seed rows \(U_{tA}\). One may construct
\(\mathcal U=(I-VT)\Lambda\) using the canonical **zero-sum**
local-pair lift \(\Lambda\). The old residue-kernel description
shows that for every \(F\in\mathscr W_0\),
\(\mathcal U\rho F=F-VT(F)\): different zero-sum lifts differ
by local singles, and \((I-VT)E=0\).

Let \(\sigma\) denote row sum. Since
\(\sum_dV_{tA,d}=-E_{tA}\), equations (R6) imply

\[
 \sigma(\mathcal U z)
       =-\sum_{t,A}(\mathcal D z)_{tA}\,
                                      \sigma(V_{tA,0}). \tag{R14}
\]

Thus \(\mathcal U z_0\) in (R12) is both zero-sum and
\(T\)-zero. This argument does not apply zero-sum identities
to arbitrary completed rows, which generally have nonzero row sum.

The marked completed seeds are
\(R_{tA}=U_{tA}-V_{tA,0}\), and belong to the actual span
\(\mathcal Q\) of completed products. Their pair map is \(S\).
The direct identities above give

\[
 \mathcal U S=R+V_{1,0,0}\gamma^\top. \tag{R15}
\]

Consequently, in the quotient \(\pi\) by the actual
\(\mathcal Q\), (R12) becomes

\[
 \pi\mathcal U z
  =\pi\mathcal U z_0
       +(\gamma^\top\mathcal D z)\,\pi V_{1,0,0}. \tag{R16}
\]

The seed part therefore contributes at most one explicit quotient direction;
the rest lies in the canonical zero-sum, \(T\)-zero lift of
\(\ker\mathcal D\). Formula (R16) itself uses the actual seed
products and does not require \(O^{-1}\). If the old source is
independent and the completion-quotient identification C5 applies,
it gives the corresponding exact decomposition of
\(B_0O^{-1}z\). It does not establish transversality of the
remaining incoming image in \(\ker\mathcal D\).

For clarity, \(\ker(\sigma V)\) consists exactly of triples
constant in the output index on each old line. Vanishing of a line
residue forces \(\sum_da_dc_dX_d\) to be proportional to
\(L_i\), hence all \(c_d\) equal; their sum is \(-E_i\)
and has zero row sum. Thus a proposed equality
\(Qy=\mathcal U z\) imposes the explicit incidence-difference
conditions \(J_1y=J_2y\) and
\(J_0y-J_1y=-\mathcal D z\). The remaining zero-sum information
is not supplied by this row-sum calculation.

## Three exact rational-zero relations at deletion length three

This separate identity qualifies the earlier finite kernel observations.
For \(k=3\), set

\[
 S_j=\sum_{a=0}^2A_1(0,a)A_j(a,2)\frac{X_a}{L_{ja}},
 \qquad j=2,3.
\]

Direct multiplication gives
\((K_1K_j)_{02}=X_2S_j/L_{10}\). Therefore

\[
 S_2(K_1K_3)_{02}-S_3(K_1K_2)_{02}=0 \tag{R17}
\]

as an exact rational-function identity. For any homogeneous linear
form \(h\), the deletion family D1 has the resulting relation

\[
 \ell=0,\quad q_{1a}=0,\quad
 q_{2a}=-hA_1(0,a)A_2(a,2),\qquad
 q_{3a}=hA_1(0,a)A_3(a,2). \tag{R18}
\]

The choices \(h=X_0,X_1,X_2\) give three independent coefficient
relations when the displayed entries are nonzero. These are genuine
rational-zero relations, unlike the previously exhibited single-pole
quotient relations. No claim is made that they exhaust the rational-zero
part of the 11-dimensional \(k=3\) residue kernel.

The finite report correctly stated that each of its chosen kernel basis
vectors had a nonzero ordinary evaluation; it explicitly did not exclude
zero-function linear combinations of those vectors. Equations
(R17)–(R18) now exhibit such combinations. The full \(k=4\)
base certificate and the deletion induction are unaffected. With a
longer common prefix, the analogous coefficients involve
\((e_0P)_a/X_a\), which generally have several rational poles;
the same cancellation does not automatically remain inside the allowed
linear coefficient family.

## Independent review

An independent Astra reviewer checked R1–R18, including the full vector-pair
domain, the signs in R8, the nilpotent inverse in R11, the full-space rank
and direct sum in R13, and the distinction between zero-sum lifts and
completed rows. The primary researcher separately checked the formulas.
The review requested the qualification “at most one” after R16, now applied.
The three exact deletion relations do not contradict the earlier finite
kernel report, which expressly allowed zero-function linear combinations.
The remaining transversality assertion is not proved by these results.

## Exact finite checks

`exploration/source24_residue_differences.py` constructs the full vector-pair
operator directly from R3/R5, then compares D O entrywise with the actual
T-output differences. At the m=3 and m=5 economic fixtures it verifies
R10–R12, projective covariance, the local-single gauge, and the decomposition
using the actual solutions OY=Z. The seed and D ranks are 9 and 15, and the
gauge-extended feedback ranks are 18 and 30. Projecting the incoming columns
to ker D preserves their observed ranks 21 and 45; the two binary output
blocks are unchanged entrywise and have ranks 18 and 30. These are finite
modular checks, not an all-length transversality proof. The primary researcher
reviewed the implementation and its recorded successful bounded run.
