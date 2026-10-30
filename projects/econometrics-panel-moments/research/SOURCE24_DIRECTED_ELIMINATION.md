# Directed residue coordinates and actual-source elimination

**Status: locally audited paper reduction; not Lean formalized.** The
proposed reduction was supplied from the
[Pro6 discussion](https://chatgpt.com/c/6ad12957-2a74-83eb-9854-70c4e7428c56).
The derivation below checks that supplied outline against the actual source,
local-pair, and seed definitions in `SOURCE24_COMPLETION_QUOTIENT.md`,
`SOURCE24_RESIDUE_DIFFERENCES.md`, and U1–U5 of
`SOURCE24_INDUCTION.md`. The local audit covers signs, scaling, source
indices, and the finite-dimensional elimination. It asserts no new finite
rank certificate or all-length independence theorem.

Work over the normalized common-G parameter field \(\mathbb K\), with old blocks
\(B=\{1,\ldots,m\}\), \(m\ge3\), and
\(A_t(a,0)=1\). Retain the geometry and nonzero-denominator assumptions of
the cited notes, including nonzero coordinates at every old-line
intersection, no triple intersections, and the binary invertibility
conditions defining the marked seeds. Put
\(n=9m(m-1)\) and \(q=3m\). The old pair space has dimension \(n\).

## Pair orientation and directed coordinates

Index old lines by \(i=(u,c)\), and write

\[
 L_i=X_0+a_1X_1+a_2X_2,
 \qquad v_i(X)=(X_0,a_1X_1,a_2X_2).
\]

For every unordered pair of lines \(i=(u,c)\), \(j=(v,d)\) in
different blocks, fix one representative \(P_{ij}\) of their
intersection. Use this same representative for both directed edges.
For example, order the lines lexicographically and take the cross product
of their coefficient rows in that order. A vector pair residue is

\[
 z_{ij}=(L_iL_jF)(P_{ij})
       =\zeta_{ij,i}v_i(P_{ij})+\zeta_{ij,j}v_j(P_{ij}). \tag{D1}
\]

The two numerator rows are independent and zero-sum at the intersection,
so (D1) gives coordinates on the two-dimensional zero-sum pair space.
The coefficients \(\zeta_{ij,i}\), \(\zeta_{ij,j}\) are local to this
pair; they are not single global coefficients attached to the lines.

Define

\[
 h_{i\to j}=-\frac{\zeta_{ij,j}}{P_{ij,0}P_{ij,c}},
 \qquad
 h_{j\to i}=-\frac{\zeta_{ij,i}}{P_{ij,0}P_{ij,d}}. \tag{D2}
\]

Thus the outgoing edge uses the coefficient of the **other** numerator
row, and the matching coordinate in its denominator belongs to its
starting line. All denominators are nonzero. The inverse is

\[
 \zeta_{ij,i}=-P_{ij,0}P_{ij,d}h_{j\to i},
 \qquad
 \zeta_{ij,j}=-P_{ij,0}P_{ij,c}h_{i\to j}. \tag{D3}
\]

Under \(P\mapsto\lambda P\), a raw pair residue scales by
\(\lambda^3\), its numerator basis by \(\lambda\), and each
\(\zeta\) by \(\lambda^2\). The denominators in (D2) scale by
\(\lambda^2\) as well. Consequently the directed coordinates are
projectively invariant. Reversing a cross-product orientation is covered
by this rule; coefficients extracted at one representative must not be
combined with a different, unadjusted residue vector.

The difference operator of R3–R6 becomes

\[
 (\mathcal Dz)_i=\sum_{j:\,\operatorname{block}(j)\ne u}
                         h_{i\to j}
 =-\sum_j\frac{\zeta_{ij,j}}{P_{ij,0}P_{ij,c}}. \tag{D4}
\]

Here is a direct check of its coefficient and sign. Write the other line
as \(L_j=X_0+b_1X_1+b_2X_2\), and first choose

\[
 P=(a_1b_2-a_2b_1,\ a_2-b_2,\ b_1-a_1),
 \qquad Q_i=(0,a_2,-a_1).
\]

In R3, the coefficient of \(v_i(P)\) is zero, and the coefficient of
\(v_j(P)\) is
\((a_1-b_1)/(a_1a_2P_cP_2)\). The axis multiplier in R5 is
\(a_1a_2/(a_1b_2-a_2b_1)\). Their product is
\(-1/(P_0P_c)\), as in (D4). Projective covariance gives the same
formula at any chosen representative.

Equivalently, the actual elementary local row

\[
 E_{i\to j}=\frac{A_u(c,d)X_cX_d}{L_i}
                 \left(e_d-\frac{v_j}{L_j}\right)
\]

has pair residue \(-A_u(c,d)P_cP_dv_j(P)\), hence
\((\mathcal D\rho E_{i\to j})_i=A_u(c,d)P_d/P_0\).
Every other output of \(\mathcal D\rho E_{i\to j}\), including the
one at \(j\), is zero. This agrees with the local-lift normalization.

## Explicit coordinates on the kernel of the difference operator

There are \(3(m-1)\) outgoing edges from each of the \(q\) lines.
Define \(r(t)=\min(B\setminus\{t\})\), and for each
\(i=(u,c)\) omit the edge to \(j(i)=(r(u),0)\). On
\(\ker\mathcal D\), retain all the other directed coordinates:

\[
 \Xi:\ker\mathcal D\longrightarrow \mathbb K^{n-q}. \tag{D5}
\]

This is an explicit isomorphism. Reconstruct the omitted coordinate by

\[
 h_{i\to j(i)}=-\sum_{j\ne j(i)}h_{i\to j}, \tag{D6}
\]

then reconstruct every pair vector using (D3) and (D1). The constraints
in (D4) involve disjoint outgoing coordinate sets, so there are exactly
\(q\) independent constraints. In particular \(\mathcal D\) is
surjective and \(\dim\ker\mathcal D=n-q\), without any old-source
independence assumption. This coordinate argument itself also works for
\(m=2\); the subsequent seed identities retain their \(m\ge3\)
hypothesis.

## A change of basis using the actual marked seeds

Index the actual source coefficient space by
\(\alpha=(t,s,A,b)\), where \(t\ne s\), and write its standard
vectors as \(e_\alpha\). Let \(O\) be the actual pair-source matrix,
and \(B_{\rm bin}\) the output-one and output-two rows of the actual
feedback matrix \(B_0=J_{\rm inc}-T_0\).

For each seed label \((t,A)\), use the source coefficient vector

\[
 Y_{tA}=e_{(t,r(t),A,0)}
       -c_{tA}\sum_{b=0}^2e_{(r(t),r(r(t)),0,b)}. \tag{D7}
\]

The normalization \(A_t(A,0)=1\) is used here. Before that
normalization, the first coefficient would be \(1/A_t(A,0)\).
Since
\(F_{r,0}=E_{r,0}+\sum_bF_{r,r(r),0,b}\), the actual seed
\(U_{tA}\) equals the source combination (D7) minus
\(c_{tA}E_{r(t),0}\). The local row has both
\(\rho E=0\) and \(B_0E=0\). Thus the established seed identities
give, with \(S=\rho(U_{tA})\),

\[
 OY=S,\qquad B_{\rm bin}Y=0. \tag{D8}
\]

Let \(C\) be the matrix of all standard source columns outside the
\(q\) anchors \((t,r(t),A,0)\). The anchor block of \(Y\) is
\(I-K\), where

\[
 K_{(r(t),0),(t,A)}=c_{tA}, \tag{D9}
\]

with all other entries zero. Its image lies in the seed-label rows with
state zero, and it annihilates every column with state zero because
\(c_{t0}=0\). Therefore \(K^2=0\) and
\((I-K)^{-1}=I+K\). After placing anchor rows first, the full change
of basis has the form

\[
 [Y,C]=\begin{pmatrix}I-K&0\\ *&I\end{pmatrix}. \tag{D10}
\]

It is invertible independently of \(O\). The corrections with
\(b=1,2\) occupy non-anchor rows and do not change (D9).

## Projection, triangular reduction, and the binary map

The audited marked-seed identity is

\[
 \mathcal DS=I-e\gamma^\top,\qquad
 \gamma^\top e=0,\qquad
 R:=(\mathcal DS)^{-1}=I+e\gamma^\top, \tag{D11}
\]

where \(e\) is the line coordinate \((1,0)\). Define

\[
 P=I-SR\mathcal D. \tag{D12}
\]

Then \(P^2=P\), \(\operatorname{im}P=\ker\mathcal D\), and
\(\ker P=\operatorname{im}S\). None of these statements assumes
\(O\) invertible. For any incoming matrix \(Z\) in the same actual
pair coordinates, put

\[
 \widehat O=\Xi POC,\qquad \widehat Z=\Xi PZ. \tag{D13}
\]

The square matrix \(\widehat O\) has size \(n-q\). Define an
isomorphism on the full pair space by

\[
 \mathcal Tz=(\mathcal Dz,\Xi Pz),\qquad
 \mathcal T^{-1}(a,b)=SRa+\Xi^{-1}b. \tag{D14}
\]

Using (D8) gives the exact triangular identity

\[
 \mathcal T\,O[Y,C]
 =\begin{pmatrix}
     \mathcal DS&\mathcal DOC\\
     0&\widehat O
   \end{pmatrix}. \tag{D15}
\]

Both exterior changes of coordinates and \(\mathcal DS\) are
invertible. Consequently

\[
 O\text{ is invertible}\quad\Longleftrightarrow\quad
 \widehat O\text{ is invertible}. \tag{D16}
\]

Under these equivalent conditions, \(POC\) is an isomorphism onto
\(\ker\mathcal D\). Decompose the actual source solution as
\(O^{-1}Z=Y\eta+C\beta\). Applying \(\Xi P\) gives
\(\beta=\widehat O^{-1}\widehat Z\); applying
\(B_{\rm bin}\) and using (D8) gives

\[
 B_{\rm bin}O^{-1}Z
   =(B_{\rm bin}C)\widehat O^{-1}\widehat Z. \tag{D17}
\]

This is a reduction of the actual binary feedback map. It neither proves
that \(\widehat O\) is invertible nor that the reduced incoming map in
(D17) has the required rank. In particular, no source inverse has been
replaced by an unrelated residue basis: the matrices \(Y\) and \(C\)
are explicit changes of the original source coefficients, and (D15)
records the remaining invertibility question exactly.
