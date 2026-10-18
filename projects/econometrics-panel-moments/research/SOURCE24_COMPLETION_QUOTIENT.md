# A completion-space realization of the remaining map

**Status: independently audited paper reformulation; not formalized in Lean.**
This records a useful construction returned by the user-authorized
[GPT-6 Pro background discussion](https://chatgpt.com/c/6ad11f17-4794-83eb-a9b2-6d1dc0543c24).
It is not a proof of all-length transversality or source independence.
Notation and geometry are those of H1–H5 in SOURCE24_INDUCTION.md.

Work over the common-G parameter field with all stated geometry denominators
inverted. Require nonzero coordinates at every intersection of old lines,
including same-block intersections, and no triple intersections. The
same-block requirement is a nonempty generic condition on the common G;
it must not be inferred from cross-block geometry alone.
Let n=9m(m−1), p=9m, and let rho denote the old pair-residue map
with its two zero-sum coordinates at each cross-point. Write T for H2's
normalized divided-line-residue operator, without the incidence term.

## Actual completed products

For iota=(t,a,b), define

\[
 I_\iota=X_aK_t(a,b)e_b,\qquad
 V_\iota=I_\iota-\delta_{ab}X_ae_a.
\]

For an actual old source index alpha=(t,s,a,b), put

\[
 Q_\alpha=I_\iota P_s^{B\setminus\{t\}}
                    -\delta_{ab}X_ae_a.
\]

Thus F_alpha=V_iota−Q_alpha, rho V=0, and TV is the p-dimensional
identity. On the actual source coefficient space,

\[
 \rho Q=-O,\qquad TQ=J_{\rm inc}-T_0=B_0. \tag{C1}
\]

This incorporates the original incidence into actual ordered products.
It does not assign incidence data to an unrelated replacement basis.

## The ambient space and its two observations

Let W consist of homogeneous degree-one rational rows R with the following
properties. Globally, the row H=R diag(X)^{-1} has no poles except simple
poles on the old lines; in particular it has no coordinate-line poles;
its residue on L_uc vanishes at the matching point L_uc=X_c=0; R vanishes
at each coordinate vertex; same-block double residues vanish; and all
cross-block double residues of R are zero-sum. Do not require R itself to
be zero-sum: completed Q rows generally are not.

The rows V and Q have these properties. One convenient check uses

\[
 \widetilde K_t=\operatorname{diag}(X)K_t\operatorname{diag}(X)^{-1}
       =\operatorname{diag}(X_a/L_{ta})A_t.
\]

Every old-line residue of Q diag(X)^{-1} then has the required factor X_c.
The vertex subtraction in Q makes its coordinate-vertex values zero.

**Residue-kernel lemma:** if R belongs to W and rho R=0, then

\[
 R=V(TR). \tag{C2}
\]

Indeed, each residue of H has no remaining poles on its projective line,
so it is a degree-one polynomial row. Matching-point vanishing makes it
X_c k_uc for a constant row k_uc. Subtracting the single-pole rows removes
all poles from H, leaving a constant row; the three vertex conditions fix
that constant. The coefficients are k_uc,d/A_u(c,d), exactly TR.

For lines i=(u,c), j=(v,d) in different blocks, let v_i be their usual
numerator rows and define the elementary two-block row

\[
 E_{i\to j}={A_u(c,d)X_cX_d\over L_i}
                    \left(e_d-{v_j\over L_j}\right).
\]

Its only pair residue is
−A_u(c,d)P_cP_d v_j(P) at P=L_i=L_j=0. The reverse row similarly gives
−A_v(d,c)P_cP_d v_i(P). Thus these two rows define an explicit pairwise
lift Lambda of arbitrary pair data: rho Lambda=Id. They belong to W.

The normalized residues used to compute the correction are

\[
 \begin{split}
 T_{i,k}E_{i\to j}
 &=\delta_{kd}-
 \left[{A_u(c,d)X_d A_v(d,k)\over A_u(c,k)L_j}\right]_{L_i=X_0=0},\\
 T_{j,k}E_{i\to j}
 &=-\left[{A_u(c,d)X_c\over L_i}\right]_{L_j=X_0=0}.
 \end{split} \tag{C3}
\]

All other line rows vanish. Define the normalized lift

\[
 \mathcal U=(I-VT)\Lambda.
\]

Then rho U=Id and TU=0. The lemma gives the canonical decomposition

\[
 R=\mathcal U(\rho R)+V(TR),\qquad
 W\simeq K^n\oplus K^p. \tag{C4}
\]

In particular U is independent of the initially chosen pairwise lift.

## Quotient by the actual completion products

Let Qspace be the span of the actual Q_alpha, and let pi be quotient by
Qspace. Assuming O invertible, (C1) and (C4) give

\[
 W=\mathcal Q\oplus V K^p,\qquad
 \overline V=\pi V:K^p\xrightarrow{\sim}W/\mathcal Q.
\]

For every old coefficient vector y,

\[
 Qy=-\mathcal U(Oy)+V(B_0y).
\]

Consequently the intrinsic formula is

\[
 B_0O^{-1}Z=\overline V^{-1}\pi\mathcal U Z,
 \quad
 \ker(B_0O^{-1}Z)=
 \{\lambda:\mathcal U Z\lambda\in\mathcal Q\}. \tag{C5}
\]

This retains the graph of the actual old source family. Under a source
coefficient change M, both O and B change by M and Qspace stays fixed.
The elementary E rows only construct U; they do not replace Qspace.

## Marked seeds and coordinate transfers

Put r(t)=min(B\{t}) and define 3m rows inside Qspace by

\[
 R_{tA}=-Q_{t,r(t),A,0}
       +c_{tA}\sum_b Q_{r(t),r(r(t)),0,b}.
\]

The normalized first column of A_t is one. Directly taking component two
therefore gives

\[
 (R_{tA})_2=X_0\left[-{X_A\over L_{tA}}(P^t)_{02}
                         +c_{tA}(P_{r(t)})_{02}\right]. \tag{C6}
\]

In the notation U_tA of the induction note, R_tA=U_tA−V_(t,A,0), so their
second components agree. Distinguish these seed rows from the lift U.

For w=e_2G^{-1}, define M_B(R)=(X_B/X_2)R_2 w, and set
A_B=U rho M_B. The raw M_B need not preserve W. Its pair data are always
well-defined because all pair-point coordinates are nonzero, and the lift
returns an element of W. Nodewise,

\[
 \rho_{ij}(M_BR)={P_B\over P_2}(\rho_{ij}R)_2w,
 \qquad
 \mathcal U Z_{tAB}=A_t(A,B)\mathcal A_B(R_{tA}). \tag{C7}
\]

The A_B commute, and A_2^2=w_2 A_2, by rho U=Id and the nodewise rank-one
operator r↦r_2w. No preservation of Qspace follows from this algebra.

## Polynomial realization and the remaining target

Let D_t=prod_a L_ta, D=prod_t D_t, and

\[
 C_t=D_t\widetilde K_t
     =\operatorname{diag}(X_aD_t/L_{ta})A_t.
\]

The injective clearing map Phi(R)=D R diag(X)^{-1} gives polynomial rows
of degree 3m. In particular,

\[
 \Phi(Q_{t,s,a,b})=
 A_t(a,b)X_a{D_t\over L_{ta}}e_b C_s
       \prod_{j\ne t,s}^{\rm ascending}C_j
       -\delta_{ab}D e_a. \tag{C8}
\]

This retains the common G, actual source orders, and explicit incidence.
With incoming rank p already known at odd m>=5, the open target is

\[
 W=\mathcal Q\oplus
    \operatorname{span}\{\mathcal A_B(R_{tA}):t,A,B\}. \tag{C9}
\]

One route is to construct p coefficient functionals annihilating the
polynomials (C8), then prove their p-by-p pairing with (C7) is nonsingular.
Neither (C4), invertibility of O, nor full incoming rank proves (C9).
No all-length nonvanishing or Lean assertion is made in this note.


## Independent review and scope

An independent Astra research reviewer checked C1–C8, including the sign in
C5, the seed identity, and the degree of the cleared products. The review
required the explicit global pole condition and nonzero coordinates at
same-block intersections now stated above. Without the latter, vanishing
double residues of R need not imply the same for H: if L_u0 and L_u1 meet
on X2=0, the row (0,0,X0 X1 X2/(L_u0 L_u1)) exhibits the gap. On the
stated generic geometry, C2 and the subsequent quotient construction pass.
The primary researcher checked the corrected statement before integration.
The complementarity condition C9 remains entirely unproved.
