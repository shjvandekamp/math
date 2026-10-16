# Local prefix recovery and a five-term matrix pencil

**Status: audited paper algebra. The remaining source determinant is open.**

This refines the copied-old scalar reduction (SK22)--(SK30) in
[SOURCE24_SCALAR_KERNEL_REDUCTION.md](SOURCE24_SCALAR_KERNEL_REDUCTION.md).
Local recovery below concerns the ambient moment-row space. Membership
in the actual source span requires a separate graph condition.

## Geometry and scalar interpolation

Fix q>=4 old blocks with the generic line and matching geometry used for
W0_q. All old line coefficients are nonzero. For every old line
i=(t,a) and coordinate c, let P_ic be its intersection with X_c=0.
Require that P_ic lies on no other old line. Use a new invertible
A=G diag(1,u,v), with u v nonzero, and lines L_nc. Require also
that all new lines avoid every P_ic; in particular
L_na(P_(ta,a)) is nonzero at every old matching point. These are generic
old/new nonincidence conditions. These formulas are not to be
evaluated directly at G*, whose same-block coordinate-edge points can
coincide.

Let J_q=span{1,X_a/L_ta}, of dimension 3q+1. The prefix space is
I=j diag(X), with each component j_c in J_q; it has dimension 9q+3.
For S in W0_q put k=S diag(X)^(-1). These divisions are already
removed by the ambient output-coordinate factors. At every old line,

\[
 g_i=\left.\frac{L_i k}{X_a}\right|_{L_i=0}
 \tag{PP1}
\]

is regular at each P_ic. At c=a, this uses the old matching condition
after canceling X_a; at c different from a, X_a is a unit there.
Other possible old-line poles avoid P_ic by the stated geometry.

For a scalar component f of k, define E_c f in J_q as follows. Its
coefficient on X_a/L_i is

\[
 e_{ic}(f)=
  \left.\left(\frac{L_i f}{X_a}\right)\right|_{L_i=0}(P_{ic}).
 \tag{PP2}
\]

Choose its constant coefficient so that f−E_c f restricts to zero
on X_c=0. This is possible and unique: after subtracting the pole
terms prescribed by (PP2), the restriction has no old-line poles
and is homogeneous of degree zero, hence constant. The coefficient
at a=c is invisible to that axis restriction, but its divided
matching value in (PP2) is separately prescribed and is essential.
Extend E_c linearly to the span of these scalar components and J_q.
It is a fixed-old, parameter-linear interpolation projection onto J_q.

## The unique ambient pair

Apply E componentwise, using E_c on component c, and define

\[
 j=E(kA^{-1})A,\qquad I_n(S)=j\operatorname{diag}(X),
 \tag{PP3}
\]
\[
 R_n(S)=I_n(S)+(S-I_n(S))K_n^{-1}.
 \tag{PP4}
\]

Then I_n(S) is a prefix row, R_n(S) belongs to W0_q, and

\[
 S=R_n(S)K_n+I_n(S)(I-K_n).
 \tag{PP5}
\]

Here the unsubscripted I in I−K_n is the identity matrix. To check
ambient membership, put z=(k−j)A^(-1). Each z_c vanishes on X_c=0
by construction. Consequently

\[
 (R_n(S))_c=X_cj_c+L_{nc}z_c
 \tag{PP6}
\]

has the output factor X_c. At an old line i=(t,a), the residue of
z_c, divided by X_a, is

\[
 (g_iA^{-1})_c-e_{ic}((kA^{-1})_c).
\]

It vanishes at P_ic. At the matching point P_ia with a=c this
cancels the additional division by X_c in (PP6), retaining the
required matching zero. For a different from c the existing X_a
factor suffices. Row sum zero follows from K_n^(-1)1=1 and
S1=0. Same-block double residues remain zero, cross-pair residues
remain zero-sum, and no new denominator lines occur. The restored
coordinate factors and row sum also give vertex vanishing.

The pair in (PP3)--(PP4) is unique among prefixes I and rows R in
W0_q satisfying (PP5). Subtract two such pairs, so S=0. On an old
line, coordinate divisibility at P_ic fixes the c different from a
components of its prefix residue after multiplication by A^(-1).
The matching condition fixes the last component c=a because
L_na(P_ia) is nonzero. Thus every pole coefficient is zero. The
remaining constant prefix is zero by coordinate divisibility on
the three axes. This proves uniqueness without a source inverse.

## Dependence on the new time factors

Write b=(1,u,v). Expanding (PP3) gives

\[
 j_j=\sum_{b',c}
    \frac{b_j}{b_{b'}}(G^{-1})_{b'c}G_{cj}E_c(k_{b'}),
 \tag{PP7}
\]

and (PP6) gives

\[
 (R_n(S))_i=X_i j_i+
 L_{ni}\sum_{b'}b_{b'}^{-1}(G^{-1})_{b'i}
                         (k_{b'}-E_i(k_{b'})).
 \tag{PP8}
\]

All maps E_c depend only on old parameters. Both recovered rows
therefore depend on the new time factors through the ratios b_j/b_b'.
For S in W01_q, k_2=0. Only the five monomials

\[
 1,\ u,\ v,\ u^{-1},\ v/u
 \tag{PP9}
\]

remain. This is an exact identity, not a truncation near a boundary.

## The actual source-graph condition

Now assume explicitly the shorter-length source-independence premise.
The actual old E/F list is a basis of W0_q. It defines a linear map
I_old:W0_q→prefix: express R in that basis and apply its formal
prefix map (SK13). This map is source-specific and is not replaced
by the ambient recovery operator.

For S in W01_q define

\[
 \mathcal F(u,v)S
   =u\{I_{\rm old}(R_n(S))-I_n(S)\}.
 \tag{PP10}
\]

In fixed old bases this is a (9q+3)-by-r_q polynomial matrix of
the form

\[
 \mathcal F(u,v)=F_0+uF_1+u^2F_2+vF_3+uvF_4.
 \tag{PP11}
\]

Its five coefficient matrices depend only on the old parameters.
The only source-specific operation in constructing them is I_old,
which may require solving the old source system. The polynomial
degree bound does not remove that dependence.

Let C denote the full copied-old source list at length n. By the
uniqueness in (PP5),

\[
 \ker\mathcal F(u,v)
   =\operatorname{span}C\cap W_{01,q}.
 \tag{PP12}
\]

For the forward implication, (PP10)=0 means the recovered ambient
pair is the actual old source graph, so copying its coefficient
vector gives S. Conversely a scalar-zero copied-old row has no
new poles by (SK27); its old row and formal prefix satisfy (PP5),
so uniqueness identifies them with the recovered pair and gives
(PP10)=0. This uses u nonzero and the stated geometry.

Copied-old injectivity under the induction premise and copied-old
scalar fullness (SK25) give the kernel dimension r_q−9q−3.
Consequently F(u,v) has generic rank 9q+3 in the joint old/new
common-G parameter space. Equivalently, fix old parameters in the
additional nonempty generic open where the relevant minors remain
nonzero polynomials in u,v. Geometry and old independence alone
are not asserted to suffice for every fixed old table. It provides explicit
prefix coordinates for the quotient by the inherited scalar-zero
rows, rather than requiring an arbitrary quotient basis.

In particular the scalar-corrected new E columns and the coupled
regular columns V^reg from (SK26)--(SK29) satisfy

\[
 \det[\mathcal F(u,v)E^\circ,
             \mathcal F(u,v)V^{\rm reg}]\ne0
 \tag{PP13}
\]

if and only if the new full source family is independent under the
old induction premise. The three E images are independently known
to be independent; quotienting by them leaves the 9q-square target
(SK30). Formula (PP11) does not claim a degree bound for (PP13):
the corrected boundary columns themselves depend on u,v through
the actual scalar and polar eliminations. Their transversality in
these prefix coordinates remains unproved.

Changing the copied-old scalar right inverse changes each corrected
column only by span(C) intersect W01_q. The transverse map kills this
space, so the polar correction coefficients do not change. Formula
(PP12) then shows that both matrices in (PP13) are independent of that
choice of scalar section. This quotient invariance does not make the
uncorrected inherited transport injective; the obstruction (SK31)
still applies before taking the quotient.

## Polar-only recovery and the old-pole determinant

There is a stronger version which needs no scalar section at all.
Let alpha:W0_n→R^(9q) be the new/old transverse pair-residue map.
At each new/old pair it tests the component transverse to the new
row direction v_na=(A_na0 X_0,A_na1 X_1,A_na2 X_2). Define

\[
 T_n:W_{0,q}\oplus\mathrm{Prefix}_q\longrightarrow W_{0,n},
 \qquad T_n(R,I)=RK_n+I(I-K_n).
 \tag{PP14}
\]

This is an isomorphism onto ker(alpha), under the generic geometry
above. Indeed, if I=j diag(X), its output component i is

\[
 (T_n(R,I))_i
 =X_i\left[j_i+\sum_a\frac{A_{nai}(R_a-I_a)}{L_{na}}\right].
 \tag{PP15}
\]

Thus it has the required coordinate factors. Old matching and
same-block conditions are inherited from R and I. At a new matching
point, R_a−I_a has the factor X_a; there are no same-new-block double
poles. Row sum and vertex vanishing follow as before. Equivalently,
the prefix generators give the local rows X_a e_a(I−K_n) and
P_tab(I−K_n), which satisfy these same ambient conditions. Each new
residue is parallel to v_na, so alpha T_n=0.

The uniqueness proof after (PP6), applied to T_n(R,I)=0, proves
injectivity. The 9q oriented local new-to-old pair rows show alpha
is onto: each has a nonzero transverse residue at its own pair and
none at another pair. With N_q=dim W0_q=9q(q−1)+3q, the dimensions are

\[
 \dim\ker\alpha=N_n-9q=N_q+9q+3.
 \tag{PP16}
\]

This equals the dimension of the domain in (PP14), proving surjectivity.
This argument uses ambient local pair rows, not independence of the
actual ordered source family.

The interpolation recovery (PP3)--(PP4) extends to this whole kernel.
For an existing pair S=T_n(R,I), one has

\[
 (S\operatorname{diag}(X)^{-1}A^{-1})_c
 =(jA^{-1})_c+\frac{R_c-I_c}{L_{nc}}.
 \tag{PP17}
\]

The last term restricts to zero on X_c=0 and has zero divided old-line
datum at P_ic. For i=(t,c) the latter uses the matching zero; for
i=(t,a) with a different from c it uses the output factor X_c.
The new line avoids these points on the generic open. Therefore
applying E_c to the combined component in (PP17) recovers (jA^-1)_c.
Here E_c is extended by the same old-line and axis data; it need
not act on the individual components of S diag(X)^(-1) separately.
The five-monomial formula (PP11) remains a claim for old W01_q only.

Assume again shorter-length source independence, and define on
ker(alpha)

\[
 \Phi_n(S)=I_{\rm old}(R_n(S))-I_n(S).
 \tag{PP18}
\]

This is onto the prefix space, and its kernel is exactly span(C).
In the coordinates (PP14), this is simply the surjective map
(R,I)↦I_old(R)−I, with kernel the actual old source graph.
In particular the three new local E rows satisfy the exact formula

\[
 E_{na}=T_n(0,X_a e_a),\qquad
 \Phi_n(E_{na})=-X_a e_a.
 \tag{PP19}
\]

Let U be the 9q shared-new source columns, V the 9q first-new
source columns, and P=alpha U. On the generic common-G open where
the previously proved polar determinant is nonzero, put
Vbar=V−U P^(-1)alpha V. Then Vbar lies in ker(alpha), and elementary
column elimination gives the exact remaining criterion

\[
 \det\bigl[\operatorname{ResPrefix}_{\rm old}
                       \Phi_n(\overline V)\bigr]\ne0.
 \tag{PP20}
\]

Here ResPrefix_old retains the 9q coefficients c_ib in
j_b=d_b+sum_i c_ib X_a/L_i, discarding the three constants d_b.
The matrix in (PP20) is 9q-by-9q. Under the shorter-length premise,
its nonvanishing is equivalent to independence of the full new
actual E/F list: the polar columns supply 9q pivots, copied-old
columns are exactly ker(Phi_n), and (PP19) supplies exactly the
three constant prefix pivots. No scalar inverse, auxiliary-line
projection, or arbitrary three-dimensional quotient basis occurs.

On W01_q, F(u,v)=u Phi_n. Consequently the scalar-corrected new
E images in (PP13) are exactly −u X_a e_a. This connects both
criteria without asserting a degree bound for their boundary
matrices. The actual source-specific map I_old and the full polar
correction remain in (PP20). Proving its determinant nonzero for
every q is still the unresolved source-independence step.
