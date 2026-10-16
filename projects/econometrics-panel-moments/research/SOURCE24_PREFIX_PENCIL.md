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

## Sparse actual seeds before inverse-append transport

The [Pro prefix investigation](https://chatgpt.com/c/6ad180d3-2498-83eb-9d9b-1a1397221300)
gave the following source-specific seed calculation, subsequently
checked locally and independently. Keep the shorter-source independence
premise when interpreting I_old as an intrinsic map on old rows.
Let r(t) be the least old time other than t, and T_t the increasing
product of the old kernels omitting t. The old cycle rows satisfy

\[
 H_{sd}=X_de_d(I-P_s^{[q]})
       =E_{sd}+\sum_e F_{s,r(s),d,e},\qquad
 I_{\rm old}(H_{sd})=X_de_d.
 \tag{PP21}
\]

For new state b set h_b=L_nb, v_b=A_n(b,:)diag(X), f_b=X_b/h_b.
For old line i=(t,a), put Z_i=X_a/L_ta and define the sparse old row

\[
 B_{ib}=\sum_d\frac{A_n(b,d)}{A_t(a,d)}F_{t,r(t),a,d}
       =Z_i v_b(I-T_t),\qquad I_{\rm old}(B_{ib})=Z_i v_b.
 \tag{PP22}
\]

These use the actual increasing suffix and constant-in-X coefficients.
The new boundary rows have the exact decomposition

\[
 U_{s,b,d}=A_n(b,d)f_bH_{sd},\qquad
 \frac{V_{t,a,b}}{A_t(a,b)}=f_bB_{ib}+Z_iE_{nb}.
 \tag{PP23}
\]

Each row in this display has only the new pole h_b. The invertible
polar matrix is therefore block diagonal by b. Its correction picks
a unique H_ib in the span of the 3q cycle rows, giving

\[
 \frac{\overline V_{t,a,b}}{A_t(a,b)}
   =f_b R^*_{ib}+Z_iE_{nb},\qquad R^*_{ib}=B_{ib}-H_{ib}.
 \tag{PP24}
\]

The cycle rows are independent because a relation among them would
give a kernel in a polar b-block. Their prefixes are polynomial
coordinate rows. Consequently the old-pole prefix coefficients of
I_old(R*_ib) are exactly those of Z_i v_b. Across all i,b their
9q-square matrix has a block A_n (up to transposition) for each of
the 3q old lines, and determinant ±det(A_n)^(3q), which is nonzero.
This seed result retains the shared-new correction and does not
require inversion of the complete old source matrix.

The transport is still essential. The row Z_i E_nb has ambient
preimage (0,Z_i X_b e_b). Thus f_b R*_ib is polar-zero by (PP24),
and the normalized target column in (PP20) is exactly

\[
 \operatorname{ResPrefix}_{\rm old}\left[
 I_{\rm old}(R_n(f_bR^*_{ib}))-I_n(f_bR^*_{ib})-Z_iX_be_b
 \right].
 \tag{PP25}
\]

Membership in the ambient transverse kernel follows for these
specific seeds from (PP24); multiplication by f_b need not preserve
that space for arbitrary old rows. In general R_n(f_b R*_ib) is
not R*_ib. The explicitly nonzero seed determinant therefore does
not establish nonvanishing of (PP25). Likewise, the polynomial
prefix of an unmultiplied cycle row does not justify dropping its
multiplied, transported defect. A rank-preserving property of the
ambient transport is proved below. Preservation of the source-prefix
defect determinant remains open.

## Single-pole transport on the ambient quotient

The [single-pole investigation](https://chatgpt.com/c/6ad18c36-7d58-83eb-b6de-cc8aa4aeef65)
suggested the following stronger transport statement. The proof uses the
canonical ambient E/local-pair basis, rather than independence of the
ordered source family. Impose the previous generic geometry, including
that every new line avoids every old cross-block intersection.
Write \(\mathcal E_q=\operatorname{span}\{E_{ta}\}\). Fix b, and let
\(\beta_b(R)\) be the 3q new/old transverse pair coordinates of f_b R
at the pairs \(h_b=L_i=0\). Multiplication by f_b takes W0_q into
W0_n: it preserves the old matching conditions and adds the factor X_b
at the only new matching point. It introduces only the new pole h_b.
Put

\[
 D_b=\ker\beta_b\subset W_{0,q}.
 \tag{PP26}
\]

On E_i, the only possibly nonzero coordinate of beta_b is its own
old line i=(t,a). Its double residue is
\(-X_aX_b v_i\), transverse to v_b: the two line coefficient rows
are independent, and all coordinates at their intersection are nonzero.
Thus beta_b restricted to E_q is diagonal and invertible. In particular

\[
 W_{0,q}=\mathcal E_q\oplus D_b,\qquad
 \dim D_b=N_q-3q.
 \tag{PP27}
\]

Let Omega collect the two-dimensional old cross-block double residues.
The canonical ambient basis proves that ker(Omega)=E_q and that Omega
identifies W0_q/E_q with the direct sum of those two-dimensional
zero-sum row spaces. For R in D_b define
\(Q_b(R)=R_n(f_bR)\) and \(I_b(R)=I_n(f_bR)\).
These are defined by (PP14), since f_b R has zero transverse residue.
At an old cross-block point P_ij, I_b has no double pole and K_n^{-1}
is regular. Consequently (PP4) gives the exact block formula

\[
 \Omega_{ij}Q_b(R)
   =f_b(P_{ij})\,\Omega_{ij}(R)K_n(P_{ij})^{-1}.
 \tag{PP28}
\]

Every block is invertible. Right multiplication preserves the zero-sum
plane because K_n 1=1; its determinant on that plane is
1/det(K_n), since the induced action on the row-sum quotient is the
identity. In matching domain and codomain residue bases, the block
determinant is

\[
 \frac{f_b(P)^2}{\det K_n(P)}
 =\frac{X_b(P)^2h_0(P)h_1(P)h_2(P)}
 {h_b(P)^2\det(G)uvX_0(P)X_1(P)X_2(P)}\ne0.
 \tag{PP29}
\]

Combining (PP27)--(PP29), the map
\(D_b\to W_{0,q}/\mathcal E_q,\ R\mapsto[Q_b(R)]\)
is an isomorphism. This is a uniform statement for the ambient transport;
no old source-matrix inverse is used.

On the common-G open where the shared-new polar theorem holds, let
H_q be the span of the cycle rows H_sd. The restriction beta_b|H_q is
also invertible, so W0_q=H_q direct-sum D_b. If Pi_b projects along
H_q onto D_b, the induced map

\[
 W_{0,q}/H_q\longrightarrow W_{0,q}/\mathcal E_q,
 \qquad [R]\longmapsto[Q_b(\Pi_bR)]
 \tag{PP30}
\]

is an isomorphism. In particular R*_ib=Pi_b B_ib. For a fixed b,
the 3q seeds R*_ib are independent by their distinct old-pole prefixes
in (PP22)--(PP24). Their transported rows are therefore independent
modulo E_q. This conclusion uses old source independence to interpret
those prefixes. It does not identify their source-graph defects with
an invertible image of the seed-prefix matrix.

## The recovered component and the actual completion defect

For R in D_b, set k=R diag(X)^{-1}, w=k A^{-1}, and
g=E(f_b w), so I_b=g A diag(X)=sum_c g_c v_c. The b-component
of f_b w vanishes on X_b=0. Its divided datum on every old line
also vanishes there: after cancellation of X_a the old matching
condition makes w's datum regular, while f_b supplies X_b and h_b
is a unit. Therefore both the pole coefficients and constant
coefficient of g_b vanish. Thus

\[
 g_b=0,\qquad
 I_b=\sum_{c\ne b}g_cv_c,\qquad
 Q_b(R)=f_bRK_n^{-1}
       +\sum_{c\ne b}g_c(v_c-h_ce_c).
 \tag{PP31}
\]

Each g_c is a whole element of J_q, of dimension 3q+1. The two
components in (PP31) are not a rank-two correction over constant
coefficients.

For the next identities retain the actual copied-old convention
I_old(E_ta)=E_ta and I_old(F_tsab)=X_a K_t(a,b)e_b. In particular
this is not the convention that assigns X_a e_a to an old E row.
Under old source independence define
\(\operatorname{Tail}_q(R)=I_{\rm old}(R)-R\).
One has W0_q intersect Prefix_q=E_q: a zero-sum prefix has each
old-line coefficient vector proportional to the corresponding line
coefficient vector, and its polynomial part then gives a sum of E's.
Since I_old is the identity on E_q, this proves

\[
 \ker\operatorname{Tail}_q=\mathcal E_q,\qquad
 \operatorname{im}\operatorname{Tail}_q
       \cap\mathrm{Prefix}_q=\{0\}.
 \tag{PP32}
\]

Indeed, if Tail_q(R) is a prefix, so is R; hence R belongs to E_q
and its tail is zero. Consequently the fixed-b transported tails
Tail_q(Q_b(R*_ib)) are independent by (PP30). This still gives no
independence after subtraction of the following known rows.

Write R*_ib=Z_i v_b-W_ib, where
W_ib=Z_i v_b T_t+H_ib, and set Q_ib=Q_b(R*_ib), I_ib=I_b(R*_ib).
The full normalized prefix defect in (PP25), before discarding its
three constant coordinates, obeys

\[
 \begin{split}
 \Delta_{ib}&=I_{\rm old}(Q_{ib})-I_{ib}-Z_iX_be_b,\\
 \Lambda_{ib}&=(f_bW_{ib}+I_{ib})K_n^{-1},\\
 Q_{ib}&=Z_iX_be_b+I_{ib}-\Lambda_{ib},\\
 \Delta_{ib}&=\operatorname{Tail}_q(Q_{ib})-\Lambda_{ib}.
 \end{split}
 \tag{PP33}
\]

These follow from v_b K_n^{-1}=h_b e_b. The third equality also
shows that Lambda has only old poles. Formula (PP31) gives its exact
b-component:

\[
 (\Lambda_{ib})_b
 =X_b\bigl(W_{ib}\operatorname{diag}(X)^{-1}A^{-1}\bigr)_b.
 \tag{PP34}
\]

The actual cycle correction H_ib remains in this formula. If gamma_j(Q)
and mu_j^(ib) are the three-component coefficients on Z_j in
I_old(Q) diag(X)^{-1} and Delta_ib diag(X)^{-1}, respectively, then
(PP31) also yields

\[
 \mu_j^{(ib)} A^{-1}e_b
 =\gamma_j(Q_{ib})A^{-1}e_b-\delta_{ji}(A^{-1})_{bb}.
 \tag{PP35}
\]

This isolates each diagonal b-sector of the target matrix after changing
the output basis by A^{-1}. It does not exclude the indicated scalar
from the spectrum of the actual coefficient map. The uniform unresolved
step is still the nonvanishing of (PP20)/(PP25), with all three sectors
and the old source prefix retained. The nonzero ambient block determinant
(PP29) proves neither that target determinant nor independence of the
equation-(24) source family for every T.

There is a further exact quotient before transport. Put
Z_q=ker(I_old). The prefix map is onto: its F images contain all
P_tab, and E_ta+sum_b P_tab=X_a e_a supplies the polynomial rows. The
cycle prefixes span exactly those three polynomial rows. Since Pi_b
subtracts only cycle rows, it preserves every old-pole prefix coefficient.
It follows that

\[
 \ker\bigl(\operatorname{ResPrefix}_{\rm old}I_{\rm old}|_{D_b}\bigr)
   =\Pi_b Z_q,\qquad
 D_b/(\Pi_bZ_q)\simeq\mathbb R^{9q},\qquad
 \dim\Pi_bZ_q=N_q-12q.
 \tag{PP36}
\]

For the nontrivial inclusion, if R in D_b has polynomial prefix, choose
H in the cycle span with I_old(H)=I_old(R). Then R-H belongs to Z_q
and Pi_b(R-H)=R. Conversely Pi_b applied to a zero-prefix row has
polynomial prefix. Surjectivity follows by applying Pi_b to any old
row with the prescribed old-pole prefix. This proves the dimension
formula using (PP27).

For one b, the seeds in (PP24) form a specified 3q-dimensional
subspace of this 9q-dimensional quotient. The map (PP30) injects
the entire subspace Pi_b Z_q as well. Its transported image may
depend on b. Establishing how these three images and their seed
complements interact with the actual source graph is a precise
remaining route; (PP36) asserts no common invariant subspace.

The relation to the previously proved incoming theorem is exact.
Let Z denote the old/old double-residue block of the physical
polar-corrected incoming columns, already right-transported by
K_n^{-1}, as in (H1)--(H5). In the same residue coordinates, (PP24)
gives

\[
 Z_{t,a,b}=A_t(a,b)\,\Omega_{\rm old}Q_b(R^*_{ib}).
 \tag{PP37}
\]

The added Z_i E_nb and the recovered prefix each have at most one
old pole, even after right multiplication by K_n^{-1}; hence neither
contributes to these old/old double residues. The audited incoming
corollary after (D10) therefore proves joint independence of all 9q
transported seeds modulo E_q for odd q>=5. The even incoming bound
(E17) gives joint rank at least 9q-6 for even q>=6. These incoming
statements require no old-source inverse. Applying the actual prefix
or tail map still uses shorter-source independence, and neither
incoming statement proves nonvanishing of (PP20). For even q the
remaining incoming test itself is the six-column map (E18).
