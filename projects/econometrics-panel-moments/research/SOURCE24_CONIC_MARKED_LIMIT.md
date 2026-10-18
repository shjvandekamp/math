# A marked conic limit for the actual source matrix

This note records the independently audited part of the supplied response
`Geplakte tekst(20261016-124601).txt`, formulas (1)--(34), from the
[source conversation](https://chatgpt.com/c/6ad1e8a7-9ac8-83ed-be7d-3d0e7e81cb59).
It gives a
regular marked limit of the actual double-residue observations, an
invertible residue/normal-jet conversion, and an exact affine recurrence
for actual source words. It does **not** prove nonvanishing of the full
retained-old Schur determinant. These are algebraic arguments, not Lean
certificates or new numerical rank evidence.

Two qualifications are necessary: the companion basis requires
`r + z != 0`, and the displayed positive parameter bounds do not by
themselves exclude every unintended incidence involving the new block.

## Parameters and the incidence open set

Put

\[
G=I+\mathbf1\mathbf1^{\mathsf T},\qquad
w(a)=\left(1,a,\frac{\rho a}{1+za}\right),\qquad
A_a=G\operatorname{diag}w(a),\quad \rho z\ne0.
\]

The actual row forms and kernels are
\(L_{ac}=A_a(c,:)X\) and
\(K_a(c,j)=A_a(c,j)X_j/L_{ac}\).
For the nonvanishing signs below take \(0<z<1/4\) and distinct conic
tail parameters \(1<a_t<2\). Taking \(\rho>0\) also makes the block
times positive. The new earliest block has parameter \(a_\circ=2/z\).

Use the affine chart

\[
X=(1,r,[-3(z+r)+y]/\rho),\qquad \mathcal M=\{y=0\}.
\]

For \(\ell_{ac}=(1+za)L_{ac}\), set
\(\eta_0=2-za\), \(\eta_1=1-2za\),
\(\lambda_a=1-ar\), and
\(\nu_a=1-5za-a(5-za)r\). Then

\[
\ell_{a0}=\eta_0\lambda_a+ay,\qquad
\ell_{a1}=\eta_1\lambda_a+ay,\qquad
\ell_{a2}=\nu_a+2ay.                                      \tag{CM1}
\]

The old within-block \((0,1)\) vertex is
\(P_a=(1,1/a,-3(z+1/a)/\rho)\), and
\(\ell_{\circ0}=(2/z)y\). Thus the new state-0 line contains all
these vertices. At \(P_a\), writing \(x=za\), the other relevant forms
are

\[
\ell_{a2}=-4(1+x),\qquad
\ell_{\circ1}=\frac{3(2-x)}x,\qquad
\ell_{\circ2}=-\frac{3(3x+2)}x.                            \tag{CM2}
\]

They are nonzero for \(0<x<1/2\). The poles on \(\mathcal M\) are
\(r_t=1/a_t\) and
\(s_t=(1-5za_t)/(a_t(5-za_t))\). For distinct tail parameters,

\[
\nu_{a_j}(1/a_i)
=1-5a_j/a_i-za_j(5-a_j/a_i)<0,
\quad
\frac{ds}{da}=-\frac{5-2za+5z^2a^2}{a^2(5-za)^2}<0.         \tag{CM3}
\]

Consequently no old cross-block tail node lies on \(\mathcal M\).

For the **full** marked matrix, additionally restrict to the incidence
open set where every other row form at each marked cross-block node is
nonzero, apart from the intended old-state \(0/1\) collision just
described. Require distinct marked lines and the units of any chosen
projective representative and output-coordinate frame. Generic initial
blocks must satisfy the same conditions. Coordinate units and any
kernel invertibility needed below are separate from the row-form units.

The extra incidence restriction is substantive. The new within-block
\((0,1)\) vertex is \((r,y)=(z/2,0)\). An old state-2 line contains it
exactly when

\[
\nu_a(z/2)=1-\frac{15}{2}za+\frac12(za)^2=0.               \tag{CM4}
\]

The small root \((15-\sqrt{217})/2\) of \(x^2-15x+2\) lies in
\((0,1/2)\), so the positive bounds alone allow this unwanted triple
incidence. Because two of those lines belong to the new block, the
once-per-block rule can still give a finite marked limit there. The
chosen incidence open set excludes it to keep only the stated collisions.

There are also genuine three-block exceptions. On the new state-1 line,
\(y=3z/2-3r\), old state-0 and state-1 lines have respective roots

\[
r=\frac{4+za}{2a(5-za)},\qquad r=\frac1{4b}.
\]

They coincide when \(b=a(5-za)/(2(4+za))\). For example,
\(z=1/18\), \(a=9/5\), and \(b=441/410\) satisfy all the positive
bounds, but new1/old-a0/old-b1 meet at
\((r,y)=(205/882,-361/588)\). After the selected new1/old-a0 pair
residue, the old-b1 denominator remains. Already the completed word in
\(F_{a,\circ,0,1}\) for these three blocks has a nonzero coefficient
of that remaining pole: using the uncleared forms, it is
\(-P_0A_a(0,1)A_\circ(1,1)P_1^2v_{b1}\), where
\(v_{b1}=A_b(1,:)\operatorname{diag}P\).
Its first output is \(-4ar^2/z\ne0\), since \(P_0=1\).
Thus the full marked extension really does need an additional
three-block incidence exclusion.

These are proper algebraic exclusions, not forced extra coincidences.
For each fixed state, the cleared old-line normals are respectively

\[
(2(1+za),a(1+za),\rho a),\quad
(1+za,2a(1+za),\rho a),\quad
(1+za,a(1+za),2\rho a).
\]

Each family has no common projective point: the constant, quadratic,
and then linear coefficients of its evaluation force all three point
coordinates to vanish. This rules out an identically forced incidence
with an independently varying tail block. For two lines from the same
old block, its other vertices are
\((1,-3/a,(1+za)/(\rho a))\) and
\((1,-1/(3a),-(1+za)/(3\rho a))\); direct substitution into the three
new forms gives no further forced incidence in \(0<za<1/2\).
The intended \((0,1)\) collision is therefore compatible with a
nonempty generic incidence open set for any fixed finite tail length.

## Actual words and their marked extension

Write \(p_{tab}=X_aK_t(a,b)\). The actual sources are

\[
E_{ta}=X_ae_a(I-K_t),\qquad
F_{tsab}=p_{tab}e_b\left(I-K_s
 \prod_{j\notin\{t,s\}}^{\nearrow}K_j\right).              \tag{CM5}
\]

The selected-first and increasing-tail order is part of this definition.
At a generic node \(P\) marked by \(L_{uc}=L_{vd}=0\), replace
\(K_u\) by \(e_c^{\mathsf T}A_u(c,:)\operatorname{diag}P\), replace
\(K_v\) analogously, and evaluate every other kernel at \(P\).
Denote these factors by \(\widetilde K_j\). With
\(E_{bb}=e_b^{\mathsf T}e_b\), the normalized raw double coefficient is

\[
\mathscr D_PF_{tsab}=-P_ae_a\widetilde K_tE_{bb}
 \widetilde K_s\prod_{j\notin\{t,s\}}^{\nearrow}\widetilde K_j.
                                                               \tag{CM6}
\]

The actual head has only one block pole, hence its cross-block double
coefficient is zero. The same applies to \(E_{ta}\). Every completed
word uses each block exactly once. Taking the selected old-state
residue therefore replaces its whole kernel; no denominator from
another row of that same kernel remains.

At \(a_\circ=2/z\), the two new0/old0 and new0/old1 marks coalesce at
\(P_a\), but CM6 has a finite limit for each mark. CM2--CM3 and the
incidence guards make all remaining factors regular. All other marked
entries are regular by the same guards. Thus the raw actual-source
double-residue matrix has a rational marked limit without any separate
regularity assumption on a Schur complement, quotient frame, or inverse
old pivot matrix. A nonsingular marked limit would imply rational
nonidentity of the corresponding actual determinant; nonsingularity is
not established here.

## The exact residue/normal-jet observation change

For an actual source row \(R\), put \(f=\ell_{\circ0}R\). Locally at
\(r_t=1/a,y=0\), its singular part has the form

\[
f=\frac{U_0(r,y)}{\ell_{a0}}+
   \frac{U_1(r,y)}{\ell_{a1}}+\text{regular},                \tag{CM7}
\]

with regular numerators. The once-per-block property excludes a product
\(\ell_{a0}^{-1}\ell_{a1}^{-1}\). Set \(d_i=U_i(r_t,0)\);
these are the marked double coefficients for the **cleared** forms.
Since the two pole curves are \(r_i(y)=r_t+y/\eta_i\), the observations
\(J_0=\operatorname{Res}_{r=r_t}f(r,0)\) and
\(J_1=[(r-r_t)^{-2}]\partial_yf(r,0)\) satisfy

\[
\binom{J_0}{J_1}=
\begin{pmatrix}
-1/(a\eta_0)&-1/(a\eta_1)\\
-1/(a\eta_0^2)&-1/(a\eta_1^2)
\end{pmatrix}\binom{d_0}{d_1},\qquad
\det=\frac{1+za}{a^2\eta_0^2\eta_1^2}\ne0.                \tag{CM8}
\]

Numerator derivatives contribute only simple poles. Terms regular in
the new kernel, including the actual head, also contribute no highest
normal-pole coefficient. In two fixed independent zero-sum output
coordinates, the four-row determinant factor is

\[
\frac{(1+za)^2}{a^4(2-za)^4(1-2za)^4}.                    \tag{CM9}
\]

For all colliding pairs, multiply CM9 over tail blocks, using consistent
row order. This exact factor uses the same cleared-line normalization
and fixed output coordinates on both sides. Explicitly, the coefficients
for cleared and uncleared forms obey
\(d^{\ell}=(1+za_u)(1+za_v)d^L\); moving pair bases contribute their
own nonzero coordinate determinants.
Those factors must be included when comparing a differently normalized
matrix. The result is an invertible observation change, not a rank
claim about the full matrix.

## Companion transfer with the actual affine head

On \(\mathcal M\), put \(q=-3(z+r)\),
\(d=(1,-1,0)\), and \(n=(3z,3r,q)\). The rows \((d,n)\) form a
basis of the zero-sum plane **if and only if \(r+z\ne0\)**: their first
two-coordinate determinant is \(3(r+z)\). At \(r=-z\),
\(n=3zd\). This corrects the supplied response's assertion that
\(z\ne0\) alone suffices. At each marked \(r=1/a\), the needed unit is
\((1+za)/a>0\).

Define

\[
g_a=-\frac{\eta_0\eta_1\lambda_a}{a(1+za)},\quad
\kappa_a=\frac{4a^2rq(1+za)^2}
 {\eta_0\eta_1\lambda_a^2\nu_a},\quad
\vartheta_a=2\left(\frac{1+za}{\eta_0\lambda_a}
 +\frac{ar(1+za)}{\eta_1\lambda_a}+\frac{aq}{\nu_a}\right)-1.
\]

On the inverse-kernel domain, \(nK_a^{-1}=g_ad\), so
\(dK_a=g_a^{-1}n\). The resulting rational kernel action is

\[
\mathsf M_a=
\begin{pmatrix}0&g_a^{-1}\\-g_a\kappa_a&\vartheta_a\end{pmatrix},
\qquad \det\mathsf M_a=\kappa_a=\det K_a.                  \tag{CM10}
\]

The inverse identity requires kernel invertibility where first used;
CM10 is then a rational identity wherever its displayed coordinates
and row-form denominators are defined.
Writing a general row as \(\sigma e_2+x_1d+x_2n\), its actual transfer is

\[
(\sigma,x)\longmapsto(\sigma,\sigma h_a+x\mathsf M_a),\quad
h_a=\left(
\frac{r(1+za)(1-za)}{(z+r)\nu_a},
\frac{(1+za)(1+ar)}{3(z+r)\nu_a}\right).                  \tag{CM11}
\]

This affine head is regular at \(r=1/a\). State coordinates are
\(\epsilon_0=(r/(z+r),1/[3(z+r)])\),
\(\epsilon_1=(-z/(z+r),1/[3(z+r)])\), and \(\epsilon_2=(0,0)\).
For an ordered word \(W=(w_1,\ldots,w_k)\), set

\[
\mathsf M_W=\mathsf M_{w_1}\cdots\mathsf M_{w_k},\qquad
h_W=\sum_i h_{w_i}\mathsf M_{w_{i+1}}\cdots\mathsf M_{w_k}.
\]

The exact coordinates of the actual sources are

\[
E_{ta}\leftrightarrow X_a(\epsilon_a-h_t-\epsilon_a\mathsf M_t),
\quad
F_{tsab}\leftrightarrow p_{tab}
 (\epsilon_b-h_{W_{ts}}-\epsilon_b\mathsf M_{W_{ts}}),        \tag{CM12}
\]

where \(W_{ts}\) has precisely the order in CM5. Generic initial blocks
use their actual affine maps in the same basis; they need not have the
companion form CM10.

## Ordered pole factors and the surviving insertion error

The entries of \(\mathsf M_{a_t}\) have at most simple poles at
\(r_t=1/a_t\). Their residue \(\mathsf R_t\) satisfies

\[
\det\mathsf R_t=
\frac{3(1+za_t)^2}{a_t^2(2-za_t)(1-2za_t)}>0.              \tag{CM13}
\]

If a word contains \(t\) once and all other factors are regular there,
take the residue at its actual position in the ordered product. Then

\[
\det\operatorname{Res}_{r=r_t}\mathsf M_W
=\det\mathsf R_t\prod_{j\in W,\ j\ne t}\det\mathsf M_j(r_t),
\]
\[
\det\mathsf M_{a_j}(r_t)=
-\frac{12a_j^2(1+za_t)(1+za_j)^2}
 {(2-za_j)(1-2za_j)(a_t-a_j)^2\nu_{a_j}(1/a_t)}>0.          \tag{CM14}
\]

Any initial-block factors require their actual determinants to be
nonzero at the node. Taking determinants removes the product order
only after the correctly ordered residue has been obtained.

The earliest-block insertion error remains. At an old cross-block node
\(L_{ta}=L_{sb}=0\), let
\(v_{ta}=A_t(a,:)\operatorname{diag}P\), define \(v_{sb}\) similarly,
and put \(\sigma=P_aA_t(a,b)P_b\),
\(\sigma'=P_bA_s(b,a)P_a\). If \(R\) is the increasing old product
excluding \(t,s\), the two retained insertion-error coefficients are

\[
\sigma v_{sb}(I-K_\circ)R,\qquad
\sigma'v_{ta}(I-K_\circ)R.                                \tag{CM15}
\]

For \(s_i=w_{\circ i}P_i\) and \(S=\sum_i s_i\),

\[
\det\bigl((I-K_\circ)|_{\mathbf1^\perp}\bigr)
=\frac{S(S^2+\sum_i s_i^2)}{\prod_iL_{\circ i}},\qquad
\det\bigl(((I-K_\circ)R)|_{\mathbf1^\perp}\bigr)
=\frac{S(S^2+\sum_i s_i^2)}{\prod_iL_{\circ i}}
 \prod_{\ell\notin\{t,s\}}\det K_\ell(P).                 \tag{CM16}
\]

Over the reals, the quadratic factor is positive at a nonzero point
when the new times are nonzero. Require separately \(S\ne0\), all
new row-form units, the other kernel determinants, and the scalar and
input-frame units in CM15. Under those generic conditions the two-column
old-pair insertion-error block is nonsingular, including on the marked
conic specialization. It cannot be dropped. Over a different field,
the quadratic factor in CM16 is an explicit additional unit condition.

At the other conic limit \(a_\circ\to0\), assuming \(P_0\ne0\),
\(K_\circ\to\mathbf1e_0\). Hence a zero-sum row satisfies
\(v(I-K_\circ)\to v\), and CM15 tends to the negative of the old
source's own-head pair coefficient. That retained pair contribution
cancels rather than preserving the old pivot. The actual regularization
terms remain necessary.

The unresolved step is the coupling of regularized retained columns to
the old cross-block double-residue rows. The marked extension, CM9, and
the nonzero local transport factors CM13--CM14 do not determine that
coupling and do not prove the full Schur determinant nonzero.
