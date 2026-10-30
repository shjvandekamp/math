# First and second normal restrictions of the actual source quotient

**Status: paper algebra checked locally, with independently reconstructed
and reviewed exact finite bases. Not Lean formalized.**
The [Pro14 investigation](https://chatgpt.com/c/6ad148ae-dbfc-83eb-b3b5-04e62b68b9fc)
supplied the induction and four finite bases. The argument below keeps
their role explicit. The independent reconstruction is in
[`source24_normal_restrictions.py`](../exploration/source24_normal_restrictions.py)
and [`source24-normal-restrictions-results.json`](../exploration/source24-normal-restrictions-results.json).
These restriction results do not prove that the actual source subspace
spans the full scalar ambient.

Use the actual subspace N from the
[binary quotient reduction](SOURCE24_BINARY_QUOTIENT.md): it contains
all same-shared-index differences over the first slot, the long-empty
rows, and the selected divergent-state-zero rows. Adding those differences
shows that every \(F_{t,s,a,0}\), with \(s\ne t\), belongs to N.
All spans below use constant real coefficients with respect to the effect
variables. Coefficients may depend on the fixed model parameters.

## Actual rows and their normal coefficients

Normalize the first column of G to one, and put
\(A_t=G\operatorname{diag}(1,u_t,v_t)\), with positive times. Set

\[
 \rho=G_{02}/G_{01},\quad \sigma=G_{12}/G_{11},\quad
 \tau=G_{22}/G_{21},\quad z_t=v_t/u_t,\quad
 r_t(x)=x+\rho z_t.
 \tag{NR1}
\]

Assume the ratios are nonzero, \(\sigma\ne\tau\), and all poles
listed below are distinct. These are generic conditions. Work in the
chart \(X=(X_0,x,1)\), and write
\(h(R)=R_2/X_2\). When h is divisible by \(X_0^j\), define
\(J_jh=(h/X_0^j)|_{X_0=0}\). This is a normal coefficient on that
subspace, not a definition of division for arbitrary h.

On the axis the binary probability of outcome two evolves by
\(p\mapsto a_t+d_tp\), where

\[
 a_t=\frac{\sigma z_t}{x+\sigma z_t},\qquad
 d_t=\frac{x(\tau-\sigma)z_t}
            {(x+\sigma z_t)(x+\tau z_t)},\qquad
 c_t=\frac{\rho z_t}{x+\rho z_t}.
 \tag{NR2}
\]

Let \(Y_t\) start with \(c_t\), then apply all other old blocks in
increasing order. Let \(Y_s^{\widehat t}\) start with \(c_s\),
then apply all blocks except t and s in increasing order. Define

\[
 H_{ts}=\frac{Y_s^{\widehat t}}{r_t},\qquad
 Z_{ts}=\frac{r_t H_{ts}}{x+\tau z_t},\qquad s\ne t.
 \tag{NR3}
\]

Let \(r(t)=\min(\{1,\ldots,m\}\setminus\{t\})\). Define
\(\delta_{ts}\) as the difference of the binary intercepts of the
move-s-first and move-r(t)-first words omitting t. Each such binary
word starts from probability zero and uses the affine maps in (NR2).
In particular \(\delta_{t,r(t)}=0\).

Directly from the actual three-state source formulas,

\[
 \begin{split}
 J_2h(F_{t,s,0,0})&=-H_{ts}/(u_tG_{01}),\\
 J_1h(F^{\rm empty}_{t,0})&=-Y_t,\\
 J_1h(F_{t,s,2,0})&=-Z_{ts}/(u_tG_{21}),\\
 J_1h\!\left(\sum_b(F_{t,s,0,b}-F_{t,r(t),0,b})\right)
   &=-\delta_{ts}.
 \end{split} \tag{NR4}
\]

Here \(F^{\rm empty}_{t,0}=X_0e_0(I-P_t)\), with P_t the actual
move-t-first full word. The first family vanishes to order at least
two in \(X_0\); the other three families vanish to order at least
one. For the last identity, the two binary products have the same
determinant. Their difference therefore has identical outcome-two
entries in both initial binary rows. The initial row supplied by block t
sums to one on the axis, leaving precisely the intercept difference.
Thus (NR4) uses available rows of N and preserves their prescribed order.

Put

\[
 E_m=\prod_{t=1}^m(x+\rho z_t)(x+\sigma z_t)(x+\tau z_t),
 \qquad
 E_m^{\rm bin}=\prod_{t=1}^m(x+\sigma z_t)(x+\tau z_t).
 \tag{NR5}
\]

The two scalar target spaces are
\(\mathcal U_1=\{p/E_m:\deg p\le3m-1\}\), of dimension 3m,
and \(\mathcal U_2=\{p/E_m:\deg p\le3m-2\}\), of dimension
\(3m-1\).

## Augmented induction for the second-normal family

Let \(\pi_t=1/r_t\), and define

\[
 \mathcal V_m=
 \{(H,\pi):H\in\mathcal U_2,
       \ \pi\in\operatorname{span}(\pi_1,\ldots,\pi_m),
       \ H(0)=\pi(0)\}.
 \tag{NR6}
\]

It has dimension \(4m-2\), and every \((H_{ts},\pi_t)\) lies in it.
Appending the largest block n sends the old augmented pair to

\[
 (H,\pi)\longmapsto(d_nH+a_n\pi,\pi).
 \tag{NR7}
\]

This map is injective. Its image is exactly the common kernel of four
linear functionals on \(\mathcal V_n\). Write
\(\xi_n=-\rho z_n\), and use coefficients of the expansion at infinity:

\[
 \begin{split}
 P(H,\pi)&=\operatorname{Res}_{x=\xi_n}\pi,\\
 Q(H,\pi)&=\operatorname{Res}_{x=\xi_n}H,\\
 I(H,\pi)&=[x^{-2}]H-\sigma z_n[x^{-1}]\pi,\\
 J(H,\pi)&=\tau z_n\{H'(0)-\pi'(0)\}+\pi(0).
 \end{split} \tag{NR8}
\]

Necessity follows by substituting (NR7). Conversely, P removes the new
pole of pi and Q the new rho pole of H. The putative inverse
\(H_{\rm old}=(H-a_n\pi)/d_n\) has no new binary poles. The equality
\(H(0)=\pi(0)\) removes the apparent pole at zero; I makes its decay
at infinity at least quadratic; J gives \(H_{\rm old}(0)=\pi(0)\).
It therefore belongs to the old augmented space. This proves the kernel
description without assuming a dimension count supplies an inverse.

For \(n\ge6\), take the four new columns
\((H_{1n},\pi_1),(H_{2n},\pi_2),(H_{n1},\pi_n),(H_{n2},\pi_n)\).
Let \(k=n-1\). Their test matrix is

\[
 \begin{pmatrix}
 0&0&1&1\\
 b_1&b_2&q_1&q_2\\
 i&i&i&i\\
 j_1&j_2&j_n&j_n
 \end{pmatrix},\qquad
 \begin{split}
 i&=\sigma(z_k-z_n),\\
 j_t&=(z_k-z_n)/(\rho z_tz_k),\\
 b_t&=\rho z_n\prod_{j<n,\,j\ne t}d_j(\xi_n)/r_t(\xi_n),\\
 q_t&=Y_t^{(n-1)}(\xi_n).
 \end{split} \tag{NR9}
\]

Its determinant is exactly \(i(q_2-q_1)(j_2-j_1)\). Moreover

\[
 q_2-q_1=
 \left[\prod_{j=3}^{n-1}d_j\right]
       (a_1+d_1c_2-a_2-d_2c_1)\big|_{x=\xi_n}.
 \tag{NR10}
\]

The last parenthesized factor has leading term
\(\sigma(z_1-z_2)/x\) at infinity,
so it is not identically zero. Varying the new positive \(z_n\)
avoids its finitely many roots and the excluded poles, as well as
\(z_n=z_k\). Thus the four new columns generically span the quotient.
The exact augmented base at m equal to five proves by induction that
the actual augmented columns span \(\mathcal V_m\) for every
\(m\ge5\). Projection onto H is onto \(\mathcal U_2\): a pi with
any prescribed value at zero can be chosen. With the separate m equal
to four H base, (NR4) therefore supplies all of \(\mathcal U_2\)
as second-normal coefficients for every \(m\ge4\).

## Deletion differences and the first-normal family

For \(m\ge5\), the binary deletion differences span

\[
 \mathcal D_m=
 \{p/E_m^{\rm bin}:\deg p\le2m-1,\ p(0)=0\},
 \qquad \dim\mathcal D_m=2m-1.
 \tag{NR11}
\]

To prove the induction, divide by \(\Delta_m=\prod_t d_t\).
The resulting Laurent space has exponents \(1-m,\ldots,m-1\).
An old deletion difference acquires a final factor d_n on append,
so its normalized Laurent function is unchanged. Only the two outer
coefficients are missing. Use \(\delta_{1n}\) and
\(\delta_{n-1,n}\). Put \(k(t)=\max(\{1,\ldots,n-1\}\setminus\{t\})\).
Up to fixed nonzero factors common to the two columns, their coefficients
at exponents \(1-n,n-1\) are

\[
 \left(\frac{z_{k(t)}-z_n}{z_nz_{k(t)}},\ z_{k(t)}-z_n\right).
 \tag{NR12}
\]

For completeness, before division by \(\Delta_n\) the corresponding
coefficients at zero and infinity are
\((z_{k(t)}-z_n)/(\tau z_nz_{k(t)})\) times x, and
\(\sigma(z_{k(t)}-z_n)/x\). These follow by comparing
\(a_{\rm old}+d_{\rm old}a_n\) with
\(a_n+d_na_{\rm old}\). The two values of \(k(t)\) are
\(n-1,n-2\); hence the determinant in (NR12) is nonzero for distinct
generic times. The exact m equal to five base starts this induction.

The function \(Y_t\) has only one rho pole, at \(\xi_t=-\rho z_t\),
with nonzero residue
\(\beta_t=\rho z_t\prod_{j\ne t}d_j(\xi_t)\), and \(Y_t(0)=1\).
Consequently \(\mathcal D_m+\operatorname{span}(Y_t)_t\) has
dimension \(3m-1\) and is exactly the kernel, inside \(\mathcal U_1\), of

\[
 \ell(f)=f(0)-\sum_t
      \frac{\operatorname{Res}_{x=\xi_t}f}{\beta_t}.
 \tag{NR13}
\]

The functional is nonzero, for example on a binary-pole function with
nonzero value at zero. A single \(Z_{ts}\) supplies its missing direction:

\[
 Z_{ts}(0)=\frac1{\tau z_t},\qquad
 \frac{\operatorname{Res}_{\xi_s}Z_{ts}}{\beta_s}
       =\frac1{(\xi_s+\tau z_t)d_t(\xi_s)},\qquad
 \ell(Z_{ts})=-\frac{\sigma(\xi_s+\tau z_t)}
                   {\tau(\tau-\sigma)z_t\xi_s}\ne0.
 \tag{NR14}
\]

Equations (NR4), (NR11)--(NR14) prove first-normal surjectivity onto
\(\mathcal U_1\) for \(m\ge5\). The separate m equal to four
first-normal base gives the same conclusion there.

## Exact finite bases and common-parameter scope

All four bases use \(\rho,\sigma,\tau=(1,2,3)\),
\(z=(1,5,7,11,13)\), truncated at m equal to four when appropriate,
and arithmetic modulo 1009. They are compatible with the positive
invertible common matrix
\(G=\begin{pmatrix}1&1&1\\1&3&6\\1&5&15\end{pmatrix}\),
whose determinant is 8. Ordered pairs below use indices starting at one.

| Base | Rows and columns | Nonzero determinant modulo 1009 |
|---|---|---:|
| H, m=4 | evaluations 1 through 11; first 11 lexicographic ordered pairs | 290 |
| Augmented H, m=5 | five pi-coefficient rows, then H evaluations 1 through 13; first 18 lexicographic ordered pairs | 487 |
| Deletion differences, m=5 | evaluations 1 through 9; pairs 13,14,15,23,24,25,32,34,45 | 730 |
| First normal, m=4 | evaluations 1 through 12; Y1,Y2,Y3,Y4,delta13,delta14,delta23,delta24,delta32,delta34,Z12,Z13 | 379 |

All evaluation denominators are nonzero at these fixtures. The indicated
evaluations determine the claimed scalar spaces: in the augmented case,
the five pi coefficients and the equality at zero leave thirteen H
coefficients to determine. A nonzero good-reduction minor proves the
corresponding rational determinant is nonzero in characteristic zero.
These remain external exact base certificates relative to the paper
induction and have not been formalized in Lean. The local script also
checks (NR4) against the original three-state products through order two
in the normal variable.
The run completed in 0.164 seconds using 16,007,168 bytes maximum RSS,
without a cutoff. It checked 1,325 actual-source Taylor coefficients,
alongside the separate binary-row and omitted-word controls.

Each induction produces a nonzero rational minor in the same irreducible
common-G, independent-time parameter family. A fixed positive G witness
already proves nonvanishing in that family. For any fixed m the required
nonzero minors and geometry conditions can therefore be intersected;
they are not being combined from unrelated parameter families. Passing
to a scalar-covariate realization, if required, uses the previously
established common-G substitution bridge, not an additional claim here.

## Consequence for the normalized degree-zero scalar quotient

Let \(D=\prod_{t,a}L_{ta}\). The scalar ambient used in this section is

\[
 \mathcal S=\{p/D:\deg p=3m,\ p\text{ vanishes at the same-block
 pair points, the matching points, and }e_2\}.
 \tag{NR15}
\]

It consists of homogeneous degree-zero functions. It is different from
the degree-one scalar space used in H6 of the induction note. Let
\(\mathcal N=h(N)\subset\mathcal S\), and let \(\mathcal E\) be
the scalar cross-block double-residue map. Its kernel is the span of
the following 3m independent functions:

\[
 f_{ta}=\frac{X_a}{L_{ta}}-
                   \frac{\mathbf1_{a=2}}{A_t(2,2)}.
 \tag{NR16}
\]

Indeed, removing all pair poles leaves a homogeneous linear residue on
each old line; the matching zero forces it to be a multiple of \(X_a\).
Subtracting those single-line fractions leaves a constant, fixed by
the value at \(e_2\). Distinct line poles prove independence.

Define T by the ordinary axis restriction and m matching values

\[
 T(h)=\left(h|_{X_0=0},(\gamma_t(h))_t\right),\qquad
 \gamma_t(h)=
 \left.\frac{(L_{t0}h)|_{L_{t0}=0}}{X_0}
                  \right|_{Q_{t0}},\quad
 Q_{t0}=(0,-\rho z_t,1).
 \tag{NR17}
\]

The quotient in the matching value is taken before evaluation. On
\(\ker\mathcal E\), T is an isomorphism onto a 3m-dimensional target.
The a=0 functions in (NR16) have zero axis restriction and matching
values equal to the standard basis. The a=1,2 functions have zero
matching values and supply the 2m distinct axis poles. Their axis
functions are bounded at infinity and vanish at x equal to zero; these
properties specify a 2m-dimensional space. In particular
\(\mathcal E\) is injective on \(\ker T\).

For any selected normal lift \(h=X_0g\), there is the exact relation

\[
 \gamma_t(h)=u_tG_{01}
          \operatorname{Res}_{x=-\rho z_t}J_1h.
 \tag{NR18}
\]

There is no derivative correction: cancel \(X_0\) first, remove the
old-line pole, and then restrict to its matching point.

First-normal surjectivity allows 2m independent lifts whose first
coefficients lie in the no-rho-pole subspace
\(\{p/E_m^{\rm bin}:\deg p\le2m-1\}\). They lie in
\(\mathcal N\cap\ker T\) by (NR18). Second-normal surjectivity
supplies another \(3m-1\) lifts divisible by \(X_0^2\), also in
that kernel, with independent second coefficients. Their first
coefficients are zero, so the two collections are independent. Thus

\[
 \dim(\mathcal N\cap\ker T)\ge5m-1.
 \tag{NR19}
\]

The separately audited surjectivity \(T(\mathcal N)\) onto the full
3m-dimensional target is proved in
[SOURCE24_AXIS_SPANNING.md, AS9--AS13](SOURCE24_AXIS_SPANNING.md).
Intersecting its generic open conditions with those above gives

\[
 \dim\mathcal N\ge8m-1,\qquad
 \dim\{w\in\mathbb K^{9\binom m2}:
       w^T\mathcal E(\mathcal N\cap\ker T)=0\}
       \le9\binom m2-(5m-1),\qquad m\ge4.
 \tag{NR20}
\]

The kernel and dimension consequences were independently audited.
They give explicit progress inside the actual scalar image of N;
they do not prove that N, its scalar image, or the remaining source
family spans its full target. Nor do first and second normal
surjectivity alone assert any higher-normal induction.

## Why the normal restrictions do not yet iterate

Appending a new kernel K to an actual source row R with its prefix I
obeys the exact identities

\[
 R^+=RK+I(I_{3\times3}-K),\qquad I^+=I.
 \tag{NR21}
\]

With \(R_0=-R_1-R_2\), \(h=R_2/X_2\), and the new matrix A and
line denominators \(L_d\), the scalar output is

\[
 \begin{split}
 h^+={}&\left(\frac{A_{12}}{L_1}-\frac{A_{02}}{L_0}\right)R_1
 +X_2\left(\frac{A_{22}}{L_2}-\frac{A_{02}}{L_0}\right)h\\
 &+\frac{I_2}{X_2}-\sum_{d=0}^2\frac{A_{d2}I_d}{L_d}.
 \end{split} \tag{NR22}
\]

The coefficient of \(R_1\) is generically nonzero. Thus scalar h does
not form a closed append state. Retaining
\((R_1,R_2,I_0,I_1,I_2)\) supplies a closed vector state; even a
formal relation with R equal to zero can have nonzero prefix I.

At \(X_2=1\), use Taylor coefficients in \(X_0\), not derivatives.
The precise coefficient transport is

\[
 (R^+)^{[\ell]}=I^{[\ell]}+
    \sum_{j=0}^{\ell}(R^{[j]}-I^{[j]})K^{[\ell-j]}.
 \tag{NR23}
\]

A source relation must use the same constant coefficient vector at
every order. The missing next step is a lifting or syzygy theorem:
combinations whose earlier normal coefficients vanish must supply
enough independent coefficients at the next order under (NR23).
The first- and second-normal results do not imply this, and they do
not assert closure of N under multiplication by \(X_0\). This append
obstruction and the retained-state formula were independently checked.

## The precise ambient filtration and the remaining third-order kernel

There is a useful geometric description of the target for higher normal
coefficients. Work with the cleared polynomial space S_m of degree 3m
and put

\[
 F^k S_m=S_m\cap X_0^k\mathbb K[X_0,X_1,X_2]_{3m-k}.
 \tag{NR24}
\]

The block points on X0=0 are exactly the m matching points Q_t0;
the additional point e2 is on that line as well. For k at least one,
their vanishing is automatic. The five remaining points of block t are

\[
 Z'_t=\{P_{t01},P_{t02},P_{t12},Q_{t1},Q_{t2}\},\qquad
 F^k S_m=X_0^k I\!\left(\bigcup_tZ'_t\right)_{3m-k}.
 \tag{NR25}
\]

Here P_tab is the intersection of the two indicated lines in block t.
All five points are off X0=0 under the generic geometry hypotheses.

The conic C_t=L_t1 L_t2 vanishes at all five points. It is their only
vanishing quadratic up to a scalar: three distinct points lie on L_t1
and three on L_t2, so a quadratic vanishing there must contain both
lines. Evaluation of the six-dimensional quadratic space at these five
points therefore has rank five. Choose a quadratic separator for a
point in Z'_t and multiply it by the C_s for all s other than t.
Cross-block nonincidence makes its value at the target nonzero.
These separators interpolate all 5m points in degree 2m.

One degree can be saved generically for m at least two. It suffices
that each pair of blocks admits cubic interpolation at its ten points:
multiply a cubic separator for that pair by the C_s from the other
m−2 blocks, obtaining degree 2m−1. Here is a direct common-G witness
for the two-block interpolation claim:

\[
 G=\begin{pmatrix}1&0&0\\1&1&1\\1&2&3\end{pmatrix},\qquad
 (u_1,v_1)=(1,1),\quad(u_2,v_2)=(2,4).
\]

At this boundary specialization, four of the ten points lie on X0=0,
with distinct ratios X2/X1 equal to −1, −2/3, −1/2, −1/3. A cubic
vanishing at all ten points must therefore be X0 times a quadratic.
In the chart X0=1, the other six points are
(0,−1), (−1/2,0), (−2,1), (0,−1/4), (−1/4,0), (−1,1/4).
A quadratic vanishing at the four points on the two coordinate axes
has the form

\[
 A(8x^2+4y^2+6x+5y+1)+Bxy.
\]

The other two values give 30A−2B=0 and (9/2)A−B/4=0, so A=B=0.
Thus the ten-point cubic evaluation matrix is invertible. This boundary
witness certifies a nonzero polynomial minor; its invertibility persists
at positive nearby parameters. The separate nonincidence conditions
can also be imposed generically. For any fixed m, the finitely many
required pair minors belong to the same common-G parameter ring;
their product with those geometric factors is nonzero.

It follows that all 5m off-axis points admit interpolation in degree
2m−1. Multiplication by powers of X0 extends it to every higher degree.
Consequently, generically for m at least two,

\[
 \dim F^kS_m=\binom{3m-k+2}{2}-5m\quad(1\le k\le m+1),
 \qquad
 \dim(F^kS_m/F^{k+1}S_m)=3m-k+1
                 \quad(1\le k\le m).
 \tag{NR26}
\]

The zeroth layer has dimension 2m. The ambient kth normal target in
the range of (NR26), after division by D and in the chart X2=1, is
exactly

\[
 \left\{\frac{p(x)}{E_m(x)}:\deg p\le3m-k\right\}.
 \tag{NR27}
\]

This is constructive: extend the prescribed binary form to q0 of degree
d=3m-k, interpolate q0(P)/X0(P) on the 5m points by a form g of
degree d−1, and set q=q0−X0g. The inequality d−1 at least 2m−1
ensures the required interpolation. Then q vanishes at all off-axis
points while keeping its prescribed restriction on X0=0.

In particular, the audited ordinary-axis, first-normal, and second-normal
source results supply all of the first three ambient layers. They give
the exact quotient statement, for every fixed m at least four generically,

\[
 S_m=p_2(N)+F^3S_m,
 \qquad \dim(S_m/F^3S_m)=8m-1,
 \qquad \dim F^3S_m=\frac{9m^2-19m+2}{2}.
 \tag{NR28}
\]

Thus the remaining full-spanning question is precisely
p2(N) intersect F^3 S_m equals F^3 S_m. Its next layer is J3 on
actual combinations whose first three coefficients all vanish.
Independent coefficient choices at successive orders would not prove
this assertion. The geometric interpolation argument and (NR28) were
independently checked locally; they supply no new higher-normal
surjectivity theorem for the actual sources.

## Finite coupled higher-normal profiles

[`source24_normal_filtration.py`](../exploration/source24_normal_filtration.py)
computes the actual cleared N polynomial matrix and the normalized
pure-path matrix at the previously recorded economic fixtures. It orders
monomials by increasing X0 exponent. At each layer k it applies that
layer's coefficient matrix to the kernel of every earlier layer, retaining
the same original source coefficients. The resulting gains are therefore
compatible successive ranks. They do not add independently ranked layers.

| m | Successive gains, before trailing zeros | Remaining polynomial dimension after layers 0,1,2 |
| --- | --- | ---: |
| 4 | 8, 12, 11, 10, 9, 8, 7, 1 | 35 |
| 5 | 10, 15, 14, 13, 12, 11, 10, 9, 8, 3 | 66 |

The actual N and normalized-path profiles agree at every layer of these
two fixtures. The [saved exact output](../exploration/source24-normal-filtration-results.json)
includes the full matrices, original generator labels, successive kernel
certificates, and explicit actual-source coefficient vectors for the
X0-cubed-divisible polynomial images. Their coefficient-kernel dimensions
are 65 and 126, including respectively 30 and 60 relations giving the
zero polynomial; the genuine polynomial dimensions are 35 and 66.
These different dimensions must not be conflated.

The same script independently corroborates the two-block interpolation
lemma at a positive common-G economic fixture. With each of its ten
points normalized to X0=1, the cubic evaluation determinant is 944753
modulo 1000003. Its point normalizations and cross-block conic-separator
values are all nonzero where required. This certificate is additional
evidence; the hand proof above already supplies the characteristic-zero
interpolation witness.

The revised run completed in 2.890 seconds using 34,258,944 bytes
maximum RSS, with no cutoff. Independent ordinary-word and clearing
checks passed, and the coupled elimination and finite output passed a
separate local audit. The higher-layer profiles concern only the two
displayed lengths. The next uniform task remains actual-source lifting
inside F^3 S_m and subsequent filtration kernels.
