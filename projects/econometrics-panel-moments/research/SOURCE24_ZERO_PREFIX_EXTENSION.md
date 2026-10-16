# A quadratic lower bound from zero-prefix source rows

**Status: independently checked paper algebra; not Lean formalized.**
The [Pro19 investigation](https://chatgpt.com/c/6ad1572b-b950-83ed-92cb-6eaa72dc3df9)
proposed the recursive family below. Local independent review checked
the actual source words, both axis restrictions, the Laurent endpoint
argument, the three-column base, and the parameter perturbation.
The result is a lower bound on the actual scalar image of N, not a
proof that this image fills its ambient space.
The [Pro21 continuation](https://chatgpt.com/c/6ad15e36-dd64-83ed-9505-b8f7d094c30f)
and two independent local audits strengthen the increment to 6q+3
in (ZP41)--(ZP50). With the exact length-six splitting base, the
strongest resulting bound is 3m²+45 for m>=6. The earlier 4q proof
is retained as the axis subargument used in that extension.

Use the actual source subspace N from
[SOURCE24_BINARY_QUOTIENT.md](SOURCE24_BINARY_QUOTIENT.md), and the
scalar map \(h(R)=R_2/X_2\) from
[SOURCE24_NORMAL_RESTRICTIONS.md](SOURCE24_NORMAL_RESTRICTIONS.md).
All linear independence statements use constant real coefficients with
respect to X. Model parameters may enter those coefficients.

## The theorem and actual recursive family

For every \(m\ge2\), the actual scalar image of N has generic dimension
at least

\[
 \dim h(N)\ \ge\ 2m(m-1)-1.
 \tag{ZP1}
\]

Here genericity is in the common-G family

\[
 A_t=G\operatorname{diag}(1,u_t,v_t),\qquad
 K_t=\operatorname{diag}(L_t)^{-1}A_t\operatorname{diag}(X),
 \qquad L_{ta}=\sum_b A_t(a,b)X_b.
 \tag{ZP2}
\]

There are positive witnesses. The construction first keeps

\[
 G_*=\begin{pmatrix}1&1&1\\1&2&1\\1&3&2\end{pmatrix},
 \qquad \det G_*=1,
 \tag{ZP3}
\]

fixed and then perturbs G when generic line geometry is required.

At a given length, let \(P_t\) be the full word with t first and the
other blocks increasing, and let \(P_s^{\widehat t}\) have s first
and then the other blocks except t increasing. Write

\[
 \begin{split}
 F_{t,s}^{ab}&=X_aK_t(a,b)e_b(I-P_s^{\widehat t}),\\
 F_{t,a}^{\rm empty}&=X_ae_a(I-P_t),\\
 r(t)&=\min\{j:j\ne t\},\\
 C_{t,s}^{ab}&=F_{t,s}^{ab}-F_{t,r(t)}^{ab}.
 \end{split}
 \tag{ZP4}
\]

Every C lies in N. The difference has zero prefix: its two source rows
have the same \(X_aK_t(a,b)e_b\). The rows

\[
 H_a=F_{1,a}^{\rm empty}-F_{2,a}^{\rm empty},
 \qquad a=0,1,2,
 \tag{ZP5}
\]

also lie in N and have zero prefix. Appending a largest block n to any
such fixed formal combination gives exactly

\[
 R^+=RK_n.
 \tag{ZP6}
\]

This uses the actual order: every old word gains n at its end, and the
reference \(r(t)\) for an old shared block does not change. No new
effect-dependent combination of source columns is introduced.

Start at \(m=2\) with the three rows (ZP5). Given the previously
constructed family at length q, append it using the same formal source
coefficients and add the following rows at \(n=q+1\):

\[
 \begin{array}{ll}
 \mathcal A_{ta}=C_{t,n}^{a0},
       &1\le t\le q,\ a=0,1,\\
 \mathcal A_{*a}=\displaystyle\sum_{b=0}^2 C_{1,n}^{ab},
       &a=0,1,\\
 \mathcal B_{sa}=C_{n,s}^{a2},
       &2\le s\le q,\ a=1,2.
 \end{array}
 \tag{ZP7}
\]

There are \(2q+2+2(q-1)=4q\) new rows. All have zero prefix and
remain available under every subsequent append. Their total count is

\[
 3+\sum_{q=2}^{m-1}4q=2m(m-1)-1.
 \tag{ZP8}
\]

## The boundary append preserves the old scalar rank

For the induction, set \(u_n=0\) and \(v_n=v\ne0\). At G equal to
(ZP3), rows 0 and 1 of \(K_n\) coincide, whereas row 2 is different:

\[
 (K_n)_{0,:}=(K_n)_{1,:}
       =\frac{(X_0,0,vX_2)}{X_0+vX_2},\qquad
 (K_n)_{2,:}=\frac{(X_0,0,2vX_2)}{X_0+2vX_2}.
 \tag{ZP9}
\]

All source rows are zero-sum. Therefore \(R_0+R_1=-R_2\), and
(ZP6) gives

\[
 h(R^+)=\mu_v h(R),\qquad
 \mu_v=\frac{vX_0X_2}{(X_0+vX_2)(X_0+2vX_2)}.
 \tag{ZP10}
\]

Multiplication by this nonzero rational function is injective. The
appended old scalar family thus keeps its rank, and its restrictions to
both \(X_0=0\) and \(X_2=0\) vanish. Axis restrictions throughout
this proof are taken after canceling the final-coordinate factor in h.
They are rational identities on the axis, away from its finitely many
remaining poles.

## The first axis isolates \(2q+2\) new rows

Let \(Q^t\) be the increasing old word omitting t. The exact
commutator formula for the first family in (ZP7) is

\[
 C_{t,n}^{ab}
     =X_aK_t(a,b)e_b(Q^tK_n-K_nQ^t).
 \tag{ZP11}
\]

On \(X_2=0\), use \(X_0=1,X_1=y\), and define

\[
 w_t(y)=\left.\frac{e_0Q^te_2^{\mathsf T}}{X_2}
                  \right|_{X_0=1,X_1=y,X_2=0}.
\]

The old word has length \(q-1\ge1\). Its final column has the
factor \(X_2\). Direct substitution in (ZP11), retaining that factor
before restriction, yields

\[
 \begin{aligned}
 h(\mathcal A_{t0})&=\frac{v-w_t}{1+u_ty},&
 h(\mathcal A_{t1})&=\frac{y(v-w_t)}{1+2u_ty},\\
 h(\mathcal A_{*0})&=v-w_1,&
 h(\mathcal A_{*1})&=y(v-w_1).
 \end{aligned}
 \tag{ZP12}
\]

For example, on this axis the leading old distribution is supported on
states 0 and 1. The divided final column of \(Q^tK_n\) contributes v;
that of \(K_nQ^t\) contributes \(w_t\). Summing over b in the starred
rows retains the old transition row sum one. This verifies both the
prefix and the signs in (ZP12).

The functions \(w_t\) are independent of the new v. They have only
the old state-0 and state-1 poles from blocks other than t and are
\(O(1/y)\) at infinity. Thus the functions in (ZP12) have simple
poles among \(-1/u_t,-1/(2u_t)\) and a polynomial part of degree
at most one. These \(2q\) poles are distinct for generic old times.

Take their ordinary y-residues, followed by the constant and linear
coefficients of the polynomial part. The leading-in-v family is

\[
 \frac1{1+u_ty},\quad\frac y{1+2u_ty}\quad(1\le t\le q),
 \qquad 1,\ y.
 \tag{ZP13}
\]

Its residue pivots are \(1/u_t\) and \(-1/(4u_t^2)\). With these
paired column and row orders, the coefficient of \(v^{2q+2}\) in
the observation determinant is

\[
 \prod_{t=1}^q\frac{-1}{4u_t^3}
       =\frac{(-1)^q}{4^q\prod_tu_t^3}\ne0.
 \tag{ZP14}
\]

Consequently all \(2q+2\) rows in (ZP12) are independent for
generic v. Every \(\mathcal B_{sa}\) vanishes on this same axis:
its \(K_n(a,2)\) contributes \(X_2\), and its nonempty old product
difference contributes another \(X_2\), before h removes one factor.

## The other axis isolates \(2(q-1)\) further rows

On \(X_0=0\), use \(X_2=1,X_1=x\). The old active two-state
probability of outcome 2 evolves by \(p\mapsto a_t+d_tp\), where

\[
 \sigma=\tfrac12,\qquad\tau=\tfrac23,\qquad z_t=v_t/u_t,
 \qquad
 a_t=\frac{\sigma z_t}{x+\sigma z_t},\qquad
 d_t=\frac{x(\tau-\sigma)z_t}
            {(x+\sigma z_t)(x+\tau z_t)}.
 \tag{ZP15}
\]

Let \(P_s\) now denote the old move-s-first full word, and put

\[
 \delta_s=e_2(P_s-P_1)e_2^{\mathsf T},\qquad
 \Delta_q=\prod_{t=1}^q d_t.
 \tag{ZP16}
\]

All the old binary products have the same determinant. Their outcome-2
differences are therefore independent of the initial binary state.
On this axis the new kernel sends every state to state 2, so the
actual incoming difference in (ZP7) gives exactly

\[
 h(\mathcal B_{s2})=-\delta_s,\qquad
 h(\mathcal B_{s1})=-x\delta_s.
 \tag{ZP17}
\]

Write \(\delta_s^{(s)}\) for the same move-s-first difference on
the prefix \(1,\ldots,s\). The common increasing suffix gives

\[
 \Lambda_s:=\frac{\delta_s}{\Delta_q}
     =\frac{\delta_s^{(s)}}{\Delta_s},\qquad 2\le s\le q.
 \tag{ZP18}
\]

This is a Laurent polynomial with exponents from \(1-s\) through
\(s-1\). Indeed, the numerator after clearing the \(2s\) binary
line factors vanishes at zero and has degree at most \(2s-1\).
The endpoint coefficients follow directly from the last transition:

\[
 \begin{aligned}
 \delta_s^{(s)}
   &=\frac{x}{\tau}\left(\frac1{z_s}-\frac1{z_{s-1}}\right)
        +O(x^2) &&(x\longrightarrow0),\\
 \delta_s^{(s)}
   &=\frac{\sigma(z_{s-1}-z_s)}x+O(x^{-2})
        &&(x\longrightarrow\infty).
 \end{aligned}
 \tag{ZP19}
\]

If \(\ell_s^-,\ell_s^+\) are the coefficients of \(x^{1-s}\)
and \(x^{s-1}\) in \(\Lambda_s\), their product is

\[
 \ell_s^-\ell_s^+
   =\frac{\sigma^{s+1}\tau^{s-1}(z_s-z_{s-1})^2}
          {(\tau-\sigma)^{2s}z_sz_{s-1}}\ne0
 \tag{ZP20}
\]

whenever adjacent z values are distinct and nonzero. Relative to the
previous pairs, \(\Lambda_s,x\Lambda_s\) supply the two new
extreme exponents \(1-s,s\). Their coefficient matrix on those two
rows is diagonal with entries \(\ell_s^-,\ell_s^+\).
Peeling these endpoint rows from \(s=q\) down to 2 proves that all
\(2(q-1)\) functions are independent. Multiplication by the common
nonzero \(\Delta_q\) proves the independence in (ZP17).

In a relation among the extended family, restriction to \(X_2=0\)
first kills every \(\mathcal A\) coefficient by (ZP14). Restriction
to \(X_0=0\) then kills every \(\mathcal B\) coefficient by (ZP20).
The remaining old relation is zero only if all its coefficients vanish,
by the injectivity in (ZP10). This proves the rank increment \(4q\).

## Three-column base and positive generic witnesses

At \(m=2\), choose old times \((u_1,v_1)=(1,1)\) and
\((u_2,v_2)=(6,3)\). The rows in (ZP5) are
\(H_a=X_ae_a(K_2K_1-K_1K_2)\). Evaluate the scalar double
residues of \(h(H_a)\) at the following old cross-pole representatives:

\[
 P_{00}=(-3,-2,5),\qquad
 P_{11}=(-3,-1,5),\qquad
 P_{20}=(-3,-1,3).
\]

The first label is the state of block 1 and the second the state of
block 2. In row order \(00,11,20\), and column order \(a=0,1,2\),
the matrix is

\[
 \begin{pmatrix}-18&0&0\\0&6&0\\-54&0&27\end{pmatrix},
 \qquad \det=-2916\ne0.
 \tag{ZP21}
\]

These values can be checked without division by other pole factors:
at a block-1 state-a / block-2 state-b node, the entry for \(H_k\)
is

\[
 X_aX_b\left(
   \mathbf1_{k=b}A_2(b,a)A_1(a,2)
  -\mathbf1_{k=a}A_1(a,b)A_2(b,2)\right).
 \tag{ZP22}
\]

The displayed nodes have no unintended old poles, so this is an exact
three-column rational-function certificate.

For the induction, intersect the nonzero old-rank minor with the finite
open conditions on the old u poles and adjacent z values. This is
possible in the same irreducible time-parameter space with G fixed at
\(G_*\). Formula (ZP14) then permits a generic positive v. The
boundary specialization \(u_n=0\) is used only to establish a nonzero
coefficient minor, not as an admissible positive model instance.

To make this precise, let \(D_m=\prod_{t,a}L_{ta}\).
Every scalar source has the polynomial numerator \(D_mh(R)\).
At the boundary append, \(D_n/D_q=(X_0+vX_2)^2(X_0+2vX_2)\)
is a nonzero polynomial, and (ZP10) gives

\[
 D_nh(R^+)=vX_0X_2(X_0+vX_2)\,D_qh(R).
 \tag{ZP23}
\]

The established rational-function independence thus gives a nonzero
minor of polynomial coefficients at the boundary. It persists when
\(u_n>0\) is sufficiently small. The full rank condition is a nonempty
open condition on the new positive times, so the extra generic
conditions needed at the next induction step can be imposed as well.
This proves (ZP1) with fixed positive \(G_*\).

Some same-block line intersections at \(G_*\) lie on a coordinate
axis: for example, rows 0 and 1 agree on their state-0 and state-2
coefficients. Consequently \(G_*\) is not asserted to satisfy the
stronger general-position assumptions of the scalar ambient quotient.
The nonzero coefficient minor nevertheless persists under a small
positive perturbation of G. Its open set intersects the generic line
geometry conditions in the full common-G parameter family. Applying
ambient or pair-residue dimensions is justified only after this final
intersection.

## Combined bound and remaining problem

Multiplication by \(D_m\) identifies h with the scalar numerator map
\(p_2\). For \(m\ge4\), combine (ZP1) with the independently
established first- and second-normal restriction theorem to obtain

\[
 \boxed{\displaystyle
 \dim p_2(N)\ge
       \max\{8m-1,\ 2m(m-1)-1\}.}
 \tag{ZP24}
\]

Both bounds hold on nonempty opens of the same irreducible common-G
family, so they can be imposed simultaneously. The quadratic bound
equals the earlier bound at \(m=5\) and improves it for \(m\ge6\).

The generic scalar pair-residue quotient has dimension
\(9\binom m2\), and its observation complement has dimension \(3m\),
as specified in
[SOURCE24_NORMAL_RESTRICTIONS.md](SOURCE24_NORMAL_RESTRICTIONS.md).
The remaining pair-weight dimension is therefore at most

\[
 \boxed{\displaystyle
 \min\left\{
   9\binom m2-(5m-1),\ 
   \frac{5m^2+m+2}{2}
 \right\},\qquad m\ge4.}
 \tag{ZP25}
\]

This only uses the observation-map dimension bound: at least
\(\dim p_2(N)-3m\) dimensions lie in its kernel, on which the pair
map is injective. It does not assert that the newly constructed rows
individually have zero observations.

The natural next target is to find additional actual source directions,
or additional normal constraints, after quotienting by this explicit
zero-prefix image. The scalar transport (ZP10) is special to zero-prefix
rows and the chosen boundary kernel. It does not close the append
operation on an arbitrary scalar \(h(R)\) in N, whose full prefix and
other vector components can contribute. Full scalar spanning and the
remaining all-length source independence are still open.

## Independently reconstructed finite checks

The accepted external exact verifier
[source24_zero_prefix_extension.py](../exploration/source24_zero_prefix_extension.py)
and its
[saved results](../exploration/source24-zero-prefix-extension-results.json)
reconstruct the actual source words and the three-column base
determinant \(-2916\). They check the append identity, the multiplier
\(\mu_v\), and the A and B axis formulas directly against those words.
The finite rank certificates use the prime 1,000,003.

At both the recorded positive fixtures and their last-block boundary
specializations, the selected recursive family has ranks
3, 11, 23, 39, 59 for \(m=2,3,4,5,6\). The new boundary rows have
combined ranks 8, 12, 16, 20, exactly \(4q\), for the four append
steps. These channels are assembled before ranking; their ranks are
not added without the joint matrix. The core verification completed in
1.519261041 seconds with 21,479,424 bytes maximum RSS and no guard
cutoff.

The complete available zero-prefix family is larger than this selected
recursive family. At the recorded positive fixtures, its finite
observation ranks, followed by those of full N, are 26/27 at \(m=3\),
66/66 at \(m=4\), and 105/105 at \(m=5\). The focused boundary
comparison uses the entire old zero-prefix family in its first two
columns:

| New length m | Inherited old zero-prefix | Inherited plus selected \(4q\) | All zero-prefix rows | Full N |
|---|---:|---:|---:|---:|
| 3 | 3 | 11 | 25 | 26 |
| 4 | 26 | 38 | 57 | 57 |
| 5 | 66 | 82 | 93 | 93 |
| 6 | 105 | 125 | 138 | 138 |

All four ranks in each row use identical ordinary-point observations.
The records retain the actual coefficient inclusions, observation
matrices, evaluation points, and nonzero minors. This follow-up
completed in 3.714893541 seconds with 42,418,176 bytes maximum RSS and
no guard cutoff. These are exact finite observation ranks and
function-space lower bounds. Sampled deficits are not function-space
upper bounds, and the additional finite gains are not a uniform
extension theorem.

There is an exact boundary constraint that could guide the next step.
At \(u_n=0\), the two new lines \(L_{n0},L_{n1}\) coincide with
\(\ell=X_0+vX_2\). Each actual source uses block n at most once, so
its scalar rational function has at most a simple \(\ell\) pole.
Since \(D_n\) contains \(\ell^2\), every cleared numerator
\(D_nh(R)\) is divisible by \(\ell\). Determining the full image in
this constrained space for every length, and then the independent
directions supplied by a positive \(u_n\) perturbation, remains open.
The following scheme calculation supplies an ambient dimension bound;
its proof is independent of the finite rank pattern.

## The boundary ambient space, including the doubled old points

At \(G_*\), the old intersection \(L_{t0}=L_{t1}=0\) coincides
with the state-1 matching point. The correct replacement for six
distinct points is a length-six scheme with one doubled point.
All dimension arguments in this section are over characteristic zero.

For one old block use \((X,Y,Z)=(X_0,u_tX_1,v_tX_2)\). Its lines
become \(L_0=X+Y+Z\), \(L_1=X+2Y+Z\), \(L_2=X+3Y+2Z\).
Define \(Z_t\) by the four reduced points

\[
 Q_0=(0,1,-1),\quad Q_2=(-3,1,0),\quad
 P_{02}=(1,1,-2),\quad P_{12}=(-1,1,-1),
 \tag{ZP26}
\]

and the length-two scheme at \(R=(-1,0,1)\) with ideal
\((L_1,Y^2)\). The four cubics

\[
 f_{ta}=X_a\prod_{b\ne a}L_{tb},\qquad
 D_t^{\rm blk}=L_{t0}L_{t1}L_{t2}
 \tag{ZP27}
\]

have common projective zero scheme exactly \(Z_t\). Their local
ideals at the four reduced points are respectively
\((X,L_0),(Z,L_2),(L_0,L_2),(L_1,L_2)\). At R the other factors
are units, and the ideal is
\((L_1,YL_0)=(L_1,Y^2)\). Away from all three lines, vanishing of
the three f cubics would force all three coordinates to vanish.
On exactly one line \(L_a\), vanishing requires \(X_a=0\);
intersections of two lines are already listed. Thus there are no
additional common zeros.

Quadratic restriction to \(Z_t\) is an isomorphism onto its six
values and tangent data. Indeed, a quadric vanishing there vanishes
at the three distinct points \(P_{02},P_{12},Q_2\) on \(L_2\),
so is \(L_2L\) for a linear form L. Since \(L_2\) is a unit at R,
L must vanish on the doubled scheme and thus be a multiple of
\(L_1\). But \(Q_0\) lies on neither line, forcing zero.
Restricting a linear relation among the four cubics to each \(L_a\)
first kills the coefficient of \(f_{ta}\), proving their independence.
They therefore span the full degree-three vanishing space.
All four are used: the three f cubics
alone are not asserted to generate the saturated ideal.

Assume that the old schemes have pairwise disjoint supports. Choose,
for each s, a cubic \(b_s\) in (ZP27)'s span nonzero at every
other old support. This is possible because that span has base scheme
exactly \(Z_s\), so finitely many proper linear conditions can be
avoided. Then \(\prod_{s\ne t}b_s\) vanishes on every other old
scheme and is a unit on \(Z_t\). Multiply it by a quadratic with
the adjusted local values. This interpolates all \(6q\) old
conditions independently in degree

\[
 3(q-1)+2=3q-1.
 \tag{ZP28}
\]

In particular \(D_s^{\rm blk}\) need not be a unit on other old
supports; that stronger condition fails at some recorded fixtures.

Including the normalization at \(e_2=(0,0,1)\), the old scalar
ambient dimension at degree \(3q\) is exactly

\[
 \binom{3q+2}{2}-6q-1=d_q,\qquad d_q=9\binom q2+3q.
 \tag{ZP29}
\]

For the interpolation proof, multiply the old separators by a generic
line through \(e_2\) avoiding every old support. Then use \(D_q\),
which vanishes on the old schemes and is nonzero at \(e_2\), for
the last value.

### The new scheme and containment of actual sources

Put \(\ell=X_0+vX_2\), \(\widetilde\ell=X_0+2vX_2\).
After removing the common \(\ell\), the new block contributes

\[
 g_0=X_0\widetilde\ell,\quad g_1=X_1\widetilde\ell,\quad
 g_2=X_2\ell,\quad g_*=\ell\widetilde\ell.
 \tag{ZP30}
\]

These have common zero scheme
\(Z_n^\partial=(\widetilde\ell,X_2^2)\), of length two and
supported at \(e_1=(0,1,0)\). In the chart \(X_1=1\), \(g_1\)
supplies \(\widetilde\ell\), and \(g_2\) modulo that line is
\(-vX_2^2\). Their other common zeros are empty.

This constraint holds for every actual scalar source, including its
prefix. Cleared completed scalar path terms are constant multiples of
\(\prod_t f_{t,a_t}\). A divergent-output-2 prefix has form
\(f_{ta}\prod_{s\ne t}D_s^{\rm blk}\); a nonzero long-empty
scalar prefix is a multiple of \(D_m\). At the new block,
\(f_{na}/\ell=g_a\) and \(D_n^{\rm blk}/\ell=g_*\).
Consequently

\[
 \overline p=\frac{D_nh(R)}{\ell}
 \in I\!\left(Z_1\cup\cdots\cup Z_q
                   \cup Z_n^\partial\cup\{e_2\}\right)_{3q+2}.
 \tag{ZP31}
\]

The normalization at \(e_2\) survives because source rows vanish
there and \(\ell(e_2)=v\ne0\). Neither coordinate vertex belongs
to an old scheme.

### Interpolation and exact ambient dimension

Assume also that \(\widetilde\ell\) avoids every old support.
Choose a line H through \(e_2\) avoiding those supports. The
quadratic \(\widetilde\ell H\) vanishes on
\(Z_n^\partial\cup\{e_2\}\) and is a unit on each old scheme.
Multiplying the old separators from (ZP28) by it interpolates all
old values, with the new three conditions zero, in degree \(3q+1\).

Linear restriction to \(Z_n^\partial\cup\{e_2\}\) is an
isomorphism onto its three values. In \(X_1=1\), a form
\(aX_0+bX_1+cX_2\) gives value and tangent coefficient
\((b,c-2va)\) on the doubled point and value c at \(e_2\).
The determinant has absolute value \(2v\ne0\). Moreover

\[
 D_q(e_1)=\prod_t6u_t^3\ne0,\qquad
 D_q(e_2)=\prod_t2v_t^3\ne0.
 \tag{ZP32}
\]

Multiplying adjusted linear forms by \(D_q\) gives those three
conditions while vanishing on all old schemes. Thus all \(6q+3\)
conditions are independent already in degree \(3q+1\).
Multiplication by a line avoiding all supports gives the same
surjectivity in degree \(3q+2\). The ambient dimension in (ZP31)
is exactly

\[
 \boxed{\displaystyle
 \binom{3q+4}{2}-6q-3
   =\frac{9q^2+9q+6}{2}
   =d_q+6q+3=d_{q+1}-3q.}
 \tag{ZP33}
\]

The disjointness and nonvanishing conditions hold on a nonempty open
set of positive old times and positive new v, with \(G_*\) fixed.
This is an upper bound on the actual boundary image. It does not prove
that actual source rows fill this ambient space for every q.

### Exact consequences at the recorded fixtures

The fixtures use \(u_t=6^{t-1},v_t=3^{t-1}\); at the boundary the
new u is zero and the new \(v=3^q\). In original coordinates,
the old support types are

\[
 \begin{aligned}
 Q_{t0}&=(0,1,-u_t/v_t),&Q_{t2}&=(-3u_t,1,0),\\
 R_t&=(-v_t,0,1),&P_{t02}&=(1,1/u_t,-2/v_t),\\
 &&P_{t12}&=(-1,1/u_t,-1/v_t).
 \end{aligned}
 \tag{ZP34}
\]

Their supports are disjoint: coordinate-zero patterns separate the
first three types, positivity separates the remaining two types, and
the strictly varying u, v, and u/v values separate points of the same
type. The line \(\widetilde\ell\) also avoids every old support.
On \(R_t,P_{t02},P_{t12}\) its value, up to nonzero scaling, is
\(2(v/v_t)-1\), \(1-4(v/v_t)\), or \(-1-2(v/v_t)\);
here \(v/v_t=3^{q+1-t}\). The values at both Q types are nonzero
directly. Therefore (ZP33) applies at these fixed rational fixtures.

The saved nonzero minors modulo 1,000,003 lift to nonzero rational
minors: the actual coefficients and evaluation points are rational,
and every evaluation denominator used is a unit modulo that prime.
Combining these lower bounds with (ZP33) proves that both the complete
zero-prefix image and full N have boundary rational-function ranks
exactly 57, 93, and 138 at lengths 4, 5, and 6. The generic ranks
within the fixed-\(G_*\) boundary family have those same values at
these three lengths. At length 3 the ambient bound is 30 while the
saved N observation rank is 26; this does not prove exact rank 26.

Similarly, (ZP29) upgrades the positive-fixture zero-prefix and N ranks
66 and 105 at lengths 4 and 5 to exact scalar ambient spanning there.
These provide possible bases for a further induction with \(G_*\)
fixed. The missing statements are a uniform \(6q+3\) boundary gain
from a full old image, and control of the remaining \(3q\) directions
when the new u becomes positive. Neither follows from the finite cases
or the ambient dimension alone.

## An exact \(3q\)-dimensional target for the first perturbation

Keep the old times and new v fixed, set \(u_n=\varepsilon\), and
take a fixed constant combination of actual N generators. Let its
cleared numerator be \(p_\varepsilon=D_n(\varepsilon)h_\varepsilon\).
Suppose this combination is in the actual boundary kernel:
\(p_0\) is the zero polynomial. Then
\(g_\varepsilon=p_\varepsilon/\varepsilon\) is regular in
\(\varepsilon\), and \(g_0=p_1\) is the coefficient of
\(\varepsilon\) in p. The following is a statement about this
kernel, not about arbitrary source coefficients.

The new doubled point \(R=(-v,0,1)\) is fixed, with tangent direction
\((-2\varepsilon,1,0)\). Since \(g_\varepsilon\) satisfies its
value and tangent conditions, at \(\varepsilon=0\) one has
\(g_0(R)=\partial_1g_0(R)=0\). On
\(\ell=X_0+vX_2=0\), this is a double zero at \(X_1=0\).

In the chart \(X_1=1\), the four new simple points have coordinates
\((X_0,X_2)\) equal to \(\varepsilon\) times

\[
 (0,-1/v),\quad(-3,0),\quad(1,-2/v),\quad(-1,-1/v).
\]

Expanding \(g_\varepsilon\) at each point first gives
\(g_0(e_1)=0\). Subtracting their first-order equations removes
the common \(\varepsilon\) coefficient \(g_1(e_1)\).
The velocity differences \((-1,0)\) and \((-3,1/v)\) are
independent, so both affine first derivatives of \(g_0\) vanish
at \(e_1\). The restriction to \(\ell\) therefore also has a
double zero at \(X_2=0\). Since p has degree \(3q+3\),

\[
 p_1|_\ell\in
 X_1^2X_2^2\,\mathbb R[X_1,X_2]_{3q-1},
 \qquad
 \dim\mathbb R[X_1,X_2]_{3q-1}=3q.
 \tag{ZP35}
\]

Here \(\mathbb R[X_1,X_2]_d\) denotes homogeneous binary forms of
degree d. This argument uses the actual moving points and tangent
condition; it makes no assertion about a proposed saturated flat-limit
ideal.

There is also an explicit formula for the induced map. Each actual
path uses the new block at most once, so group the scalar combination as

\[
 h_\varepsilon=
 \frac{H_0(\varepsilon)}{L_{n0}}+
 \frac{H_1(\varepsilon)}{L_{n1}}+
 \frac{H_2(\varepsilon)}{L_{n2}}+
 H_{\rm reg}(\varepsilon),
\]

where the H coefficients are regular in \(\varepsilon\) and have
only old line poles. The new lines are
\(L_{n0}=\ell+\varepsilon X_1\),
\(L_{n1}=\ell+2\varepsilon X_1\), and
\(L_{n2}=\widetilde\ell+3\varepsilon X_1\).
The boundary-kernel condition implies
\((H_0(0)+H_1(0))|_\ell=0\). Differentiating
\(D_qL_{n0}L_{n1}L_{n2}h_\varepsilon\) and then restricting
to \(\ell\) gives

\[
 \begin{split}
 p_1|_\ell
   &=\left.D_qX_1\widetilde\ell\,
               (2H_0(0)+H_1(0))\right|_\ell\\
   &=\left.vX_1X_2D_qH_0(0)\right|_\ell,\\
 \Theta(p)&=\frac{p_1|_\ell}{X_1^2X_2^2}
        =\left.\frac{vD_qH_0(0)}{X_1X_2}\right|_\ell
          \in\mathbb R[X_1,X_2]_{3q-1}.
 \end{split}
 \tag{ZP36}
\]

The apparent divisions in the last expression are removable by
(ZP35). The derivative terms of the H coefficients contain a factor
\(\ell\) and disappear in this trace. Allowing regular
parameter-dependent source coefficients does not change the induced
map on a fixed boundary-kernel vector: their additional derivative
terms are combinations of boundary numerators, all divisible by
\(\ell\).

If the actual boundary image fills the space of dimension
\(d_q+6q+3\) in (ZP33), and \(\Theta\) on its coefficient kernel
is onto the \(3q\)-dimensional target, the first perturbation supplies
\(3q\) independent directions modulo that boundary image. Indeed,
restriction to \(\ell\) annihilates every boundary column, so these
are legitimate cokernel observations of the derivative. A corresponding
minor has nonzero leading coefficient, giving full scalar ambient rank
\(d_{q+1}\) for generic positive \(\varepsilon\). Surjectivity of
\(\Theta\), and uniform boundary spanning, remain unproved.

### A canonical inherited subfamily of the boundary kernel

Some genuine boundary relations can be constructed entirely from old
rows. Let R be an old zero-prefix combination with scalar component
R2 identically zero. Its zero row sum gives
\(R=R_1(e_1-e_0)\). Componentwise coordinate divisibility implies
\(R_1=X_0X_1f\), with \(D_qf\) a polynomial of degree
\(3q-1\). The same formal source coefficients append R to RK_n.
Rows 0 and 1 of the boundary kernel coincide, so this appended vector
vanishes identically at \(\varepsilon=0\).

For nonzero epsilon the exact difference of their outcome-2 entries is
\(-\varepsilon vX_1X_2/(L_{n0}L_{n1})\). Consequently

\[
 D_nh(RK_n)=-\varepsilon vX_1L_{n2}D_qR_1,
 \qquad
 \Theta(RK_n)=v^3(D_qf)|_\ell.
 \tag{ZP37}
\]

This uses a true old scalar-kernel vector; individually vanishing
new-output-1 source columns do not supply these relations.

The condition can be expressed without first choosing an old kernel
basis. On every old zero-prefix row define

\[
 B_v(R)=-\frac1v\,
       \frac{(D_qR_1/X_1)|_\ell}{X_2}
       \in\mathbb R[X_1,X_2]_{3q-1}.
 \tag{ZP38}
\]

The first coordinate division is removable by component divisibility.
The second is removable because R vanishes at e1, so its restricted
numerator vanishes at X2=0. On R2=0, (ZP38) equals
\((D_qf)|_\ell\). If A is the coefficient matrix of the old
cleared scalar component-two map and B is that of (ZP38), both on the
same original generator columns, then

\[
 \operatorname{rank}(\Theta\text{ on inherited relations})
 =\operatorname{rank}\begin{pmatrix}A\\B\end{pmatrix}
       -\operatorname{rank}A.
 \tag{ZP39}
\]

Thus, assuming old scalar rank dq, the augmented rank dq+3q is
equivalent to surjectivity from this inherited subfamily. Scalar full
span alone does not imply that joint condition. It controls the
projection to component two but does not determine where its kernel
lies relative to the other component's restriction. All coefficient
couplings in (ZP39) must be retained.

### Exact finite splitting certificates

`exploration/source24_zero_prefix_split_jet.py` applies the first derivative
to the systematic kernel in the original source coordinates, at the saved
boundary fixtures. It checks the old six-condition schemes and the boundary
interpolation hypotheses over the same field, of prime order 1,000,003.
The boundary ranks saturate (ZP33), so the computed evaluation kernels are
the actual polynomial kernels over that field.

The new kernel is never inverted on the merged line. At
\(X=(-v,x,1)\), direct differentiation of the polynomial matrix
\((L_{n0}L_{n1}L_{n2})K_n\) gives

\[
 J_n=\begin{pmatrix}
 2xv(-v)&0&2xv^2\\
 xv(-v)&0&xv^2\\
 0&0&0
 \end{pmatrix}.
 \tag{ZP40}
\]

Inserting this matrix at the actual position of the new block computes
the derivative without a singular rational evaluation. Independent dual
arithmetic on the actual rational words checks the cleared derivative at
ordinary points. The verifier then applies the original-coordinate kernel,
divides its trace by x squared, and interpolates its 3q coefficients.
Six additional points check each interpolation; the degree bound is (ZP35),
not an extrapolation from those checks.

| New length n | Boundary rank | Induced trace rank | Combined rank | Mixed minor mod p |
| --- | ---: | ---: | ---: | ---: |
| 4 | 57 | 9 | 66 | 244881 |
| 5 | 93 | 12 | 105 | 60146 |
| 6 | 138 | 15 | 153 | 468890 |

The mixed matrix uses independent boundary columns followed by selected
original-coordinate kernel vectors. Its upper-right block is zero, and
its determinant is checked against the product of the two pivot minors.
These are genuine leading coefficients of minors of the source family
along the new-u curve: the lower observations are restrictions of cleared
numerators to ell, whose constant terms vanish for every source column.
After dividing those observation rows by epsilon, their limits are exactly
the derivative observations used in the certificate.

A nonzero minor over the rational-function field in epsilon modulo p
witnesses a nonzero characteristic-zero polynomial minor after clearing
denominators. This lifting argument does not lift each modular kernel
vector as a characteristic-zero relation. It lifts the nonvanishing of
the resulting source minor. Consequently, for each of n=4,5,6 the actual
zero-prefix scalar image, and therefore the N scalar image, generically
fills the ambient space at fixed G*. In particular, the new n=6 case has
generic scalar rank 153. A positive value of the new u can be chosen away
from the finitely many roots of that minor.

For q=4,5, the inherited old scalar kernels alone have trace ranks 12 and
15. The verifier checks their inclusion in the new boundary kernel and
both identities (ZP37), using independent component-one evaluations of the
old words. It does not use the unsaturated sampled q=3 kernel.

All matrices, source coefficients, kernel bases, selected minors, geometry
checks, and hashes of the referenced boundary matrices are saved in
`exploration/source24-zero-prefix-split-jet-results.json`. The run exited
zero in 2.477699792 seconds, with maximum RSS 66,535,424 bytes and no
resource guard hit. These are external exact finite certificates with
the paper lifting argument above. They are not Lean certificates, and
they do not prove uniform trace surjectivity.

## A uniform extension by all 6q+3 boundary directions

The previous 4q increment can be strengthened to 6q+3. The proof below
uses a filtration of observations on one common fixed-G* parameter
family. In particular, the matching observations are applied after both
axis restrictions have been eliminated. No closure of N under rational
scalar multiplication is assumed.

Retain the old A and B families from (ZP7), of sizes 2q+2 and
2q−2. Write Q^t for the increasing old word omitting t and P_t for
the old word with t first. Add the following actual zero-prefix rows:

\[
 M_{t,0}=C_{t,n}^{02},\qquad M_{t,2}=C_{t,n}^{20}\quad(1\le t\le q),
 \qquad E=F_{\emptyset,n,2}-F_{\emptyset,1,2}.
 \tag{ZP41}
\]

Set \(S_t=\sum_b C_{t,n}^{2b}\),
\(T_1=E-S_1\), and \(T_2=E-S_2+B_{2,2}\).
The new family is A, B, all M, T1, T2, E, with 6q+3 columns.
Its coefficients in the source family are 0 and ±1.

First, the accepted X2=0 observations separate A. Their determinant
has leading coefficient \((-1)^q/(4^q\prod_tu_t^3)\) in degree
2q+2 of v. All other new rows and all inherited scalar rows vanish
on that axis.

### The remaining two axis pivots

On X0=0, X2=1, put x=X1, z_t=v_t/u_t, sigma=1/2, tau=2/3,
c=tau−sigma, and retain d_t and Delta_q from the binary calculation.
Let delta_t=(P_t−P_1)22, V_t=1−(P_t)22, and V^t=1−(Q^t)22.
The binary slope of Q^t is Delta_q/d_t. Its input from the first
block t, starting in state 2, has state-1 probability
b_t=x/(x+tau z_t). Therefore

\[
 V_t=V^t+\frac{\Delta_q}{d_t}b_t,
 \qquad V_t=V_1-\delta_t.
 \tag{ZP42}
\]

The new boundary kernel resets every row to state 2 on this axis.
The actual source formulas give h(E)=V1, h(S_t)=V^t, and
h(B_t2)=−delta_t, with B_12=0. It follows that

\[
 h(T_t)|_{X_0=0}=\Delta_q U_t,
 \qquad U_t=\frac{x+\sigma z_t}{c z_t}\quad(t=1,2).
 \tag{ZP43}
\]

The accepted Laurent endpoint argument gives a basis
\(\{\delta_s/\Delta_q,x\delta_s/\Delta_q:2\le s\le q\}
\cup\{1,x\}\) of the powers x^(1−q) through x^q.
The determinant of U1,U2 in the last two coordinates is
\(\sigma c^{-2}(1/z_2-1/z_1)\ne0\).
Thus B,T1,T2 supply 2q independent axis pivots. These restrictions
depend only on old parameters.

Also V1/Delta_q lies in that same Laurent space: the binary numerator
has degree at most 2q, is divisible by x, and division by Delta_q
removes its denominator and divides by a nonzero multiple of x^q.
Consequently E's second-axis restriction can be eliminated using B,T,
with coefficients depending only on old parameters. Call the corrected
row E0. It vanishes on both axes.

### The 2q matching pivots on the joint axis kernel

Boundary clearing writes h=pbar/(D_q ell tilde). If h vanishes on
both axes, pbar is divisible by X0 X2. Hence h/mu has only old line
poles. On this subspace define the observation

\[
 \mathcal M_{ta}(h)=
  \left.\left(L_{ta}\frac h\mu\right)\right|_{L_{ta}=0}(Q_{ta}),
 \quad Q_{t0}=(0,-z_t,1),\quad
 Q_{t2}=(1,-1/(3u_t),0),\quad a=0,2.
 \tag{ZP44}
\]

The line is restricted first, and all other old denominators are
required to be units at the indicated point. These are generic
conditions. The observation annihilates an inherited mu h_old by
the old matching condition.

Put q_tb=e_b Q^t e2, W_t=q_t0/X2, and

\[
 H_t=\widetilde\ell(1-q_{t2})-\frac{X_0\ell}{v}W_t.
 \tag{ZP45}
\]

Direct multiplication, using
\(K_ne_2=(vX_2/\ell)\mathbf1+\mu e_2\), gives the same
column-2 commutator entry in rows 0 and 2:
\((vX_2/\ell)(1-q_{t2})-(X_0/\widetilde\ell)q_{t0}\).
The actual source differences therefore satisfy

\[
 \frac{h(M_{t,0})}{\mu}=\frac{v_tH_t}{L_{t0}},
 \qquad
 \frac{h(M_{t,2})}{\mu}=\frac{H_t}{L_{t2}}.
 \tag{ZP46}
\]

These rows vanish on both axes. At another block's matching point,
H_t has zero matching residue. For q_t2, a state-0 pole requires a
previous arrival with factor X0, and a state-2 matching residue retains
the final X2 factor. For W_t, a state-2 pole requires a separate arrival
factor X2 even after the final X2 is removed; its possible state-0
residue is killed by the explicit X0 in (ZP45).
Thus the matching matrix on M is diagonal, with entries

\[
 2vv_t(1-\eta_t),\qquad 1-\omega_t/v,
 \quad \eta_t=q_{t2}(Q_{t0}),\quad\omega_t=W_t(Q_{t2}).
 \tag{ZP47}
\]

For each t, 1−eta_t is a nonzero rational function. For example,
fix z_t and let all other old z_s tend to zero; at x=−z_t the
remaining binary kernels tend to the state-1 absorber, so eta_t tends
to zero. Each omega_t is independent of new v. The matching
determinant is therefore the nonzero rational function
\(2^q\prod_tv_t(1-\eta_t)\prod_t(v-\omega_t)\).

### The last vertex jet

Define j(h) as the coefficient of epsilon in h(epsilon,0,1).
All denominators here are units at epsilon=0. An inherited row
mu h_old has j=0, since mu=epsilon/(2v)+O(epsilon²) and
h_old(e2)=0. The M rows also have j=0: their scalar formulas contain
X0 times the commutator entry, which vanishes at e2.

If a nonempty old word ends with block k, its state-2 probability
starting from state 2 is 1−epsilon/(2v_k)+O(epsilon²). At zero,
all earlier matrices reset to state 2, so only the last transition
contributes this first derivative. Writing k(t)=max({1,...,q}−{t}),
the actual words give

\[
 \begin{split}
 j(E)&=1/(2v_q)-1/(2v),\\
 j(S_t)&=1/(2v_{k(t)})-1/(2v),\\
 j(B_{t,2})&=1/(2v_{k(t)})-1/(2v_q),\qquad j(B_{t,1})=0.
 \end{split}
 \tag{ZP48}
\]

In particular j(T1)=j(T2)=0. The old-only axis correction of E
therefore leaves j(E0)=c_old−1/(2v), a nonzero rational function.
Eliminate its matching observations using M. That correction has
zero j, so the last pivot survives unchanged.

The resulting filtered observation determinant is, up to a nonzero
sign, the product of the A determinant, the B/T axis determinant,
the matching determinant, and c_old−1/(2v). Each factor is nonzero
over the same old-parameter field with new variable v. All required
generic conditions therefore intersect any old independent-family
open set. This proves

\[
 \boxed{\text{old scalar rank }r
       \quad\Longrightarrow\quad
       \text{new scalar rank at least }r+6q+3.}
 \tag{ZP49}
\]

The new columns are independent modulo the entire inherited old
scalar ambient, not just modulo the selected old basis. Thus if the
old zero-prefix image is full, (ZP49) and (ZP33) prove full boundary
spanning. Generic positive new u follows by nonvanishing of a cleared
coefficient minor, as in the earlier extension argument.

Starting from the rational three-column length-two base gives the
uniform bound 3m²−9. The stronger finite bases above give 66 at
m=4, 105 at m=5, and

\[
 \dim p_2(N)\ge3m^2+45\quad(m\ge6),
 \qquad
 d_m-\dim p_2(N)\le\frac32(m-6)(m+5).
 \tag{ZP50}
\]

For the last bound, choose the finite 153-dimensional zero-prefix
base at m=6, then apply (ZP49) repeatedly. At each step the old
parameters lie in the positive independent-family open set; earlier
boundary specializations are not retained. The bound is a paper
theorem with external finite base certificates. It is not a Lean
theorem, uniform scalar spanning, or equation-(24) independence.

The separate verifier `source24_zero_prefix_boundary_extension.py`
tests these actual 6q+3 columns modulo all inherited zero-prefix
generators. The original old times (6^(t−1),3^(t−1)) give gains
15,21,26,32 at q=2,3,4,5. They violate the matching-point genericity
hypothesis: z_t=z_(t−1)/2 places Q_t0 on the preceding block's
state-1 line. These deficient observations are retained, rather than
treated as a generic refutation or silently discarded.

One prescribed alternative, old times (7^(t−1),3^(t−1)), new u=0
and new v=3^q, avoids every required matching collision and gives:

| q | Inherited observed rank | New gain | Joint rank | Joint minor mod 1,000,003 |
| --- | ---: | ---: | ---: | ---: |
| 2 | 3 | 15 | 18 | 279735 |
| 3 | 26 | 21 | 47 | 28317 |
| 4 | 66 | 27 | 93 | 993774 |
| 5 | 105 | 33 | 138 | 987904 |

All candidate columns occur in the joint pivot minors. Independent
actual-word checks verify (ZP46), the scalar append, and source-coordinate
inclusions. Canceled matching matrices are diagonal of ranks 4,6,8,10;
omega is computed both as a dual derivative and by stripping the final
transition's output factor. Other-block residue checks vanish as required.
The saved JSON includes both fixtures, their actual source coordinates,
minors, pole collisions, and denominator checks. The alternative run
exited zero in 2.030978042 seconds, at maximum RSS 73,105,408 bytes,
without hitting a guard. These finite checks corroborate the uniform
paper argument; they do not replace it.

### Why the joint condition does not propagate automatically

The next plausible invariant is the augmented scalar/restriction rank
in (ZP39). Its naive boundary induction has a precise obstruction.
Use an auxiliary line X0=−w X2, with w different from 0,v,2v.
On this line the boundary new kernel is constant after cancellation.
The old kernels are regular at e1. Therefore R1/X1 for every actual
boundary source is regular at e1, whereas

\[
 D_n|_{X_0=-wX_2}=(v-w)^2(2v-w)X_2^3D_q|_{X_0=-wX_2}.
 \tag{ZP51}
\]

Its B_w observation is divisible by X2². The target at length n
has dimension 3q+3, but the boundary restriction image has dimension
at most 3q+1, even before imposing the scalar kernel. Two endpoint
coefficients are missing.

For a genuine old scalar-kernel row R1=X0 X1 f, the append gives
the following exact auxiliary polynomial, with epsilon=u_n:

\[
 B_w(RK_n)=\varepsilon(v-w)X_1X_2
     [3\varepsilon X_1+(2v-w)X_2]
     (D_qf)|_{X_0=-wX_2}.
 \tag{ZP52}
\]

Its first coefficient is also divisible by X2². Its second coefficient
can reach the linear endpoint, but that value is
3(v−w)(D_q f)(e1). The already used scalar trace (ZP37) has endpoint
v³(D_q f)(e1). Thus any inherited combination preserving all first
scalar traces kills this proposed second-order endpoint as well.
One cannot add its rank to the scalar rank independently.

The unresolved induction must construct additional actual relations
after the scalar eliminations, or an equivalent coupled argument.
Neither the full boundary gain nor the finite inherited-jet bases
alone prove that assertion.

### The actual scalar kernel loses three boundary endpoints

There is a sharper statement than (ZP51) after imposing R2=0.
In the chart X1=1, write X0=−wz, X2=z. Every old kernel tends
to the state-1 reset matrix, and the new boundary kernel is constant.
Its first two rows equal k=(−w,0,v)/(v−w). Every zero-prefix
boundary row is analytic in z and has constant term
\(\kappa(k-e_1)\): a completed word ending in an old block tends
to e1, a word ending in the new block tends to k, and only state-1
old prefixes can contribute a nonzero constant term. New-prefix
output-1 terms vanish; the other new-prefix differences have zero
constant term because both old tails reset to e1.

If R2 is identically zero, k2=v/(v−w) forces kappa=0. Hence
R1=O(z), and (ZP51) now implies

\[
 B_w(\ker p_2\text{ at the boundary})
   \subseteq X_2^3\,\mathbb R[X_1,X_2]_{3q-1},
 \qquad \operatorname{rank}\le3q.
 \tag{ZP53}
\]

Thus the joint induction must recover three endpoint coefficients,
not just the two excluded for arbitrary boundary rows.

`source24_zero_prefix_joint_boundary.py` checks B_w at w=5 on the
same original-coordinate boundary kernels used for Theta. It verifies
cleared words without division, interpolation with six extra points,
and a single stacked matrix for both maps. The saved highest coefficient
row vanishes, consistently with (ZP53). It gives:

| n | Boundary scalar rank | B_w on its kernel | [B_w; Theta] on the same kernel | Scalar plus both |
| --- | ---: | ---: | ---: | ---: |
| 4 | 57 | 9 | 18 | 75 |
| 5 | 93 | 12 | 24 | 117 |
| 6 | 138 | 15 | 30 | 168 |

The stacked maps have zero row-space overlap at these fixtures. Their
mixed minors are 605343,703342,563527 modulo 1,000,003. Combining the
finite lower bounds with (ZP53) proves that the boundary auxiliary
kernel rank is generically exactly 3q at these three lengths; it does
not prove this for every q. The remaining joint target is respectively
78,120,171. The main run took 1.011 seconds and 59,736,064 bytes RSS;
the saved-coefficient follow-up checked the sharper zero row without
rerunning evaluations or ranks. All data are in the corresponding
`source24-zero-prefix-joint-boundary-results.json`.

### Two endpoint lifts after the actual scalar projection

The following lemmas are conditional on old scalar spanning and
surjectivity of the inherited trace in (ZP37). Those hypotheses provide
a full scalar basis at positive new u=epsilon: independent appended
old columns, the 6q+3 new boundary columns, and 3q unscaled inherited
kernel columns whose numerators begin at order epsilon. No uniform
version of these hypotheses is inferred here.

Define signed terminal incidences ell_t by the completed-word
expansion of a zero-prefix row. At e1 only initial state 1 and shared
state 1 survive. A completed word contributes the divided output
values of its final transition, so, with
a_t=1/(2u_t), b_t=v_t/(2u_t),

\[
 (R_0/X_0)(e_1)=\sum_t\ell_t a_t,
 \qquad (R_2/X_2)(e_1)=\sum_t\ell_t b_t.
 \tag{ZP54}
\]

All appended old zero-prefix rows have zero incidence: every term ends
with n and their prefix weights cancel. Among the selected new columns
only Astar1=sum_b C_1n^(1b) has nonzero incidence, namely e_n−e_q.
All other A, B, M, T, E columns have zero incidence.

First use C=C_nq^(11), with incidence e_q−e_(q−1). In its unique
scalar expansion in the stated basis, evaluation at e1 forces the
Astar1 coefficient to be
kappa=(b_q−b_(q−1))/(b_n−b_q). Subtract the entire scalar expansion
to obtain an actual row R with R2=0. With p_i=D_n R_i/X_i,

\[
 p_0(R)(e_1)=D_n(e_1)\frac{\Delta}{b_n-b_q},\qquad
 \Delta=(b_n-b_q)(a_q-a_{q-1})-(a_n-a_q)(b_q-b_{q-1}).
 \tag{ZP55}
\]

This is generically nonzero: a_n=1/(2epsilon), b_n=v/(2epsilon),
and its leading coefficient in epsilon^(-1) is a nonzero rational
function of v and the old times. For any scalar-zero R, zero row sum
gives B_w=−p0|auxline/X1. Thus this corrected row has nonzero
constant auxiliary endpoint, B_w(R)(e1)=−p0(R)(e1).

For a second row take C=C_nq^(01). Let V=e1(P1−Pq) for old words.
Exactly C=epsilon X0 X1 V/L_n0. Its scalar numerator begins with
epsilon ell X0 tilde p_old, where p_old=D_q X1 V2/X2 is in the
old scalar ambient. This coefficient belongs to the full boundary
image: after removing ell, it satisfies the old conditions, the new
tilde factor, and normalization at e2.

In the scalar basis above, every coefficient of C is O(epsilon).
To see this, divide the inherited kernel columns by epsilon: the
limiting basis is independent because their ell traces complement
the boundary image. The inverse has at most a simple pole in the
unscaled basis. At order zero the boundary coefficients vanish;
at order one, the ell trace of C's first coefficient is zero, forcing
the unscaled jet coefficients' constant terms to vanish too.
The Astar1 coefficient is exactly zero by (ZP54), since C has zero
incidence and b_n−b_q is nonzero.

Set
\(J_x(R)=\partial_0(p_0-v^{-1}p_2)(e_1)\).
For any appended old row, direct multiplication gives
p0−p2/v=−D_q R2 L_n0 L_n1, so Jx=0 exactly. Among the other
selected new basis columns only A_t1=C_tn^(10) and Astar0 can
contribute Jx; their values are O(epsilon³). Their terminal new-block
terms cancel because a_n−b_n/v=0. The other selected columns have
a remaining X2 factor or at least two X0 factors after the output
division. Direct calculation for C gives

\[
 J_x(C)=6D_q(e_1)\varepsilon^3
       \left[(a_q-a_{q-1})-\frac{b_q-b_{q-1}}v\right].
 \tag{ZP56}
\]

Its scalar projection changes this only at order epsilon^4, since
all contributing projection coefficients are O(epsilon). The
corrected scalar-zero row therefore retains a nonzero leading Jx.
Its constant auxiliary endpoint is zero by its zero incidence.
Its linear endpoint, in the chart X1=1, is
w partial_0 p0(e1)−partial_2 p0(e1), which is nonzero for generic w:
the row and its scalar-projection coefficients do not depend on w,
and partial_0 p0=Jx is nonzero.

These two corrected rows give

\[
 \operatorname{rank}(\text{constant and linear auxiliary endpoints
 on the actual scalar kernel})=2
 \tag{ZP57}
\]

under the stated scalar-basis hypotheses. Both lifts were checked
independently against the actual source words. The quadratic endpoint
and the uniform auxiliary body rank remain open. Separate body and
endpoint ranks cannot be added without checking their common kernel.

### A third conditional endpoint lift

Keep the same hypotheses and assume q>=4. Let C2=C_nq^(01) be
the second candidate above, put s=q−2, and set C3=C_ns^(11).
For C3 the old word difference V=e1(P1−Ps) has the common final
blocks q−1 and q. On X2=0, X1=1, each binary suffix determinant
starts with a_j X0. The preceding difference starts with
(a_s−a_(s−1))X0. Hence

\[
 V_0=KX_0^3+O(X_0^4),\qquad
 K=(a_s-a_{s-1})a_{q-1}a_q\ne0.
 \tag{ZP58}
\]

The final old transition also gives
V2/X2=v_q V0/X0 on this axis after cancellation. Define
Jxx=partial_0²(p0−p2/v)(e1). Like Jx, it vanishes exactly on
every appended old row. Direct cancellation in the two new candidates
gives, with D*=D_q(e1) and delta=a_q−a_(q−1)−(b_q−b_(q−1))/v,

\[
 \begin{array}{ll}
 J_x(C2)=6D_*\varepsilon^3\delta,&
 J_{xx}(C2)=10D_*\varepsilon^2\delta+O(\varepsilon^3),\\
 J_x(C3)=0,&
 J_{xx}(C3)=12D_*\varepsilon^3K(1-v_q/v).
 \end{array}
 \tag{ZP59}
\]

For example, the C2 polynomial multiplier on this axis is
epsilon X0(X0+2epsilon)(X0+3epsilon). Its linear and quadratic
coefficients are 6epsilon³ and 5epsilon²; the latter second
derivative accounts for the factor 10.

For both candidates the first scalar coefficient in epsilon lies
in the boundary image, so the previous projection argument makes
every scalar-basis coefficient O(epsilon). The Astar1 coefficient is
exactly zero, since both candidates have zero terminal incidence.
Only the A columns can affect Jx or Jxx. They have Jx=O(epsilon³)
and Jxx=O(epsilon²); A_t0 has Jx=0 and Jxx=O(epsilon³).
The remaining columns retain X2 and contribute neither derivative.
The leading coefficients in these orders stay bounded as v tends
to infinity. The terminal new-block terms cancel in p0−p2/v;
the remaining coefficients involve old divided outputs and their
derivatives. The old tails contain at least two terminal matrices,
so derivatives of the initial new kernel do not introduce an
uncontrolled coefficient at these orders.

The order-epsilon A projection coefficients are O(1/v). Indeed,
restrict the first scalar coefficient to X2=0. For C2 and C3 this
restriction is independent of v. Other basis columns have zero
boundary restriction, whereas the A matrix is v times an invertible
leading matrix plus an old-only matrix, by (ZP12)--(ZP14).
Thus its inverse is O(1/v). This bound uses the same scalar
projection as the endpoint calculation.

For the scalar-zero residuals R2,R3, these bounds give

\[
 \begin{split}
 J_x(R2)&=6D_*\varepsilon^3\delta+O(\varepsilon^4),\\
 J_{xx}(R2)&=10D_*\varepsilon^2\delta+O(\varepsilon^3),\\
 J_x(R3)&=\varepsilon^4 O(1/v)+O(\varepsilon^5),\\
 J_{xx}(R3)&=\varepsilon^3
       [12D_*K(1-v_q/v)+O(1/v)]+O(\varepsilon^4).
 \end{split}
 \tag{ZP60}
\]

First take the coefficient of epsilon^6 in det(Jx,Jxx), then let
v tend to infinity. Its limit is
72D*²(a_q−a_(q−1))K, which is nonzero. This ordered expansion
proves nonvanishing of a rational function; it does not exchange
an uncontrolled pair of limits.

Both corrected rows have exactly zero constant auxiliary endpoint.
On scalar-zero rows B_w=−p0|auxline/X1, so the coefficient of w³
in their linear/quadratic endpoint determinant is
−det(Jx,Jxx)/2. This determinant is generically nonzero. Together
with (ZP55), the actual scalar kernel therefore maps onto all three
endpoint coordinates, under the same old scalar/trace hypotheses.
This is a conditional paper lemma, independently checked locally.
It does not by itself prove the full auxiliary rank: the endpoint
correction against a basis for the remaining coefficients must still
be retained.

### The remaining body map without an old scalar inverse

The boundary observations in (ZP41)--(ZP49) give an isomorphism from
the boundary scalar ambient modulo its inherited old ambient to
6q+3 quotient coordinates: they annihilate the latter, and the
displayed 6q+3 columns give full rank in a quotient of exactly that
dimension. Apply these coordinates to all new zero-prefix generators,
and let Knew be their coefficient kernel. Under old scalar fullness,
every row in Knew can have its scalar component canceled by an
appended old zero-prefix row. The latter has component one identically
zero at the boundary, so this correction does not change B_w.

Conversely, decomposing an actual boundary scalar-kernel row into old
and new generators puts its new part in Knew. Thus the desired
auxiliary image is exactly

\[
 B_w(\text{actual boundary scalar kernel})
       =B_w(K_{\rm new}).
 \tag{ZP61}
\]

This removes the old scalar inverse from the body problem while
preserving all coefficients. The unresolved uniform condition is
rank B_w(Knew)=3q. Even after proving that condition, the endpoint
Schur correction on the same coefficient space must be shown
nonsingular. Simply inserting the new kernel on the left of an old
scalar relation is not justified by the actual move-first source
words. Right appending such a relation instead kills it identically
at the boundary because the new rows 0 and 1 coincide.
