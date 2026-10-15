# A quadratic lower bound from zero-prefix source rows

**Status: independently checked paper algebra; not Lean formalized.**
The [Pro19 investigation](https://chatgpt.com/c/6ad1572b-b950-83ed-92cb-6eaa72dc3df9)
proposed the recursive family below. Local independent review checked
the actual source words, both axis restrictions, the Laurent endpoint
argument, the three-column base, and the parameter perturbation.
The result is a lower bound on the actual scalar image of N, not a
proof that this image fills its ambient space.

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
