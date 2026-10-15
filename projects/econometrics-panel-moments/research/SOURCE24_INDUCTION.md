# Equation (24): an induction and a quadratic-size residue test

Research note, 15 October 2026. The algebraic arguments below reduce the
three-choice independence problem to explicit finite determinants and prove
generic nonvanishing of the shared-new polar half. Some supporting source
recursion statements and the binary scalar-span parity recurrence are now
formalized in Lean; [STATUS.md](../STATUS.md) gives the exact scope. The
polar theorem is a paper proof. Nonvanishing of the remaining regular Schur
half for every panel length remains unproved, so the complete all-length
source-independence claim remains open.

## Exact split of the source family

Use the paper's one-based time labels and three alternatives. Its restriction
on the shared positions is

\[
 t_r=r\qquad(1\le r\le \max(0,j-1)).
\]

Consequently, the equation (24) columns whose shared set contains period 1
are exactly three indicator lifts of the complete source family for the
remaining \(T-1\) periods: fix \(y_1=a\), delete the first shared position,
shift the other time labels, and use initial outcome \(a\). Their supports
for different \(a\) are disjoint. The remaining columns have either
\(j=0\), or \(j=1\) with shared position \(t\ge2\). Put \(n=T-2\). Their
number is

\[
 3n+9n(n-1)=3n(3n-2)
 =\ell(3,T)-3\ell(3,T-1).
\]

Thus, once the shorter source family is a basis, independence at length
\(T\) reduces to independence of these new columns modulo the three
conditional moment spaces for the shorter panel.

## An explicit quotient map

Let \(X=(X_0,X_1,X_2)\) be homogeneous effect coordinates. Index the
transition following outcome \(y_t\) by \(t\). Thus its coefficient matrix
is the paper's time-\(t+1\) index table. For \(t\in B:=\{2,\ldots,T-1\}\),
write

\[
 L_{ta}=\sum_i A_t(a,i)X_i,\qquad
 v_{ta}=(A_t(a,i)X_i)_i,\qquad
 K_t=\operatorname{diag}(L_{t0},L_{t1},L_{t2})^{-1}A_t
       \operatorname{diag}(X_0,X_1,X_2).
\]

All vectors below are row vectors. Each \(K_t\) has row sum one. Let
\(P_s^C\) denote the product of the matrices indexed by a nonempty set
\(C\), with \(s\in C\) first and all remaining indices in increasing
order. An empty product is the identity.

For a moment \(m\), the three rational functions

\[
 C_i(X)=\sum_{y:y_1=i}m(y)p_y(X)
\]

are its image modulo the three shorter conditional moment spaces: their
joint kernel is precisely the direct sum of those spaces. For source
columns, compute these functions by replacing the likelihood times its
scale ratio by the transformed-chain likelihood, then summing the chain
after the occurrence of \(y_1\). These sums telescope because the matrices
have row sum one.

Multiply all three components by the common initial denominator and divide
each column by its nonzero initial-row coefficient. The new source columns
then have the following images:

\[
 F_{s,a}=X_a e_a(I-P_s^B),\qquad s\in B,
\]

and

\[
 F_{t,s,a,b}=X_aK_t(a,b)e_b(I-P_s^{B\setminus\{t\}}),
 \qquad t,s\in B,\quad t\ne s.
\]

Here \(a\) is the value of the shared outcome \(y_t\), and \(b\) is the
value at the position where the two orders first differ. These formulas
retain the paper's precise increasing-order suffix convention.

The quotient images depend only on the tail matrices with indices in
\(B\). The transition following period 1 disappears in the telescoping
sum. The initial outcome changes only the nonzero column factors removed
above. More generally, every source numerator has the initial-row
coefficient of its fixed first-generated state as a column factor, while
the original likelihood numerator supplies nonzero row factors. Thus
source rank is the same for every initial outcome at a positive table.

## The zeroth-level columns reduce exactly to single-block relations

Define

\[
 E_{t,a}=X_a e_a(I-K_t).
\]

For \(n\ge2\), choose \(r=\min(B\setminus\{s\})\). The elementary
identity \(I-K_sP=(I-K_s)+K_s(I-P)\) gives

\[
 F_{s,a}=E_{s,a}+\sum_b F_{s,r,a,b}.
\]

Therefore subtracting the displayed sum of first-level columns replaces
each zeroth-level column by \(E_{s,a}\). This is an invertible column
operation with constant coefficients. No coefficient depending on \(X\)
is used. When \(n=1\), the equality \(F_{s,a}=E_{s,a}\) is immediate.

## A canonical basis of the quotient relation space

Let

\[
 D=\prod_{t\in B}\prod_a L_{ta},
\]

and let \(Z\) be the union of the six base points of each block, as in
the structural dimension proof. Consider the real vector space

\[
 W_n=\left\{\left(\frac{X_i g_i}{D}\right)_i:
 g_i\in I(Z)_{3n},\quad \sum_i X_i g_i=0\right\}.
\]

Under the primitive conditions of the structural theorem, this is the
quotient of the full moment space by the three shorter conditional moment
spaces. Indeed, splitting the cleared polynomial by \(y_1=i\) gives a
relation \(\sum_i h_i c_i=0\) for the first cubic block. The one-block
divisibility argument gives \(c_i=L_i g_i\) and \(\sum_iX_i g_i=0\).
Cross-block nonincidence makes \(c_i\) vanish at every tail base point if
and only if \(g_i\) does. The tail span theorem identifies the admissible
\(c_i\) with the required tail product space.

For completeness, its dimension is

\[
 \dim W_n=3\dim I(Z)_{3n}-\dim I(Z)_{3n+1}
 =3n(3n-2).
\]

The coordinate map \(I(Z)_{3n}^3\to I(Z)_{3n+1}\) is onto. Start with
any homogeneous coordinate decomposition of a polynomial in the target.
At each base point its three coefficients form a coordinate syzygy.
Interpolate the three scalar Koszul correction values in degree \(3n-1\)
using the already constructed global separators. Subtract those
corrections to make each coefficient vanish at every base point without
changing its coordinate combination. Surjectivity and the established
evaluation dimensions give the displayed count.

In addition to the \(E_{t,a}\), define the **local pair** vectors

\[
 B_{t,s,a,b}=X_aK_t(a,b)e_b(I-K_s),\qquad t\ne s.
\]

Retain the primitive structural conditions used above, and impose the
following additional, explicit geometry conditions:

1. All transition coefficients used as scalars are nonzero.
2. Every intersection of a line from one block with a line from another
   block has all three coordinates nonzero.
3. No third denominator line passes through such an intersection.

These conditions are stronger than those needed for the dimension theorem.
They are finite polynomial nonvanishing conditions after choosing
cross-product representatives. Distinct positive conic parameters
\(L(w)=X_0+wX_1+w^2X_2\) satisfy them: their pair intersection is
\((uv,-u-v,1)\), and a third line evaluates to \((w-u)(w-v)\).

**Lemma.** Under these conditions, the \(3n\) single-block vectors \(E\)
and the \(9n(n-1)\) ordered local-pair vectors \(B\) form a basis of
\(W_n\).

**Proof.** First they belong to \(W_n\). Their row sums are zero.
Multiplication of component \(i\) by \(D/X_i\) gives a polynomial. For
\(E_{t,a}\), its component \(a\) is

\[
 \frac{D}{L_{ta}}\sum_{c\ne a}A_t(a,c)X_c,
\]

and its other components are \(-A_t(a,i)X_aD/L_{ta}\). For
\(B_{t,s,a,b}\), its component \(b\) is

\[
 A_t(a,b)X_a\frac{D}{L_{ta}L_{sb}}
       \sum_{c\ne b}A_s(b,c)X_c,
\]

and its other components are
\(-A_t(a,b)A_s(b,i)X_aX_bD/(L_{ta}L_{sb})\).
These expressions vanish at every within-block pair intersection. At a
coordinate base point \(L_{ta}=X_a=0\) or \(L_{sb}=X_b=0\), the displayed
sum in the exceptional component also vanishes. The remaining blocks
contribute unchanged denominator factors. Thus all coefficient polynomials
belong to \(I(Z)_{3n}\).

Consider any constant linear relation among these vectors. At the
cross-block point \(P=\{L_{ta}=L_{sb}=0\}\), multiply that relation by
\(L_{ta}L_{sb}\) and evaluate. Only two local-pair columns survive, namely
\(B_{t,s,a,b}\) and \(B_{s,t,b,a}\). Their values are

\[
 -A_t(a,b)X_a(P)X_b(P)v_{sb}(P),\qquad
 -A_s(b,a)X_a(P)X_b(P)v_{ta}(P).
\]

They are independent. Both \(v\)-vectors have row sum zero, and multiplying
the two independent line-coefficient vectors by the invertible diagonal
matrix \(\operatorname{diag}(X(P))\) preserves their independence.
Therefore the two corresponding coefficients in the linear relation are
zero. Applying this argument at each cross-block line pair kills every
\(B\) coefficient. A single-line residue then kills each remaining
\(E_{t,a}\) coefficient: its residue is the nonzero polynomial vector
\(-X_a v_{ta}\) on that line. All columns are independent, and their count
equals \(\dim W_n\). ∎

This lemma does **not** replace the specified source family by a theorem
about that family. Its value is to provide explicit coordinates for the
remaining source-independence question.

## The exact remaining determinant

For each unordered cross-block line pair
\(\{(u,c),(v,d)\}\), evaluate

\[
 \rho_{uc,vd}(F)
   =\left.(L_{uc}L_{vd}F)\right|_{P_{uc,vd}}.
\]

This lies in the two-dimensional zero-sum row space. Express it in the
ordered basis \((v_{uc}(P),v_{vd}(P))\). An implementation can choose any
nonzero two-by-two coordinate minor of those two vectors; independence
ensures at least one exists. Equivalently, use the scaled pair-residue
vectors appearing in the lemma to obtain the actual \(B\) coefficients.

Collect these two coordinates for every unordered cross-block line pair.
There are \(9\binom n2\) such pairs. On the \(9n(n-1)\) first-level source
columns \(F_{t,s,a,b}\), this produces a square matrix

\[
 R_n(A)\in\mathbb R^{9n(n-1)\times9n(n-1)}.
\]

All single-block vectors \(E\) have zero double-pole residues. The canonical
basis lemma therefore shows

\[
 \text{new source columns are independent in the quotient}
 \quad\Longleftrightarrow\quad \det R_n(A)\ne0.
\]

Together with the lifted-family induction this is an exact sufficient
route to independence of equation (24) for all \(T\). For \(T=5\), the
matrix has size 54; for \(T=6\), size 108. Its entries can be evaluated
using only three-by-three transfer-matrix products and cross-product
points. No enumeration of the \(3^T\) paths or expansion of homogeneous
polynomials is necessary.

The sufficiency direction actually requires less than the full quotient
identification. Suppose only that the shorter source family is independent
and \(R_n\) is invertible. Apply the conditional-sum map to a relation
among length-\(T\) source columns; it kills all lifted columns. Perform
the exact zeroth-level column reduction. Double-pole residues and
invertibility of \(R_n\) kill the remaining first-level coefficients.
Single-line residues then kill the \(E\) coefficients. What remains is a
relation among the three disjoint shorter-family lifts, whose independence
kills every coefficient. This argument does not assume shorter-family
completeness or that \(W_n\) exhausts the quotient.

To compute an entry, multiply the relevant rational expression for
\(F_{t,s,a,b}\) by the two pole factors before substituting the point.
For a pole belonging to a matrix \(K_u\), replace that factor in the
matrix word by its residue matrix, which has only the appropriate row
nonzero, equal to \(v_{uc}(P)\). All other matrix factors evaluate
ordinarily at \(P\). If the pole belongs to the scalar prefactor
\(K_t(a,b)\), its residue is \(A_t(a,b)X_b(P)\). A column missing one of
the two pole factors contributes zero. These instructions avoid evaluating
an undefined \(0/0\) expression.

For the economic family, the entries are rational functions of exponential
index coefficients on the stated geometry region. Clearing the explicitly
nonzero denominators gives an analytic exceptional factor. A nonzero
economic witness for each \(n\), together with the inherited shorter
factor, would yield the desired nonempty open dense region by the same
analytic argument as the existing finite theorem.

## What remains open

The new mathematical gap is an all-\(n\) nonvanishing theorem for
\(R_n\) on the economic parameter family. The single-block reduction is
exact, but naively stripping the suffix from a first-level source column
introduces a second shared position. Such a column is outside the new
part of the restricted equation (24) family. Multiplying columns by
functions of \(X\) is not a valid independence-preserving column operation.

One can reduce the resulting rational vectors to the canonical \(E,B\)
basis by partial fractions in three variables, but this alone does not
prove the resulting square change-of-basis matrix invertible. Primitive
geometry, the dimension formula, and a count of the source columns are
therefore insufficient substitutes for this missing nonvanishing proof.

One exact transformation may help organize an induction. Suppose all
coefficient matrices are invertible and let \(N=\max B\). Right
multiplication of every rational row vector by \(K_N^{-1}\) is an
injective real-linear operation, despite its dependence on \(X\). For
\(t,s<N\), the new block is last in the increasing suffix, so

\[
 F^{B}_{t,s,a,b}K_N^{-1}
 =F^{B\setminus\{N\}}_{t,s,a,b}
  +X_aK_t(a,b)e_b(K_N^{-1}-I),
\]

with the analogous identity for zeroth-level columns. The formula

\[
 K_N^{-1}=\operatorname{diag}(X)^{-1}A_N^{-1}
           \operatorname{diag}(L_N)
\]

shows that these transformed old-index columns have no denominator from
the new block. Columns with \(t=N\) or \(s=N\) can still have such poles.
This suggests a filtration by new-line residues. It does not finish an
induction: on a new line \(L_{Na}=0\), the restriction of \(K_N^{-1}\) to
zero-sum row vectors generically has rank one. New-line residues therefore
retain only one of the two cross-pair coordinates; a second argument must
control the information transferred to old-line residues or regular
parts. This approach has not yet produced an all-\(n\) determinant proof.

There is also an exact block structure directly in \(R_n\). For a
cross-point involving two old blocks, and a source column with both
indices old, the double residue is its old double residue multiplied on
the right by \(K_N(P)\). The correction
\(X_aK_t(a,b)e_b(I-K_N)\) has at most one old pole and contributes zero.
Thus the old-row, old-column block is \(R_{n-1}\) followed by independent
invertible two-dimensional coordinate changes at the old cross-points,
whenever those \(K_N(P)\) are invertible. This gives a Schur-complement
reduction with \(18(n-1)\) new rows and columns. It does not prove that the
Schur complement is nonsingular.

The remaining determinant can be isolated more precisely. Put
\(m=n-1\). At each old-new cross-point, expand the residue vector
in the basis \((v_{\mathrm{old}},v_N)\), and call its two scalar
coordinates \(\alpha,\beta\), respectively. Order the rows as
old-old residues, old-new \(\alpha\), old-new \(\beta\), and
the columns as old-old source pairs, pairs with \(t=N\), and pairs
with \(s=N\). The exact block matrix is

\[
 R_n\sim
 \begin{pmatrix}
 O&D&E\\
 0&P&Q\\
 B&R&S
 \end{pmatrix}. \tag{S1}
\]

Here \(O\) is the transported old residue matrix just described,
and each of the last two row or column groups has size \(9m\).
The zero block is exact: in every old-old source column, \(K_N\)
is last in the word, and its new-line residue is parallel to \(v_N\).
The polar theorem below proves that \(P\) is generically invertible
on the common-\(G\), independent-time family. Assuming also that
\(O\) is invertible, ordinary constant-matrix elimination leaves
the single \(9m\)-square target

\[
 H=S-BO^{-1}E-(R-BO^{-1}D)P^{-1}Q. \tag{S2}
\]

In the displayed row and column orders,
\(\det R_n=\det O\det P\det H\), with the coordinate-change
and permutation factors restored when comparing to the original
matrix. Proving generic nonvanishing of \(H\) for every \(m\)
is the remaining regular-half problem; the polar theorem alone does
not prove it.

The independent finite calculation `exploration/source24_schur.py`,
recorded in `exploration/source24-schur-results.json`, verifies (S1),
(S2), the transported old block, and the determinant factors with
permutation signs at six asymmetric positive fixtures. They use
\(G=\left(\begin{smallmatrix}1&1&1\\1&30&10\\1&3&2\end{smallmatrix}\right)\),
\(m=2,3,4\), economic old time factors, and new factors
\((1,\varepsilon,\varepsilon^3)\) at
\(\varepsilon=1/7,2/11\). In these exact modular checks the
regular matrices have full ranks \(18,27,36\), respectively.
These are finite witnesses, not an all-length proof for (S2).

The two halves of the inverse-matrix filtration can be described exactly.
Write \(n=m+1\), let \(D_{\mathrm{old}}\) be the product of the old lines,
and retain invertibility of \(A_N\). The vectors in \(W_nK_N^{-1}\) with
no pole on any new line are precisely

\[
 \frac{f}{D_{\mathrm{old}}},\qquad
 f_i\in I(Z_{\mathrm{old}})_{3m+1},\quad
 \sum_i f_i=0,\quad f_a(R_{Na})=0\quad(a=0,1,2).
\]

To verify this, multiply back by \(K_N\). The resulting coefficient
polynomials in the definition of \(W_n\) are

\[
 g_i=\sum_j f_j A_N(j,i)\frac{D_N}{L_{Nj}},
 \qquad D_N=\prod_j L_{Nj}.
\]

At an old base point, the diagonal factors \(D_N/L_{Nj}\) and the matrix
\(A_N\) are invertible, so all \(g_i\) vanish exactly when all \(f_i\)
vanish. At a new within-block pair point, every \(D_N/L_{Nj}\) is zero.
At \(R_{Na}\), only the term \(j=a\) can survive, giving exactly
\(f_a(R_{Na})=0\). Row-sum zero is preserved by both matrices.

The canonical local-pair columns \(B_{N,t,a,b}K_N^{-1}\) give
\(9m\) independent new-line pole coordinates. At their own cross-point,
the old-line residue direction is independent of \(v_{Na}\), the row
kernel of \(K_N^{-1}\) there, so the transformed residue is nonzero.
All other such pair coordinates are zero. The transformed old canonical
basis, the three \(E_{N,a}K_N^{-1}\), and the \(9m\) columns
\(B_{t,N,a,b}K_N^{-1}\) have no new-line pole. Consequently the pole
image has dimension \(9m\), and its kernel has dimension
\(\dim W_m+9m+3\). This explains the two groups of new coordinates
without identifying them as independent coordinates for the specified
long-suffix source columns. That last inference remains open.

A simple absorbing-state limit also does not settle the determinant.
For \(G_h=((1,1,1),(1,2,4),(1,4,h))\), put
\(\varepsilon=h^{-1}\) and change effect coordinates to
\(X_2=\varepsilon Z\). In these coordinates the limiting coefficient
matrix is \(((1,1,0),(1,2,0),(1,4,1))\). After dividing each source
column by its nonzero scalar \(A_t(a,b)\), the limiting columns with
\(a,b\in\{0,1\}\) stay in the binary zero-sum direction: a chain
started in 0 or 1 cannot reach 2 at order zero. Their rational functions
depend only on \(X_1/X_0\), with a common product of \(2n\) binary
linear denominators and numerator degree \(2n+1\). Their span therefore
has dimension at most \(2n+2\), while there are \(4n(n-1)\) such
columns. The zeroth-order normalized family is necessarily deficient for
\(n\ge2\). This does not rule out a useful higher-order argument: at
first order a chain can enter state 2 and then propagate through additional
denominators involving \(Z\). No higher-order rank bound or nonvanishing
claim has been established for this degeneration.

## A proved bridge to scalar covariates

One need not insist on slopes \((0,1,2)\) when searching for a generic
economic witness. The following elementary specialization lemma removes
that unnecessary restriction.

Let \(P(G,u_1,v_1,\ldots,u_n,v_n)\) be a nonzero polynomial obtained by
clearing the residue determinant's denominators on matrices
\(A_t=G\operatorname{diag}(1,u_t,v_t)\), with the normalized entries of
\(G\) treated as parameters. Choose an integer \(B\) strictly larger
than the degree of \(P\) in each individual \(u_t\). Then

\[
 P(G,u_1,u_1^B,\ldots,u_n,u_n^B)
\]

is a nonzero polynomial. Indeed, each monomial's pair of exponents
\((a_t,b_t)\) maps to \(a_t+Bb_t\); the bound \(0\le a_t<B\) makes
this map injective in every time coordinate. Distinct monomials cannot
cancel under substitution. A nonzero real polynomial cannot vanish on
the entire positive orthant, so positive normalized \(G\) and positive
\(u_t\) can be selected off its zero set. Taking \(x_t=\log u_t\) and
slopes \((0,1,B)\) realizes these tables with a scalar covariate.

The same argument can be applied to the product of this determinant
numerator and any finite list of required nonzero geometry polynomials,
provided that product is nonzero in the common-\(G\), independent-time-factor
family. This proves economic attainability once nonvanishing has been
shown on that intermediate family. It does not turn a result for freely
varying transition tables into a result for a common \(G\); that remains
a substantive restriction.

Finite-field deficiency alone does not establish a real rank upper bound.
For the original conic \(T=5\) witness, however, a subsequent exact
rational calculation now establishes

\[
 \operatorname{rank}_{\mathbb Q}R_3=51,\qquad
 \dim_{\mathbb Q}\ker R_3=3.
\]

The calculation verifies three primitive integer nullvectors against the
original rational matrix; a nonzero modular minor supplies the matching
rank lower bound. Their supports have sizes 16, 16, and 20, and every
nonzero coefficient has both shared and divergent outcomes in
\(\{0,2\}\). Thus the deficiency is exact, rather than an inference from
modular rank. By the quotient-coordinate argument above, the 63 new
source images have rank 60 at this specialization. This is an external
exact-arithmetic result, **not a Lean certificate**; it does not yet
provide expanded nullvectors among all 162 original source columns.
See `exploration/conic_residue_nullspace.py` and
`exploration/conic-nullspace-results.json`. The perturbed economic
witnesses and their separate finite certificate status are recorded in
the exploration results.

## Coalescing time factors: exact column identities

This section records algebraic identities, not an all-length independence
proof. Keep one outcome pair \((a,b)\) fixed, use row vectors, and write

\[
 K_i(\varepsilon)=K+\varepsilon D_i+\varepsilon^2E_i+O(\varepsilon^3),
 \qquad p=X_aK(a,b),\qquad \ell(H)=X_aH(a,b).
\]

For common \(G\), independent linear time tilts
\(A_i=G\operatorname{diag}(1,1+\varepsilon\delta_i,
1+\varepsilon\zeta_i)\) give
\(D_i=\delta_iK_u+\zeta_iK_v\). The normalization of each transition
row generally makes \(E_i\ne0\); none of the identities below discards
these terms. Set \([H,J]=HJ-JH\).

For adjacent IDs \(u<v\) in the ordered set \(B\setminus\{t\}\), let
\(A\) be the ordered product before \(u\), and \(C\) the ordered
product after \(v\). The exact source-column difference is

\[
 \Delta_t(u,v):=F_{t,u,a,b}-F_{t,v,a,b}
 =X_aK_t(a,b)e_b(K_vAK_u-K_uAK_v)C.
\]

Replacing, for each fixed \(t,a,b\), its list of columns by one base
column and adjacent differences is an invertible constant column
operation. If \(u\) has position \(j\), counted from one in
\(B\setminus\{t\}\), and \(c\) IDs follow \(v\), the first
coefficient of this difference is

\[
 [\varepsilon]\Delta_t(u,v)
 =p\,e_b[D_v-D_u,K^j]K^c.
\]

The first derivatives of the common prefix, suffix, and scalar prefactor
cancel. These repeated first coefficients permit further constant column
operations with genuinely second-order leading terms.

For three consecutive global IDs \(r<s<t\), put
\(U=D_s-D_r\), \(V=D_t-D_r\), let \(j-1\) be the number of IDs
before \(r\), and let \(c\) be the number after \(t\). The triangle
combination

\[
 H=\Delta_t(r,s)+\Delta_r(s,t)-\Delta_s(r,t)
\]

has zero coefficients of orders zero and one, and

\[
 [\varepsilon^2]H
 =e_b\left\{
   \ell(V)[U,K^j]-\ell(U)[V,K^j]
   +p\bigl(VK^{j-1}U-UK^{j-1}V\bigr)
 \right\}K^c. \tag{C1}
\]

Here is a direct derivation that also checks the cancellation of every
\(E_i\). Let \(A\) and \(C\) be the common actual prefix and suffix,
\(U_*=K_s-K_r\), \(V_*=K_t-K_r\), and \(p_r=X_aK_r(a,b)\).
Expansion of the three column differences gives the exact identity

\[
 H=e_b\{\ell(V_*)(U_*AK_r-K_rAU_*)
       -\ell(U_*)(V_*AK_r-K_rAV_*)
       +p_r(V_*AU_*-U_*AV_*)\}C.
\]

Every term has two matrix differences. Taking their first coefficients
and the zeroth coefficients of the remaining factors proves (C1).
For two time directions, (C1) is their alternating bilinear form
multiplied by the signed area of the three time-tilt vectors.

There are also second-order identities from moving the shared slot.
Fix a globally adjacent edge \(u<v\), with \(L\) IDs before \(u\)
and \(R\) after \(v\). Set \(V=D_v-D_u\).
If adjacent shared IDs \(t,t'\) occupy zero-based prefix positions
\(k,k+1\), where \(0\le k\le L-2\), put \(U=D_{t'}-D_t\).
The coefficients of orders zero and one in
\(\Delta_t(u,v)-\Delta_{t'}(u,v)\) vanish, and the second is

\[
 e_b\left\{-\ell(U)[V,K^L]
   +p\left(VK^kUK^{L-k-1}
          -K^{k+1}UK^{L-k-2}V\right)\right\}K^R. \tag{C2}
\]

For adjacent shared IDs in suffix positions \(k,k+1\), with
\(0\le k\le R-2\), the corresponding second coefficient is

\[
 e_b[V,K^{L+1}]
   \left\{pK^kUK^{R-k-2}-\ell(U)K^{R-1}\right\}. \tag{C3}
\]

To derive (C2), the difference of the first prefix derivatives is
\(K^kUK^{L-k-2}\), whereas the difference of the scalar derivatives
is \(-\ell(U)\). Substitution in the adjacent-edge identity gives
the displayed expression. The same argument on the suffix proves (C3).
All common second derivatives cancel. With three consecutive shared
prefix slots having equal increments \(U\), a second finite difference
also cancels the scalar term in (C2), giving

\[
 p e_b\left\{VK^k[U,K]K^{L-k-2}
       -K^{k+1}[U,K]K^{L-k-3}V\right\}K^R,
 \qquad 0\le k\le L-3. \tag{C4}
\]

These are constant combinations of the original source columns. No
effect-dependent coefficients have been used to change the column span.

The second-order alternating form does not vanish identically for
softmax transitions. At the boundary matrix

\[
 G=\begin{pmatrix}1&1&1\\1&1&0\\1&0&1\end{pmatrix},
 \qquad X=(1,1,1),\quad u=v=1,
\]

take \(U=K_u\), \(V=K_v\), \(a=b=0\), and \(j=1\). Then

\[
 e_0\{V_{00}[U,K]-U_{00}[V,K]+K_{00}(VU-UV)\}
       =(0,-1/54,1/54),\qquad \det K=-1/12.
\]

Thus no suffix power kills this particular row. Although this boundary
matrix has zero entries and fails some residue-geometry assumptions, the
displayed rational coefficient is defined and nonzero. Continuity gives
strictly positive nearby common matrices with the same nonvanishing
property. This establishes a nonzero second-order column for arbitrary
suffix length, not independence from other columns.

The same boundary matrix supports two independent spectral variables.
On the zero-sum row space, let \(\tau=\operatorname{tr}K-1\) and
\(d=\det K\). For \(X=(1,t,s)\), put
\(A=1+t+s\), \(B=1+t\), \(C=1+s\). Direct computation gives

\[
 \tau=1+A^{-1}-B^{-1}-C^{-1},\qquad
 d=-\frac{ts}{ABC}.
\]

At \((t,s)=(1,2)\), their derivative rows are
\((3/16,7/144)\) and \((-1/48,1/144)\), so the Jacobian is
\(1/432\). Their image therefore contains an open set, proving that
\(\tau\) and \(d\) are algebraically independent. The nonzero
Jacobian also persists under a small positive perturbation of \(G\).

After spectral decomposition, (C2)--(C4) contain terms with two varying
nonstationary eigenvalue exponents. This is a possible source of the
quadratic number of independent directions needed as \(n\) grows.
However, the accompanying coefficients also depend on the effects, and
the remaining terms have not been eliminated. Algebraic independence of
the spectral invariants does not by itself establish independence of these
columns. A nonsingular full leading matrix, or an equivalent Laurent
determinant argument, remains unproved. Independence of stacked Taylor
coefficients is not a substitute: pointwise column relations may have
\(\varepsilon\)-dependent coefficients.

As a check on the identities, `exploration/coalescent_checks.py` verifies
the adjacent-edge coefficient and (C1)--(C3) directly from exact rational
series of the original \(F\) columns, retaining normalization terms.
The recorded cases cover \(n=3,\ldots,6\), two positive common matrices,
three effect vectors, and every outcome pair: 2,160 adjacent-edge checks
and 540 checks for each of the triangle, prefix, and suffix formulas.
It also checks the boundary curvature and spectral Jacobian. These are
external spot checks of the algebraic identities, not rank certificates
or Lean proofs; (C4) follows by subtraction of (C2).

## A last-block degeneration and its binary obstruction

The inverse-matrix filtration above permits a more explicit boundary
calculation, but its simplest candidate polar block is singular. Normalize
the first column of the common matrix \(G\) to one, put
\(\alpha_a=G_{a1}\), \(\beta_a=G_{a2}\), and choose the last block
as \(A_N=G\operatorname{diag}(1,\varepsilon,\varepsilon^B)\), with
integer \(B>1\). On its line \(L_{Na}=0\), use the affine parameter

\[
 X_1=1,\qquad X_2=z,\qquad
 X_0=-\varepsilon\alpha_a-\varepsilon^B\beta_a z.
\]

For invertible \(G\) and nonzero \(\alpha_a z\), the exact inverse
formula gives

\[
 \varepsilon^{B-1}K_N^{-1}
 \longrightarrow z^{-1}E_{22}G^{-1}
       \operatorname{diag}(\alpha_c-\alpha_a)_{c=0}^2. \tag{L1}
\]

Only row two can survive. Its row sum is zero, because row two of
\(G^{-1}\) annihilates both the first and second columns of \(G\).
Its component \(a\) is also zero. Under generic conditions this row is
nonzero, as expected for the one-dimensional new-line residue direction.

Divide each shared-\(N\) source column by the nonzero constant
\(A_N(a,b)\), multiply it on the right by \(K_N^{-1}\), and take
its residue along \(L_{Na}=0\). The resulting row is exactly

\[
 X_aX_b\,e_b(I-P_s^{\mathrm{old}})K_N^{-1}.
\]

Write \(\kappa_i=1\) for \(i=0\) and zero otherwise. After multiplying
this column by the constant power
\(\varepsilon^{B-1-\kappa_a-\kappa_b}\), its limit is the common row in
(L1) times
\(X_a^0X_b^0[e_b(I-P_s^{\mathrm{old},0})]_2\), where
\((X_0^0,X_1^0,X_2^0)=(-\alpha_a,1,z)\).
The limiting old transitions have zero first column; after one step a
path stays in the binary state set \(\{1,2\}\).

The \(b=0\) column for a given \(s\) has a row-zero pole only at
\(L_{s0}|_{X_0=0}=0\). Later matrices use only rows one and two.
For distinct restricted lines and invertible binary transitions, these
\(m\) poles form a diagonal nonzero block. The other \(2m\) columns
are, up to a shared nonzero rational factor and signs,

\[
 q(P_s)(z),\qquad z\,r(P_s)(z),
\]

where \(q(P)=P_{12}\), \(r(P)=P_{21}\), and \(P_s\) orders
the \(m\) old binary transitions with \(s\) first. Their generic
independence would have made this particular polar half sufficient.
It is false already for \(m=2\).

The failure has a short exact calculation. Common \(G\) makes the two
binary row odds \(c_i z\) and \(\rho c_i z\), with common
\(\rho\ne1\). If \(d_i\) is the binary determinant, set

\[
 H_i=d_i^{-1}
  =\frac{(1+c_i z)(1+\rho c_i z)}{(\rho-1)c_i z},\qquad
 Q_i=\frac{q_i}{d_i}=\frac{1+\rho c_i z}{\rho-1},\qquad
 R_i=\frac{zr_i}{d_i}=\frac{1+c_i z}{(\rho-1)c_i}.
\]

Dividing every column by the common rational function
\(\prod_i d_i\) is an injective linear transformation. In any word
order, its two columns become the sums of \(Q_i\), respectively
\(R_i\), times the preceding \(H\) products. These are Laurent
polynomials supported on powers \(1-m,\ldots,m\).
Moving slot \(s\) to the front changes the first sum by

\[
 h_s=\sum_{i<s}\frac{c_i-c_s}{c_ic_s(\rho-1)^2}
       \bigl(z^{-1}+\rho(c_i+c_s)+\rho c_ic_sz\bigr)
       \prod_{j<i}H_j,
\]

and changes the second by \(-z h_s\). The formula follows from
\(H_i-1=Q_i+R_i/z\). The pairs \(h_s,z h_s\), for
\(s=2,\ldots,m\), are independent when consecutive \(c_i\)'s
are distinct: their successive outer powers are unique. They leave a
two-dimensional Laurent remainder, which need not be filled by the two
ascending baseline columns.

Indeed, for \(m=2\), let
\(J=1+\rho(c_1+c_2)z+\rho c_1c_2z^2\). Direct factorization gives

\[
 h_2=\frac{(c_1-c_2)J}{c_1c_2(\rho-1)^2z},\quad
 Q_{\mathrm{base}}=\frac{(1+\rho c_1z)J}{(\rho-1)^2c_1z},\quad
 R_{\mathrm{base}}=\frac{(1+c_1z)J}{(\rho-1)^2c_1c_2z}.
\]

Both baseline columns lie in the span of \(h_2,z h_2\). The four
binary columns therefore have rank exactly two for
\(c_1\ne c_2\) and \(\rho\ne1\). Consequently the leading
shared-\(N\) polar half above is deficient when \(m=2\). This
rules out that particular simple leading block, not the complete
Schur complement: the other new columns and higher powers of
\(\varepsilon\) have not been eliminated or shown dependent.

In fact the binary rank has an exact parity law for every length:

\[
 \operatorname{rank}\{q(P_s),zr(P_s):1\le s\le m\}
 =\begin{cases}2m,&m\text{ odd},\\2m-2,&m\text{ even}.
 \end{cases} \tag{L2}
\]

Assume \(\rho\ne0,1\), all \(c_i\ne0\), and consecutive
\(c_i\)'s distinct. The rank means linear independence over constant
real coefficients, for rational functions of \(z\); it is not rank
over \(\mathbb R(z)\). Lean now proves the scalar-span parity
recurrence and both baseline remainders below; the Laurent endpoint
independence and full rank formula are not yet formalized.

Let \(Q^{(k)},R^{(k)}\) be the ascending prefix sums for the first
\(k\) blocks, with empty sums zero, and write

\[
 A^{(k)}=\prod_{i\le k}H_i=1+Q^{(k)}+R^{(k)}/z.
\]

For an appended odds parameter \(c\), write
\(h_{k+1}(c)=(R_cQ^{(k)}-Q_cR^{(k)})/z\), and set \(h_1=0\).
Define the scalar Laurent polynomial

\[
 \Phi_k(c)=-\frac{1+\rho cz}{z}R^{(k)},\qquad \Phi_0=0.
\]

With \(e=c_k\), direct substitution gives the exact recurrence

\[
 \Phi_k(c)=1-\Phi_{k-1}(e)
       +\frac{\rho-1}{e-c}
          \bigl(eh_k-ch_{k+1}(c)\bigr). \tag{L3}
\]

To check it, substitute
\(Q^{(k)}=U+A^{(k-1)}Q_e\),
\(R^{(k)}=V+A^{(k-1)}R_e\), where
\(A^{(k-1)}=1+U+V/z\). The only two-block identity needed is

\[
 (1+cz)Q_e-e(1+\rho cz)R_e=(e-c)z.
\]

After multiplying (L3) by \((e-c)z\), the remaining expression is
\((e-c)z(A^{(k-1)}-1-U-V/z)=0\).
Induction in (L3) proves that \(\Phi_k(c)\), modulo the scalar
span of \(h_2,\ldots,h_{k+1}(c)\), is one for odd \(k\) and
zero for even \(k\).

It remains to connect this scalar recurrence to the two baseline
columns. For \(m\ge2\), put \(c=c_{m-1}\), \(d=c_m\),
\(U=Q^{(m-2)}\), \(V=R^{(m-2)}\), and

\[
 v_Q=\frac{d(1+\rho cz)}{c-d},\qquad
 v_R=\frac{1+cz}{c-d}.
\]

The exact outer-column elimination is

\[
 Q^{(m)}-v_Qh_m=Q_d S,\qquad
 R^{(m)}-v_Rh_m=R_d S, \tag{L4}
\]

where

\[
 S=\frac{d(1+\rho cz)V-(1+cz)U}{(c-d)z}
   =\Phi_{m-2}(c)-\frac{c(\rho-1)}{c-d}h_{m-1}.
\]

Although \(v_Q,v_R\) are linear polynomials in \(z\), (L4) uses
only constant multiples of the already available columns \(h_m,z h_m\).
For an explicit verification, put \(A=1+U+V/z\). Then
\(Q^{(m)}=U+A Q_{cd}\), \(R^{(m)}=V+A R_{cd}\), and
\(h_m=(R_dU-Q_dV)/z+A h_{cd}\). The two-block factorization gives
\(Q_{cd}=v_Qh_{cd}\), \(R_{cd}=v_Rh_{cd}\), while
\(R_dv_Q-Q_dv_R=z\). Subtraction proves (L4).

By (L3), \(S\) is congruent to the parity of \(m\) modulo the
scalar span of the earlier \(h\)'s. Multiplication by the linear
polynomials \(Q_d,R_d\) puts the discarded terms in the paired span
of \(h_s,z h_s\). Thus the two baseline remainders are exactly
\(Q_m,R_m\) for odd \(m\), and both zero for even \(m\).
The independent paired columns have no nonzero combination supported
only on \(1,z\), by the same outer-power elimination used above.
Finally, the coefficient determinant of \(Q_m,R_m\) in that central
basis is \(-1/(\rho-1)\ne0\). This proves (L2), including \(m=1\).

Under the separate generic assumptions making the row-zero pole block
nonzero and disjoint from the binary poles, the leading shared-\(N\)
polar half consequently has rank \(9m\) for odd \(m\), and
\(9m-6\) for even \(m\): there are three independent new-line
blocks, each consisting of \(m\) row-zero poles plus the binary rank
in (L2). These are ranks of this particular leading boundary block.
They are not ranks of the full Schur complement at general parameters.

The finite calculations in `exploration/binary_laurent.py` and
`exploration/binary-laurent-results.json` agree with (L2): ranks
\(2,2,6,6,10,10\) for \(m=1,\ldots,6\), using
\(\rho=2,-1\) and \(c_i=i\) or \(2^{i-1}\). The proof above
establishes the general parity law independently of those checks.

The exact binary kernel can also guide a correction away from the
boundary. At \(m=2\), write \(A_{12}=P_{12}(1,2)\) and
\(B_{12}=z(1-P_{12}(2,2))\), and similarly for the reverse word.
The two constant relations at \(X_0=0\) are

\[
 A_{12}-A_{21}-c_2B_{12}+c_1B_{21}=0,
\]
\[
 c_1A_{12}-c_2A_{21}
       -\rho c_1c_2B_{12}+\rho c_1c_2B_{21}=0.
\]

Differentiating these relations gives candidates for the two lost
directions on each new line. Choosing \(B\ge3\) controls the other
terms in this derivative: in (L1), the scaled inverse's row two is its
displayed limit plus \(O(\varepsilon^{B-1})\), and rows zero and one
are \(O(\varepsilon^{B-1})\). Also
\(X_0/\varepsilon=-\alpha_a+O(\varepsilon^{B-1})\). Thus the
inverse-matrix functional and the normalized coordinate prefactors have
zero first derivative. Only the old transition matrices vary at first
order, through \(X_0'=-\alpha_a\). A moving old cross-point adds
\(z'\partial_z\) of a zeroth-order nullrelation, which is zero because
that relation vanishes identically as a rational function.

More explicitly, at \(X_0=0\) write
\(k_i=(\eta,1,\rho)_i\), where
\(\eta=\beta_0\alpha_1/(\alpha_0\beta_1)\). Then

\[
 K_t^0(i)=\left(0,\frac1{1+k_ic_tz},
                       \frac{k_ic_tz}{1+k_ic_tz}\right),\qquad
 \left.\frac{\partial K_t(i)}{\partial X_0}\right|_0
 =\frac{e_0-K_t^0(i)}{\alpha_i u_t(1+k_ic_tz)}.
\]

Product differentiation therefore specifies the actual first kernel
derivatives. Their row-zero pole parts can be removed using the leading
row-zero columns. The even-length calculation below identifies a
nonzero coefficient for the two remaining directions. In particular,
the boundary obstruction does not imply singularity of the generic
shared-\(N\) polar half.

There is useful remaining parameter freedom. Keeping all \(c_t\) fixed
while varying \(u_t\), and choosing \(v_t\) accordingly, preserves
every leading transition matrix and the leading column kernel. Each
transition derivative has the scalar factor \(1/u_t\). Thus the first
kernel-derivative matrix after the fixed leading elimination is linear in
the independent parameters \(1/u_t\); its two-dimensional missing
determinant on each new line is quadratic in those parameters. A nonzero
coefficient suffices for this polar correction, but still leaves the
separate regular half of the full Schur complement.

## An explicit even-length polar first-order coefficient

This section proves an algebraic lemma over constant real column
coefficients and connects it to the full shared-\(N\) polar block.
The paper proof received an independent internal audit in
[SOURCE24_POLAR_AUDIT.md](../reviews/SOURCE24_POLAR_AUDIT.md).
It is not a proof of independence of the whole source family: the other
half of the Schur complement is still open. The polar argument has not
been formalized in Lean.

Let \(m\ge2\) be even, retain \(\rho\ne0,1\), and put
\(c=c_{m-1}\), \(d=c_m\), \(e=c_1\). Assume all
\(c_t\ne0\), adjacent \(c_t\)'s are distinct, and write

\[
 D=\prod_{t=1}^m d_t,\qquad
 I_m=\operatorname{span}_{\mathbb R}\{h_s,zh_s:2\le s\le m\},
 \qquad V_m=\operatorname{span}_{\mathbb R}\{z^{1-m},\ldots,z^m\}.
\]

The parity theorem says \(V_m=I_m\oplus\operatorname{span}\{1,z\}\).
Write \(\Pi:V_m\to\operatorname{span}\{1,z\}\) for this
constant-linear projection. For a move-first word \(P_s\), use scalar
columns \(A_s=q(P_s)\), \(B_s=zr(P_s)\); an overall minus
sign in the original first column is immaterial.

The row-zero columns must be included in the same scalar quotient.
If their row odds are \(\eta c_tz\), direct binary propagation gives

\[
 \frac{P_s(0,2)}D=Q_{\mathrm{word}\ s}+Z_s,\qquad
 Z_s=\frac{\eta-1}{\rho-1}\frac{1+\rho c_sz}{1+\eta c_sz}.
 \tag{P1}
\]

Here \(Q_{\mathrm{word}\ s}=A_s/D\). Since \(m\) is even,
each such Laurent column belongs to \(I_m\), so the full leading
scalar span is exactly
\(I_m+\operatorname{span}\{Z_1,\ldots,Z_m\}\).
Assume \(\eta\ne0,1,\rho\), and that the poles
\(-1/(\eta c_s)\) are distinct and disjoint from all binary poles
\(-1/c_t,-1/(\rho c_t)\). Each \(Z_s\) then has its own
nonzero pole and the sum is direct. This removal of the Laurent part
of a row-zero column uses constant combinations of the binary columns.

The two-dimensional binary column kernel can be parametrized by its
last-word coefficients \((p,q)\), those of \((A_m,B_m)\).
To see this, let \(S_A,S_B\) be the total coefficients of the two
column types in a relation. The outer \(h_m,zh_m\) terms in (L4)
give

\[
 p=-\frac{dS_A+S_B}{c-d},\qquad
 q=\frac{\rho cdS_A+cS_B}{c-d}.
 \tag{P2}
\]

Their determinant is \(cd(\rho-1)/(c-d)^2\ne0\). The earlier
paired \(h\) columns determine the other coefficients uniquely.
Thus choose a constant kernel basis with last coefficients
\((1,0)\), \((0,1)\). If \(C_A,C_B\) denote the sums over
the earlier words in any relation, its endpoints give

\[
 dC_A+C_B=-cp-q,\qquad
 C_A+\frac{C_B}{\rho d}=-p-\frac q{\rho c}.
 \tag{P3}
\]

Indeed the last block is \(m\) for every earlier word and \(m-1\)
for the last word; at zero the two columns have leading terms
\(c_{\mathrm{last}}z,z\), and at infinity they have limits
\(1,1/(\rho c_{\mathrm{last}})\).

Keep every \(c_t\) fixed and isolate the derivative coefficient
with only \(w_m=1/u_m\) nonzero. Normalize it to one. For now also
take the boundary \(1/\alpha_1=0\), \(1/\alpha_2=1\).
The attainable positive-parameter limit justifying this choice is
given below. The derivative of the last transition then has binary
row factors \(h_1=0\), \(h_2=r_d=1/(1+\rho dz)\).
All earlier words end with this transition. If their preceding binary
distribution is \(\pi\), the derivative of its final probability
of state two is \(w_1+(w_2-w_1)\pi_2\), where
\(w_i=-h_iB_m(i,2)\). Consequently

\[
 A_s'=\lambda A_s+k_A,\quad B_s'=\lambda B_s+k_B\quad(s<m),
\]
\[
 \lambda=-\frac{\rho(1+dz)}{(\rho-1)(1+\rho dz)},\qquad
 k_A=dk_B,\qquad k_B=\frac{\rho z}{(\rho-1)(1+\rho dz)}.
 \tag{P4}
\]

For the last word, let \(q_0=(K_1^0\cdots K_{m-1}^0)_{02}\).
The exceptional transition is first, so
\(A_m'=0\) and
\(B_m'=zr_d(1-q_0)-r_dB_m\).
Subtracting \(\lambda\) times the identically zero original kernel
relation, and applying (P3), gives its two derivative defects

\[
 N_p=\frac{\rho}{(\rho-1)(1+\rho dz)}
                \bigl((1+dz)A_m-cz\bigr),\qquad
 N_q=\frac{B_m-zr_d}{\rho-1}-zr_dq_0.
 \tag{P5}
\]

Using an effect-dependent multiplier on an identity that is already
zero here is only a way to compute its derivative; it is not an
effect-dependent change of source columns. The kernel basis and the
subsequent quotient operations all have constant coefficients.

Set \(U=Q^{(m-1)}\), \(V=R^{(m-1)}\). The product identities are

\[
 A_m/D=Q_d+H_dU,\quad B_m/D=R_d+H_dV,\quad
 q_0/D=H_d(U+Z_1),\quad D^{-1}=H_d(1+U+V/z).
\]

Substitution in (P5) gives the useful closed forms

\[
 \frac{N_p}D=\frac{\rho(1+dz)}{(\rho-1)^2dz}
       \bigl((1+(d-c)z)U-cV+(d-c)z\bigr),
 \tag{P6}
\]
\[
 \frac{N_q}D=\frac{\rho R_d}{\rho-1}(dV-U)-R_dZ_1.
 \tag{P7}
\]

All four shifted Laurent reductions needed for (P6)--(P7) follow
from the scalar recurrence, without treating a vector-space quotient
as a ring. Since the prefix length \(m-1\) is odd,
\(\Pi U=Q_c\), \(\Pi V=R_c\). Also
\(\Phi_{m-1}(d)=-V/z-\rho dV\) is one modulo the scalar span
of \(h_2,\ldots,h_m\). Applying this identity and its product by
\(z\), whose discarded terms are available \(zh_s\) columns,
gives the last two of

\[
 \begin{aligned}
 \Pi(U/z)&=-d-dQ_c,&\quad \Pi(zU)&=-z-Q_c/d,\\
 \Pi(V/z)&=-1-\rho dR_c,& \Pi(zV)&=-z/(\rho d)-R_c/(\rho d).
 \end{aligned} \tag{P8}
\]

The first two follow in the same way from the exact identity
\((\rho-1)dh_m=U/z+dU+d\Phi_{m-1}(d)\) and its product
by \(z\). Thus every removal in (P8) uses a constant combination
of the displayed paired columns.

Expanding (P6) and applying (P8) now yields

\[
 \Pi(N_p/D)=P(z)=\frac{\rho}{(\rho-1)^2}(1+cz).
 \tag{P9}
\]

The Laurent part of (P7) reduces to \(Q_c/((\rho-1)c)\).
To reduce the positive factor \(R_dZ_1\), remove its row-zero
pole by subtracting the constant \(R_d(z_0)\) times \(Z_1\),
with \(z_0=-1/(\eta e)\):

\[
 (R_d(z)-R_d(z_0))Z_1
   =\frac{\eta-1}{(\rho-1)^2\eta e}(1+\rho ez).
 \tag{P10}
\]

Retaining the minus sign of \(-R_dZ_1\) in (P7), the second
class modulo the entire leading scalar span is therefore

\[
 Q(z)=\frac1{(\rho-1)^2}
       \left(\frac1c-\frac{\eta-1}{\eta e}+\frac\rho\eta z\right).
 \tag{P11}
\]

The coefficient determinant of \(P,Q\) in the basis \(1,z\) is

\[
 \det(P,Q)=\frac{\rho}{\eta(\rho-1)^4}
       \left(\rho-\eta+\frac ce(\eta-1)\right).
 \tag{P12}
\]

It is nonzero for every even \(m\ge2\) at
\(\rho=2\), \(\eta=3\), \(c_t=5^{t-1}\): the bracket
is \(-1+2\cdot5^{m-2}>0\). Multipliers \(1,2,3\) times
different powers of five also give distinct binary and row-zero poles.

Here is how this coefficient is attained in the common-transition
parameter space. More generally take

\[
 G_M=\begin{pmatrix}1&1&1\\1&M&M/\eta\\1&b&\rho b/\eta\end{pmatrix},
 \qquad
 A_t\sim G_M\operatorname{diag}(w_t,1,\eta c_t),
 \tag{P13}
\]

where the table equivalence is multiplication by the nonzero scalar
\(1/u_t\), and \(w_t=1/u_t\). For positive \(w_t\) this is
exactly the original table with \(v_t/u_t=\eta c_t\).
Every leading transition is independent of \(M,w_t\), while its
row derivative has factor \(w_t/\alpha_i\). Set \(w_m=1\),
earlier \(w_t=0\), and let \(M\to+\infty\). The row-one
derivative vanishes and the row-two derivative has the common factor
\(1/b\). The row-zero transition derivative never enters a binary
kernel relation: before the last block the leading distribution is
binary, and in the last word its initial state is binary. Thus (P6)--(P12)
are precisely this limiting coefficient after division by \(1/b\).
Restoring it multiplies (P12) by \(1/b^2\).

For the new table choose \(A_N=G_M\operatorname{diag}(1,\varepsilon,
\varepsilon^B)\) with integer \(B\ge3\). On new line \(a\),
the derivative also has common factor \(-\alpha_a\). Before
taking the \(M\) limit, divide by this nonzero factor, normalize
the explicit coordinate factors, and identify the nonzero inverse row
functional from (L1) with a scalar. Explicitly its constant row vector
is
\(e_2G_M^{-1}\operatorname{diag}(\alpha_j-\alpha_a)\),
up to the common rational factor \(1/z\). If the \(\alpha_j\)
are distinct it is nonzero: the nonzero row \(e_2G_M^{-1}\) sums
to zero because the first column of \(G_M\) is all ones, and
therefore has at least two nonzero entries. Some component other than
\(a\) survives. The resulting scalar normalization is constant in
\(z\), apart from a common injective rational multiplication.
The scaled inverse functional and normalized coordinate factors have
zero first \(\varepsilon\) derivative for \(B\ge3\), as shown
above. This normalization is necessary when \(\alpha_1=M\) grows.

For the explicit choice \(\rho=2,\eta=3,b=3\),
\(\det G_M=M/3+1\ne0\), and all entries are positive for
finite positive \(M\). The nonzero limiting rational coefficient
therefore persists at sufficiently large finite \(M\), and then
at small positive earlier \(w_t\). This supplies positive finite
old time factors, with one common positive invertible \(G_M\).
The same coefficient, up to the described nonzero factors, works on
all three new lines simultaneously. For each finite choice, sufficiently
small positive \(\varepsilon\) realizes the nonzero leading minor.

For completeness, independence of the scalar rational functions detects
the required old-new pole residues. Before division by \(D\), the
leading functions \(q(P_s),zr(P_s),P_s(0,2)\) vanish at zero and
are bounded at infinity. Their allowed finite poles are precisely the
distinct old restricted lines. The two kernel derivatives in (P5)
have the same endpoint properties and only simple allowed poles.
For \(N_p\), \(A_m\) has no pole at the last row-two denominator;
for \(N_q\), use \(B_m-zr_d=d_m\,zr(P_{\mathrm{prefix}})\)
in (P5). These identities exclude an extra double pole at the last
transition. Equivalently, moving-pole differentiation of an identically
zero leading relation has double-pole coefficient equal to the pole
velocity times its zero residue. A function in this span with all finite
residues zero is pole-free and bounded at infinity, hence constant,
and its value at zero makes it zero. Thus the residue map is injective
on the leading pivots and these derivative columns. The inverse's common
\(1/z\) factor is nonzero at every allowed pole and only rescales
the corresponding residue rows. A moving old cross-point contributes
\(z'\partial_z\) of the leading nullrelation, which is identically
zero.

This proves the following conditional paper lemma. Under the displayed
pole assumptions, for even \(m\), if
\(\rho-\eta+(c/e)(\eta-1)\ne0\), the normalized last-block
perturbation has two independent first kernel derivatives on each new
line. Hence the \(3m\)-column block on that line has a nonzero
leading minor after constant kernel elimination. For odd \(m\), the
corresponding leading block already has rank \(3m\). The three
new-line blocks are separate, so together their shared-new polar half
has a nonzero \(9m\)-column minor at positive finite perturbations
of the common-\(G\) family (P13).

In particular, the explicit powers-of-five choice proves that the
shared-new polar determinant is not identically zero on the common-
\(G\), independent-time parameter space for every \(m\ge1\).
Additional generic line-incidence conditions used elsewhere can be
imposed by a small perturbation inside this nonzero-minor neighborhood
whenever their polynomial factors are not identically zero on that same
parameter space. The scalar-covariate substitution discussed earlier
then applies to the resulting nonzero polynomial in independent time
factors. These conclusions do not supply the unproved regular half of
the full Schur complement.

The separate finite check `exploration/binary_polar_derivative.py`, with
results in `exploration/binary-polar-derivative-results.json`, verifies
eight exact rational fixtures: \(m=2,4,6,8\), each with
\((\rho,\eta)=(2,3),(3,2)\). It solves the actual constant
Laurent column kernel with prescribed last-word coefficients, checks
the four reductions coefficientwise, compares (P6)--(P7) to actual
three-state product derivatives at three rational points, and checks
the row-zero subtraction and (P12). These finite diagnostics support
the all-length algebra above; they do not replace it or certify full
source independence.

## Additional finite degeneration diagnostics

The sparse and absorbing computations are recorded separately in the
exploration scripts and results. Normalized sparse evaluations did not
provide a full witness. In the absorbing chart, the subsequent
first-order experiment used the constant kernel \(N\) of the zeroth
evaluation matrix \(M_0\), and tested
\([M_{0,\mathrm{pivot}},M_1N]\), explicitly verifying
\(M_0N=0\). This is the relevant column elimination, rather than
stacking \(M_0\) and \(M_1\).

For the tested independent and economic time factors, \(n=2\) had
zeroth rank 16 and full first-order rank 24; \(n=3\) had zeroth rank
31 and first-order rank 51 out of 63. These finite evaluation results
are in `exploration/absorbing-firstjet-results.json`. The latter case
does not furnish the required first-order witness. The tests do not
establish a universal rank upper bound, rule out higher-order excursions,
or prove an all-length source determinant. The exact identities and the
binary parity proof above remain separate from these
finite diagnostics.
