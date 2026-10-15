# Equation (24): an induction and a quadratic-size residue test

Research note, 15 October 2026. The algebraic arguments below establish a
reduction of the three-choice independence problem to explicit finite
determinants. They are mathematical proofs and derivations, **not new Lean
theorems**. Nonvanishing of those determinants for every panel length on the
economic parameter family remains unproved.

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
