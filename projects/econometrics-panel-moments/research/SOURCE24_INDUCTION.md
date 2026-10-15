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

There is nevertheless a complete nonvanishing argument for this binary
subproblem when \(m\) is odd. Fix \(c>0\) and \(\rho>0\),
\(\rho\ne1\), and set \(c_i=c+\delta\xi_i\), with consecutive
\(\xi_i\)'s distinct. Use the constant column transformation to the
two ascending baseline columns and \(h_s,z h_s\), then divide each
difference column by the parameter \(\delta\). At \(\delta=0\),
put

\[
 H=\frac{(1+cz)(1+\rho cz)}{(\rho-1)cz},\qquad
 J=z^{-1}+2\rho c+\rho c^2z=c(\rho-1)(H+1).
\]

The limits of \(h_s/\delta\) are triangular nondegenerate combinations
of \(JH^j\), \(0\le j\le s-2\): the coefficient of the last
power is proportional to \(\xi_{s-1}-\xi_s\). The Laurent space
supported on \(1-m,\ldots,m\) has the basis
\(H^j,zH^j\), \(0\le j\le m-1\), as follows by successively
peeling its two outer powers. The limiting difference columns therefore
span exactly

\[
 (H+1)\{p(H)+zq(H):\deg p,\deg q\le m-2\}.
\]

In the remaining two-dimensional quotient, evaluation at \(H=-1\)
leaves the basis \(1,z\). The baseline columns limit to
\(Q S_m(H)\), \(R S_m(H)\), where
\(S_m(H)=1+H+\cdots+H^{m-1}\). For odd \(m\),
\(S_m(-1)=1\), and the coefficient determinant of the two linear
polynomials \(Q=(1+\rho cz)/(\rho-1)\) and
\(R=(1+cz)/((\rho-1)c)\) is \(-1/(\rho-1)\ne0\).
Thus the entire limiting coefficient matrix is nonsingular. This proves
generic binary independence for every odd \(m\), with a nonzero
leading determinant of order \(\delta^{2m-2}\) before the difference
columns were rescaled. It is a Laurent determinant argument, rather
than an inference from stacked jets.

For even \(m\), both baseline quotient classes vanish in this
coalescence. That fact alone does not prove a generic even-length
deficiency. Exact finite checks in `exploration/binary_laurent.py`
and `exploration/binary-laurent-results.json` give ranks
\(2,2,6,6,10,10\) for \(m=1,\ldots,6\), using
\(\rho=2,-1\) and \(c_i=i\) or \(2^{i-1}\). Their even-length
baseline remainders are zero; their odd-length remainders are precisely
\(Q_m,R_m\). These are evidence for a stronger parity identity,
not yet a proved general even-length statement. The \(m=2\)
deficiency above is already proved symbolically.

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
directions on each new line. A complete Schur derivative must also
differentiate the inverse-matrix row functional, the chosen line
coordinates, and the scalar normalizations, or prove their contributions
vanish in the quotient. No such complete derivative determinant has been
established here. The rank-two boundary obstruction must not be promoted
to singularity of the generic shared-\(N\) polar half.

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
odd-length binary nonvanishing proof above remain separate from these
finite diagnostics.
